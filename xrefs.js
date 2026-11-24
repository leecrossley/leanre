/* leanre cross-references browser.
 *
 * Reads the static LXRF v1 export written by `leanre/xrefs.py` (manifest.json +
 * gzip-9 `.lxrf` files) straight from a static host and renders:
 *   - window.LeanreXrefs.XrefClient            lazy binary reader with LRU caches
 *   - window.LeanreXrefs.renderExplorer        the #xrefs page
 *   - window.LeanreXrefs.renderCompare         stand-alone "compare A vs B" panel
 *   - window.LeanreXrefs.hydrateItemConnections live counts on #item/<name>
 *   - window.LeanreXrefs.runSelfTest           hook for #selftest=1
 *
 * Safety: every piece of data is written with textContent / setAttribute; no
 * innerHTML, no eval, no external requests (only same-origin `baseUrl` fetches).
 *
 * License: AGPL-3.0-or-later
 */
(function (root) {
  "use strict";

  const VERSION = "1.0.0";
  const SCHEMA = "leanre.xrefs/1";
  const HUB_SENTINEL = 0xFFFFFFFF;
  const DIR_FWD = 0;
  const DIR_REV = 1;
  const DIR_REV_HUB = 2;
  const ALL_KINDS = 0b1110; // bit (1 << kind) for kind in {1,2,3}
  const ROLE_KEY = ["", "type", "value", "both"];
  const ROLE_LABEL = ["", "Statement", "Proof", "Both"];
  const ROLE_LONG = ["", "in the statement", "in the proof", "statement and proof"];
  // Sorting/filtering by name or popularity needs the per-declaration metadata
  // of every row; only do that when it stays cheap.
  const META_SORT_MAX_ROWS = 2000;
  const META_SORT_MAX_NEW_FILES = 8;
  const VARINT_MUL_LIMIT = 34359738368; // 128^5: more than 5 groups is overlong

  const hasDoc = typeof document !== "undefined";
  const now = () => (typeof performance !== "undefined" && performance.now) ? performance.now() : Date.now();
  const fmt = (n) => (n == null || !isFinite(n)) ? "–" : Number(n).toLocaleString("en-US");
  const pct = (a, b) => b > 0 ? (100 * a / b).toFixed(1) + "%" : "0%";

  /** JS UTF-16 code-unit comparison (matches manifest `name_order: "utf16"`). */
  function cmp16(a, b) { return a < b ? -1 : a > b ? 1 : 0; }

  function shortName(name) {
    const s = String(name || "");
    const parts = s.split(".");
    if (parts.length < 2) return s;
    let last = parts[parts.length - 1];
    if (/^_/.test(last) && parts.length >= 3) last = parts[parts.length - 2] + "." + last;
    return last || s;
  }

  const LEAN_CORE_PREFIXES = new Set([
    "Eq", "And", "Or", "Not", "True", "False", "Exists", "Iff",
    "Nat", "Int", "Ne", "Fin", "List", "Option", "Subtype", "Prod", "Sum",
    "Bool", "Char", "String", "Quot", "Classical", "Decidable",
    "propext", "id", "congrArg", "OfNat", "HAdd", "HMul", "HSub", "HDiv",
    "instHAdd", "instOfNatNat", "Init", "Lean"
  ]);

  function isLeanCoreName(name) {
    let s = String(name || "");
    if (!s) return false;
    if (s.startsWith("_private.Init.") || s.startsWith("_private.Lean.")) return true;
    if (s.startsWith("_root_.")) s = s.slice(7);
    const dot = s.indexOf(".");
    const head = dot >= 0 ? s.slice(0, dot) : s;
    return LEAN_CORE_PREFIXES.has(head);
  }

  function declOrigin(m, manifest) {
    if (!m) return null;
    if (manifest && manifest.mode === "source") return { key: "project", label: "This project" };
    if (m.mod_idx >= 0) return { key: "project", label: "This project" };
    if (isLeanCoreName(m.name)) return { key: "core", label: "Lean core" };
    return { key: "mathlib", label: "Mathlib" };
  }

  // ---------------------------------------------------------------------------
  // Small LRU (Map insertion order)
  // ---------------------------------------------------------------------------
  class LRU {
    constructor(cap) { this.cap = Math.max(1, cap | 0); this.m = new Map(); }
    has(k) { return this.m.has(k); }
    get(k) {
      if (!this.m.has(k)) return undefined;
      const v = this.m.get(k);
      this.m.delete(k);
      this.m.set(k, v);
      return v;
    }
    set(k, v) {
      if (this.m.has(k)) this.m.delete(k);
      this.m.set(k, v);
      while (this.m.size > this.cap) this.m.delete(this.m.keys().next().value);
    }
    get size() { return this.m.size; }
    clear() { this.m.clear(); }
  }

  // ---------------------------------------------------------------------------
  // Fetch + gzip sniffing
  // ---------------------------------------------------------------------------
  function isGzip(u8) { return u8 && u8.length >= 2 && u8[0] === 0x1f && u8[1] === 0x8b; }

  async function gunzipIfNeeded(u8) {
    if (!isGzip(u8)) return u8;
    if (typeof DecompressionStream !== "function") {
      throw new Error("This browser cannot unpack the cross-reference data (DecompressionStream is missing). Please use a current Chrome, Edge, Firefox or Safari.");
    }
    const stream = new Blob([u8]).stream().pipeThrough(new DecompressionStream("gzip"));
    return new Uint8Array(await new Response(stream).arrayBuffer());
  }

  /** Fetch `url` as bytes; gunzip only when the payload starts with 1f 8b. */
  async function fetchGunzip(url, signal, fetchImpl) {
    const f = fetchImpl || (typeof fetch === "function" ? fetch : null);
    if (!f) throw new Error("fetch is not available");
    const resp = await f(url, signal ? { signal, credentials: "same-origin" } : { credentials: "same-origin" });
    if (!resp.ok) throw new Error("HTTP " + resp.status + " for " + url);
    const u8 = new Uint8Array(await resp.arrayBuffer());
    return gunzipIfNeeded(u8);
  }

  const utf8 = typeof TextDecoder !== "undefined" ? new TextDecoder("utf-8") : null;
  function decodeText(u8) { return utf8.decode(u8); }

  // ---------------------------------------------------------------------------
  // LXRF v1 adjacency codec
  //   header (16 B, LE): "LXRF" | u8 version=1 | u8 dir | u16 flags=0 | u32 start_id | u32 count
  //   count * u32 degree (0xFFFFFFFF = reverse list stored in rev_hub/{id}.lxrf)
  //   stream 1: ULEB128 targets (first absolute, then delta-1)
  //   stream 2: 2-bit kinds, LSB-first (1 statement, 2 proof, 3 both)
  // ---------------------------------------------------------------------------
  function parseAdjShard(input) {
    const u8 = input instanceof Uint8Array ? input : new Uint8Array(input);
    const n = u8.length;
    if (n < 16) throw new Error("Cross-reference file too short for its header (" + n + " bytes)");
    if (u8[0] !== 0x4c || u8[1] !== 0x58 || u8[2] !== 0x52 || u8[3] !== 0x46) throw new Error("Bad LXRF magic");
    const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    const version = u8[4];
    const dir = u8[5];
    const flags = dv.getUint16(6, true);
    const start = dv.getUint32(8, true);
    const count = dv.getUint32(12, true);
    if (version !== 1) throw new Error("Unsupported LXRF version " + version);
    if (dir > DIR_REV_HUB) throw new Error("Invalid LXRF direction " + dir);
    if (flags !== 0) throw new Error("Unexpected LXRF flags " + flags);
    if (dir === DIR_REV_HUB && count !== 1) throw new Error("Hub file must hold exactly one row");
    const degEnd = 16 + count * 4;
    if (degEnd > n) throw new Error("Truncated degree table");
    const deg = new Uint32Array(count);
    let total = 0;
    for (let i = 0; i < count; i++) {
      const d = dv.getUint32(16 + 4 * i, true);
      deg[i] = d;
      if (d === HUB_SENTINEL) {
        if (dir !== DIR_REV) throw new Error("Hub marker outside a reverse file (row " + i + ")");
      } else {
        total += d;
      }
    }
    const kindBytes = Math.floor((total + 3) / 4);
    if (degEnd + kindBytes > n) throw new Error("Truncated LXRF body");
    const kindStart = n - kindBytes;
    const rowOff = new Uint32Array(count + 1);
    const edgeOff = new Uint32Array(count + 1);
    let pos = degEnd;
    let e = 0;
    for (let i = 0; i < count; i++) {
      rowOff[i] = pos;
      edgeOff[i] = e;
      const d = deg[i];
      if (d === HUB_SENTINEL || d === 0) continue;
      let seen = 0;
      while (seen < d) {
        if (pos >= kindStart) throw new Error("Truncated target stream at row " + i);
        if ((u8[pos++] & 0x80) === 0) seen++;
      }
      e += d;
    }
    rowOff[count] = pos;
    edgeOff[count] = e;
    if (pos !== kindStart) throw new Error("LXRF end-of-buffer invariant failed (" + pos + " != " + kindStart + ")");
    if (total & 3) {
      const tail = u8[n - 1];
      if ((tail >>> ((total & 3) * 2)) !== 0) throw new Error("Non-zero padding bits in final kind byte");
    }
    return { u8, version, dir, flags, start, count, deg, total, kindStart, rowOff, edgeOff };
  }

  function decodeRow(sh, local) {
    if (!(local >= 0 && local < sh.count)) throw new RangeError("Row " + local + " outside file of " + sh.count);
    const d = sh.deg[local];
    if (d === HUB_SENTINEL) return { hub: true, degree: -1, targets: null, kinds: null };
    const targets = new Uint32Array(d);
    const kinds = new Uint8Array(d);
    const u8 = sh.u8;
    let pos = sh.rowOff[local];
    let prev = 0;
    for (let k = 0; k < d; k++) {
      let val = 0, mul = 1, b;
      do {
        b = u8[pos++];
        val += (b & 0x7f) * mul;
        mul *= 128;
        if (mul > VARINT_MUL_LIMIT && (b & 0x80)) throw new Error("Overlong varint at row " + local);
      } while (b & 0x80);
      prev = k === 0 ? val : prev + val + 1;
      if (prev > 0xFFFFFFFE) throw new Error("Target id overflow at row " + local);
      targets[k] = prev;
    }
    const ks = sh.kindStart;
    let e = sh.edgeOff[local];
    for (let k = 0; k < d; k++, e++) {
      const kd = (u8[ks + (e >>> 2)] >>> ((e & 3) * 2)) & 3;
      if (kd === 0) throw new Error("Invalid edge kind 0 at row " + local);
      kinds[k] = kd;
    }
    return { hub: false, degree: d, targets, kinds };
  }

  /**
   * Decode an LXRF adjacency file (raw bytes or an already-parsed object).
   * With `localIdx`, returns that row: `{ hub, degree, targets, kinds }`
   * (`hub: true` means "fetch rev_hub/{start+localIdx}.lxrf").
   * Without it, returns the header plus every decoded row.
   */
  function decodeAdjShard(bytes, localIdx) {
    const sh = bytes && bytes.rowOff ? bytes : parseAdjShard(bytes);
    if (localIdx != null) return decodeRow(sh, localIdx);
    const rows = [];
    for (let i = 0; i < sh.count; i++) rows.push(decodeRow(sh, i));
    return { version: sh.version, dir: sh.dir, flags: sh.flags, start_id: sh.start, count: sh.count, total_edges: sh.total, rows };
  }

  function lowerBound(arr, lo, hi, q) {
    while (lo < hi) {
      const mid = (lo + hi) >>> 1;
      if (cmp16(arr[mid], q) < 0) lo = mid + 1; else hi = mid;
    }
    return lo;
  }

  function hasSorted(typed, v) {
    let lo = 0, hi = typed.length;
    while (lo < hi) {
      const mid = (lo + hi) >>> 1;
      if (typed[mid] < v) lo = mid + 1; else hi = mid;
    }
    return lo < typed.length && typed[lo] === v;
  }

  function normBase(u) {
    let s = String(u == null ? "" : u);
    if (s && !s.endsWith("/")) s += "/";
    return s;
  }

  // ---------------------------------------------------------------------------
  // XrefClient
  // ---------------------------------------------------------------------------
  class XrefClient {
    constructor(baseUrl, manifest, options) {
      this.baseUrl = normBase(baseUrl || "data/xrefs/");
      this.options = options || {};
      this.fetchImpl = this.options.fetchImpl || null;
      this.manifest = null;
      this._initP = null;
      this._inflight = new Map();
      this._adj = new LRU(this.options.maxAdjFiles || 24);
      this._rows = new LRU(this.options.maxRows || 12);
      this._meta = new LRU(this.options.maxMetaFiles || 24);
      this._names = new LRU(this.options.maxNameFiles || 32);
      this._modules = null;
      this._modulesP = null;
      this.stats = { requests: 0, bytes: 0, urls: [] };
      if (manifest && manifest.schema) this._setManifest(manifest);
    }

    async init() {
      if (this.manifest) return this.manifest;
      if (!this._initP) {
        this._initP = this._fetchBytes("manifest.json").then((u8) => {
          const m = JSON.parse(decodeText(u8));
          this._setManifest(m);
          return m;
        }).catch((err) => { this._initP = null; throw err; });
      }
      return this._initP;
    }

    _setManifest(m) {
      if (!m || m.schema !== SCHEMA) throw new Error("Unexpected cross-reference schema: " + (m && m.schema));
      if (m.name_order && m.name_order !== "utf16") throw new Error("Unsupported name order " + m.name_order);
      this.manifest = m;
      const ranges = m.name_ranges || [];
      this._firstKeys = ranges.map((r) => String(r[0]));
      this._lastKeys = ranges.map((r) => String(r[1]));
      this._hubSet = new Set(m.rev_hub_ids || []);
    }

    path(key, idx) {
      const m = this.manifest;
      const tmpl = (m.paths && m.paths[key]) || ({ fwd: "fwd/{s}.lxrf", rev: "rev/{s}.lxrf", rev_hub: "rev_hub/{id}.lxrf", meta: "meta/{m}.lxrf", names: "names/{n}.lxrf" })[key];
      const pad = Number((m.pad && m.pad[key]) || 0);
      let tok = String(idx);
      if (pad > 0) while (tok.length < pad) tok = "0" + tok;
      return tmpl.replace("{s}", tok).replace("{id}", tok).replace("{m}", tok).replace("{n}", tok);
    }

    _fetchBytes(rel) {
      if (this._inflight.has(rel)) return this._inflight.get(rel);
      const url = this.baseUrl + rel;
      const p = fetchGunzip(url, null, this.fetchImpl).then((u8) => {
        this.stats.requests++;
        this.stats.bytes += u8.length;
        if (this.stats.urls.length < 4000) this.stats.urls.push(rel);
        return u8;
      });
      this._inflight.set(rel, p);
      const done = () => { this._inflight.delete(rel); };
      p.then(done, done);
      return p;
    }

    _cached(lru, key, loader) {
      const hit = lru.get(key);
      if (hit !== undefined) return Promise.resolve(hit);
      const ik = "\u0000" + key;
      if (this._inflight.has(ik)) return this._inflight.get(ik);
      const p = loader().then((v) => { lru.set(key, v); return v; });
      this._inflight.set(ik, p);
      const done = () => { this._inflight.delete(ik); };
      p.then(done, done);
      return p;
    }

    _checkId(id) {
      const n = this.manifest.n_decls;
      if (!(Number.isInteger(id) && id >= 0 && id < n)) throw new RangeError("Declaration id out of range: " + id);
    }

    _loadAdj(key, idx) {
      return this._cached(this._adj, key + ":" + idx, async () => parseAdjShard(await this._fetchBytes(this.path(key, idx))));
    }

    /** Raw adjacency row: `{ degree, targets: Uint32Array, kinds: Uint8Array, isHub }`. */
    async getRow(declId, dir) {
      await this.init();
      this._checkId(declId);
      const d = dir === "rev" ? "rev" : "fwd";
      const key = d + ":" + declId;
      const hit = this._rows.get(key);
      if (hit) return hit;
      const ssz = this.manifest.shard_size;
      const s = Math.floor(declId / ssz);
      const sh = await this._loadAdj(d, s);
      if (sh.dir !== (d === "fwd" ? DIR_FWD : DIR_REV) || sh.start !== s * ssz) throw new Error("Unexpected header in " + this.path(d, s));
      let row = decodeRow(sh, declId - sh.start);
      let isHub = false;
      if (row.hub) {
        const hs = await this._loadAdj("rev_hub", declId);
        if (hs.dir !== DIR_REV_HUB || hs.start !== declId) throw new Error("Unexpected header in " + this.path("rev_hub", declId));
        row = decodeRow(hs, 0);
        isHub = true;
      }
      const out = { declId, dir: d, degree: row.degree, targets: row.targets, kinds: row.kinds, isHub };
      this._rows.set(key, out);
      return out;
    }

    // ----- modules -----
    getModules() {
      if (this._modules) return Promise.resolve(this._modules);
      if (!this._modulesP) {
        this._modulesP = this.init().then(() => this._fetchBytes(this.manifest.modules_url || "modules.lxrf")).then((u8) => {
          const text = decodeText(u8);
          const mods = text ? text.split("\n") : [];
          if (mods.length && mods[mods.length - 1] === "") mods.pop();
          this._modules = mods;
          return mods;
        }).catch((err) => { this._modulesP = null; throw err; });
      }
      return this._modulesP;
    }
    moduleName(modIdx) {
      if (!(modIdx >= 0) || !this._modules) return null;
      return this._modules[modIdx] || null;
    }

    // ----- metadata -----
    _loadMeta(m) {
      return this._cached(this._meta, m, async () => {
        const text = decodeText(await this._fetchBytes(this.path("meta", m)));
        const lines = text.split("\n");
        if (lines.length && lines[lines.length - 1] === "") lines.pop();
        return lines;
      });
    }

    _metaFromLine(id, line) {
      const p = line.split("\t");
      if (p.length !== 12) throw new Error("Malformed metadata row for id " + id);
      const labels = this.manifest.kind_labels || [];
      const ki = +p[1];
      const modIdx = +p[6];
      return {
        decl_id: id, name: p[0], kind_idx: ki, kind: labels[ki] || "",
        fan_in: +p[2], fan_out: +p[3], fan_out_type: +p[4], fan_out_value: +p[5],
        mod_idx: modIdx, line_no: +p[7], live_mask: +p[8], dom_size: +p[9],
        type_nodes: +p[10], value_nodes: +p[11],
        module: this.moduleName(modIdx)
      };
    }

    async getMeta(declId) {
      const m = await this.getMetaBatch([declId]);
      return m.get(declId);
    }

    /** Resolve many ids at once; fetches each metadata file at most once. */
    async getMetaBatch(declIds) {
      await this.init();
      const msz = this.manifest.meta_shard_size;
      const groups = new Map();
      for (const id of declIds) {
        this._checkId(id);
        const m = Math.floor(id / msz);
        if (!groups.has(m)) groups.set(m, []);
        groups.get(m).push(id);
      }
      const out = new Map();
      await Promise.all(Array.from(groups.keys()).map(async (m) => {
        const lines = await this._loadMeta(m);
        for (const id of groups.get(m)) {
          const line = lines[id - m * msz];
          if (line == null) throw new Error("Missing metadata row for id " + id);
          out.set(id, this._metaFromLine(id, line));
        }
      }));
      return out;
    }

    /** True when resolving metadata for every id stays cheap. */
    canResolveAll(ids) {
      if (ids.length > META_SORT_MAX_ROWS) return false;
      const msz = this.manifest.meta_shard_size;
      const need = new Set();
      for (let i = 0; i < ids.length; i++) {
        const m = Math.floor(ids[i] / msz);
        if (!this._meta.has(m)) need.add(m);
        if (need.size > META_SORT_MAX_NEW_FILES) return false;
      }
      return true;
    }

    // ----- names -----
    _loadNames(n) {
      return this._cached(this._names, n, async () => {
        const text = decodeText(await this._fetchBytes(this.path("names", n)));
        const lines = text.split("\n");
        if (lines.length && lines[lines.length - 1] === "") lines.pop();
        const names = new Array(lines.length);
        for (let i = 0; i < lines.length; i++) {
          const t = lines[i].indexOf("\t");
          names[i] = t < 0 ? lines[i] : lines[i].slice(0, t);
        }
        return { lines, names, lower: null };
      });
    }

    _nameRow(line) {
      const p = line.split("\t");
      if (p.length !== 7) throw new Error("Malformed name row");
      const labels = this.manifest.kind_labels || [];
      return { name: p[0], decl_id: +p[1], kind_idx: +p[2], kind: labels[+p[2]] || "", fan_in: +p[3], fan_out: +p[4], mod_idx: +p[5], line_no: +p[6] };
    }

    _rangeFor(q) {
      // first file whose last name >= q
      return lowerBound(this._lastKeys, 0, this._lastKeys.length, q);
    }

    /** Exact name lookup: one small name file at most. */
    async lookupName(exactName) {
      await this.init();
      const q = String(exactName == null ? "" : exactName);
      if (!q) return null;
      const s = this._rangeFor(q);
      if (s >= this._lastKeys.length || cmp16(this._firstKeys[s], q) > 0) return null;
      const f = await this._loadNames(s);
      const lo = lowerBound(f.names, 0, f.names.length, q);
      if (lo < f.names.length && f.names[lo] === q) return this._nameRow(f.lines[lo]);
      return null;
    }

    /** Names starting with `prefix` (case-sensitive, sorted order). */
    async searchPrefix(prefix, limit) {
      await this.init();
      const q = String(prefix == null ? "" : prefix);
      const lim = limit == null ? 50 : limit;
      const out = [];
      if (!q || lim <= 0) return out;
      const N = this._lastKeys.length;
      let s = this._rangeFor(q);
      while (s < N && out.length < lim) {
        if (!this._firstKeys[s].startsWith(q) && cmp16(this._firstKeys[s], q + "\uffff") > 0) break;
        const f = await this._loadNames(s);
        let i = lowerBound(f.names, 0, f.names.length, q);
        for (; i < f.names.length && out.length < lim; i++) {
          if (!f.names[i].startsWith(q)) return out;
          out.push(this._nameRow(f.lines[i]));
        }
        s++;
      }
      return out;
    }

    /**
     * Case-insensitive "contains" search over every name. Cancellable via
     * `opts.signal`; reports `{ done, total, matches }` through `opts.onProgress`.
     */
    async searchSubstring(query, opts) {
      await this.init();
      const o = opts || {};
      const q = String(query == null ? "" : query).trim().toLowerCase();
      const limit = o.limit || 100;
      const N = this._lastKeys.length;
      const res = { query: q, results: [], matches: 0, scanned: 0, total: N, cancelled: false, ms: 0 };
      if (!q) return res;
      const t0 = now();
      const keep = Math.max(limit * 20, 2000);
      let pool = [];
      let next = 0;
      const signal = o.signal;
      const score = (name, lower) => {
        if (lower === q) return 0;
        const leaf = shortName(name).toLowerCase();
        if (leaf === q) return 1;
        if (leaf.startsWith(q)) return 2;
        if (lower.startsWith(q)) return 3;
        return 4;
      };
      const rank = () => {
        pool.sort((a, b) => a.s - b.s || b.r.fan_in - a.r.fan_in || a.r.name.length - b.r.name.length || cmp16(a.r.name, b.r.name));
        if (pool.length > keep) pool.length = keep;
      };
      const worker = async () => {
        for (;;) {
          if (signal && signal.aborted) return;
          const i = next++;
          if (i >= N) return;
          const f = await this._loadNames(i);
          if (signal && signal.aborted) return;
          if (!f.lower) f.lower = f.names.map((x) => x.toLowerCase());
          const L = f.lower;
          for (let k = 0; k < L.length; k++) {
            if (L[k].indexOf(q) !== -1) {
              res.matches++;
              pool.push({ s: score(f.names[k], L[k]), r: this._nameRow(f.lines[k]) });
            }
          }
          if (pool.length > keep * 4) rank();
          res.scanned++;
          if (o.onProgress) {
            try { o.onProgress({ done: res.scanned, total: N, matches: res.matches }); } catch (_) { /* ignore */ }
          }
        }
      };
      const conc = Math.max(1, Math.min(o.concurrency || 4, N));
      const workers = [];
      for (let i = 0; i < conc; i++) workers.push(worker());
      await Promise.all(workers);
      res.cancelled = !!(signal && signal.aborted);
      rank();
      res.results = pool.slice(0, limit).map((x) => x.r);
      res.ms = Math.round(now() - t0);
      return res;
    }

    // ----- edges -----
    /**
     * Paged neighbours of `declId`.
     * opts: { offset, limit, kindMask (bit 1<<kind), origin: all|project|external,
     *         sort: id|fan_in|name, desc, filterText }
     * Metadata is resolved only for the returned page unless sorting/filtering by
     * metadata is requested and cheap (see `canResolveAll`).
     */
    async getEdges(declId, dir, opts) {
      const t0 = now();
      const o = opts || {};
      const row = await this.getRow(declId, dir === "rev" ? "rev" : "fwd");
      const deg = row.degree;
      const kindMask = o.kindMask == null ? ALL_KINDS : o.kindMask;
      const offset = Math.max(0, Math.floor(o.offset || 0));
      const limit = Math.max(1, Math.floor(o.limit || 100));
      const origin = o.origin || "all";
      const sort = o.sort || "id";
      const desc = !!o.desc;
      const filterText = String(o.filterText || "").trim().toLowerCase();

      const counts = [0, 0, 0, 0];
      const K = row.kinds;
      for (let i = 0; i < deg; i++) counts[K[i]]++;

      let pos; // positions into row.targets, in display order
      if ((kindMask & ALL_KINDS) === ALL_KINDS) {
        pos = null;
      } else {
        let n = 0;
        for (let k = 1; k <= 3; k++) if (kindMask & (1 << k)) n += counts[k];
        pos = new Uint32Array(n);
        let j = 0;
        for (let i = 0; i < deg; i++) if (kindMask & (1 << K[i])) pos[j++] = i;
      }
      let n = pos ? pos.length : deg;
      const needMeta = sort !== "id" || origin !== "all" || !!filterText;
      let note = "";
      let sortApplied = "id";
      let metaApplied = false;
      let metaAvailable = true;
      let metaMap = null;
      if (n > 0) {
        let canResolve = n <= META_SORT_MAX_ROWS;
        let ids = null;
        if (canResolve) {
          ids = new Array(n);
          for (let i = 0; i < n; i++) ids[i] = row.targets[pos ? pos[i] : i];
          canResolve = this.canResolveAll(ids);
        }
        metaAvailable = canResolve;
        if (needMeta) {
          if (canResolve) {
            metaMap = await this.getMetaBatch(ids);
            let list = [];
            for (let i = 0; i < n; i++) list.push(pos ? pos[i] : i);
            if (origin !== "all") {
              list = list.filter((p) => {
                const mm = metaMap.get(row.targets[p]);
                return origin === "project" ? mm.mod_idx >= 0 : mm.mod_idx < 0;
              });
            }
            if (filterText) list = list.filter((p) => metaMap.get(row.targets[p]).name.toLowerCase().indexOf(filterText) !== -1);
            if (sort === "fan_in") {
              list.sort((a, b) => (metaMap.get(row.targets[b]).fan_in - metaMap.get(row.targets[a]).fan_in) || (row.targets[a] - row.targets[b]));
              if (!desc) list.reverse();
              sortApplied = "fan_in";
            } else if (sort === "name") {
              list.sort((a, b) => cmp16(metaMap.get(row.targets[a]).name, metaMap.get(row.targets[b]).name));
              if (desc) list.reverse();
              sortApplied = "name";
            } else if (desc) {
              list.reverse();
            }
            pos = Uint32Array.from(list);
            n = pos.length;
            metaApplied = true;
          } else {
            note = "This list has " + fmt(n) + " entries, so it is shown in ID order (sort and filters are disabled above " + fmt(META_SORT_MAX_ROWS) + " rows to keep navigation instant).";
          }
        } else if (!canResolve) {
          note = "This list has " + fmt(n) + " entries, so it is shown in ID order (sort and filters are disabled above " + fmt(META_SORT_MAX_ROWS) + " rows to keep navigation instant).";
        }
      }
      if (!metaApplied && desc && sort === "id" && n > 1) {
        const src = pos;
        const rev = new Uint32Array(n);
        for (let i = 0; i < n; i++) rev[i] = src ? src[n - 1 - i] : n - 1 - i;
        pos = rev;
      }
      const end = Math.min(n, offset + limit);
      const pageIds = [];
      const pageKinds = [];
      for (let i = offset; i < end; i++) {
        const p = pos ? pos[i] : i;
        pageIds.push(row.targets[p]);
        pageKinds.push(K[p]);
      }
      const meta = pageIds.length ? (metaMap || await this.getMetaBatch(pageIds)) : new Map();
      const rows = pageIds.map((id, i) => Object.assign({}, meta.get(id), { id, role: pageKinds[i], roleKey: ROLE_KEY[pageKinds[i]] }));
      return {
        declId, dir: row.dir, degree: deg, isHub: row.isHub,
        counts: { type: counts[1], value: counts[2], both: counts[3] },
        total: n, offset, limit, rows,
        sortApplied, desc, metaApplied, metaAvailable, note,
        ms: Math.round(now() - t0)
      };
    }

    /**
     * Exact dependency diff between two declarations (complete, untruncated):
     * removed = only A depends on it, added = only B, role_changed = both but
     * with a different role, shared = both with the same role.
     * Computes both proof-only Jaccard (kind === 2 || kind === 3) and all-references Jaccard.
     */
    async compareDecls(idA, idB) {
      const t0 = now();
      const [ra, rb] = await Promise.all([this.getRow(idA, "fwd"), this.getRow(idB, "fwd")]);
      const removed = [], added = [], roleChanged = [], shared = [];
      const A = ra.targets, B = rb.targets, KA = ra.kinds, KB = rb.kinds;
      let i = 0, j = 0;
      let proofCountA = 0, proofCountB = 0, proofInter = 0;
      while (i < A.length && j < B.length) {
        const inProofA = (KA[i] & 2) !== 0;
        const inProofB = (KB[j] & 2) !== 0;
        if (A[i] === B[j]) {
          if (inProofA) proofCountA++;
          if (inProofB) proofCountB++;
          if (inProofA && inProofB) proofInter++;
          if (KA[i] === KB[j]) shared.push({ id: A[i], kind: KA[i] });
          else roleChanged.push({ id: A[i], from: KA[i], to: KB[j] });
          i++; j++;
        } else if (A[i] < B[j]) {
          if (inProofA) proofCountA++;
          removed.push({ id: A[i], kind: KA[i] }); i++;
        } else {
          if (inProofB) proofCountB++;
          added.push({ id: B[j], kind: KB[j] }); j++;
        }
      }
      for (; i < A.length; i++) {
        if ((KA[i] & 2) !== 0) proofCountA++;
        removed.push({ id: A[i], kind: KA[i] });
      }
      for (; j < B.length; j++) {
        if ((KB[j] & 2) !== 0) proofCountB++;
        added.push({ id: B[j], kind: KB[j] });
      }
      const inter = shared.length + roleChanged.length;
      const uni = A.length + B.length - inter;
      const proofUni = proofCountA + proofCountB - proofInter;
      return {
        a: idA, b: idB, degreeA: A.length, degreeB: B.length,
        removed, added, role_changed: roleChanged, shared,
        counts: { removed: removed.length, added: added.length, role_changed: roleChanged.length, shared: shared.length },
        jaccard: uni ? inter / uni : null,
        all_inter: inter,
        all_union: uni,
        proof_jaccard: proofUni ? proofInter / proofUni : null,
        proof_inter: proofInter,
        proof_union: proofUni,
        proof_count_a: proofCountA,
        proof_count_b: proofCountB,
        ms: Math.round(now() - t0)
      };
    }

    async resolveName(nameOrId) {
      if (typeof nameOrId === "number") return this.getMeta(nameOrId);
      const r = await this.lookupName(nameOrId);
      return r ? this.getMeta(r.decl_id) : null;
    }
  }

  const clients = new Map();
  function getClient(baseUrl, manifest, options) {
    const key = normBase(baseUrl || "data/xrefs/");
    let c = clients.get(key);
    if (!c) {
      c = new XrefClient(key, manifest, options);
      clients.set(key, c);
    } else if (manifest && manifest.schema && !c.manifest) {
      c._setManifest(manifest);
    }
    return c;
  }

  // ---------------------------------------------------------------------------
  // DOM helpers (textContent only)
  // ---------------------------------------------------------------------------
  function safeHref(u) {
    const s = String(u == null ? "" : u).trim();
    if (!s) return null;
    if (/^https?:\/\//i.test(s) || /^#/.test(s) || /^\.\.?\//.test(s) || /^\/(?!\/)/.test(s)) return s;
    return null;
  }

  function h(tag, props, kids) {
    const n = document.createElement(tag);
    if (props) {
      for (const k of Object.keys(props)) {
        const v = props[k];
        if (v == null || v === false) continue;
        if (k === "text") n.textContent = String(v);
        else if (k === "class") n.className = v;
        else if (k === "href") { const sv = safeHref(v); if (sv) n.setAttribute("href", sv); }
        else if (k.length > 2 && k.slice(0, 2) === "on" && typeof v === "function") n.addEventListener(k.slice(2), v);
        else if (k === "value" || k === "checked" || k === "disabled" || k === "selected") n[k] = v;
        else n.setAttribute(k, v === true ? "" : String(v));
      }
    }
    addKids(n, kids);
    return n;
  }
  function addKids(n, kids) {
    if (kids == null) return;
    if (!Array.isArray(kids)) kids = [kids];
    for (const c of kids) {
      if (c == null || c === false) continue;
      n.appendChild(typeof c === "string" || typeof c === "number" ? document.createTextNode(String(c)) : c);
    }
  }
  const SVGNS = "http://www.w3.org/2000/svg";
  function sv(tag, attrs, kids) {
    const n = document.createElementNS(SVGNS, tag);
    if (attrs) for (const k of Object.keys(attrs)) {
      const v = attrs[k];
      if (v == null) continue;
      if (k === "text") n.textContent = String(v);
      else if (k.slice(0, 2) === "on" && typeof v === "function") n.addEventListener(k.slice(2), v);
      else n.setAttribute(k, String(v));
    }
    addKids(n, kids);
    return n;
  }
  function clear(n) { while (n && n.firstChild) n.removeChild(n.firstChild); }
  function truncate(s, n) { s = String(s || ""); return s.length > n ? s.slice(0, n - 1) + "…" : s; }
  const enc = encodeURIComponent;

  function defaultGithubUrl(opts, mod, line) {
    if (!mod || !opts.repoUrl) return null;
    const base = safeHref(String(opts.repoUrl).replace(/\/+$/, ""));
    if (!base || !/^https?:\/\//i.test(base)) return null;
    let p = String(mod);
    if (p.includes("..")) return null;
    if (!p.endsWith(".lean") && /^[A-Za-z0-9_'.]+$/.test(p)) p = p.replace(/\./g, "/") + ".lean";
    const prefix = String(opts.srcPrefix || "").replace(/^\/+/, "");
    if (prefix && !p.startsWith(prefix)) p = prefix + p;
    return base + "/blob/" + enc(String(opts.pinnedCommit || "main")) + "/" + p.split("/").map(enc).join("/") + (line > 0 ? "#L" + Math.floor(line) : "");
  }
  function githubFor(opts, mod, line) {
    if (!mod) return null;
    try {
      const u = typeof opts.buildGithubUrl === "function" ? opts.buildGithubUrl(mod, line) : defaultGithubUrl(opts, mod, line);
      const s = safeHref(u);
      return s && /^https?:\/\//i.test(s) ? s : null;
    } catch (_) { return null; }
  }

  function qualNameNodes(name) {
    const s = String(name || "");
    const leaf = shortName(s);
    if (leaf && s.length > leaf.length && s.endsWith(leaf)) {
      const prefix = s.slice(0, s.length - leaf.length);
      return [h("span", { class: "lx-q-pre" }, prefix), h("strong", { class: "lx-q-leaf" }, leaf)];
    }
    return [h("strong", { class: "lx-q-leaf" }, s)];
  }
  function roleTag(kind) {
    return h("span", { class: "lx-role lx-r" + kind, title: "Used " + ROLE_LONG[kind] }, ROLE_LABEL[kind]);
  }
  function originBadge(m, manifest) {
    if (!manifest || manifest.mode === "source") return null;
    const orig = declOrigin(m, manifest);
    if (!orig || orig.key === "project") return null;
    return h("span", { class: "lx-orig lx-orig-" + orig.key, title: orig.label + " declaration" }, orig.label);
  }
  function kindPill(kind) {
    return kind ? h("span", { class: "pill lx-kind lx-k-" + String(kind).replace(/[^a-z]/gi, "") }, kind) : null;
  }
  function skeleton(lines) {
    const w = h("div", { class: "lx-skel", "aria-hidden": "true" });
    for (let i = 0; i < (lines || 4); i++) w.appendChild(h("div", { class: "lx-skel-line", style: "width:" + (88 - (i * 13) % 40) + "%" }));
    return w;
  }
  function errBox(msg) { return h("div", { class: "lx-err", role: "alert" }, msg); }

  // ---------------------------------------------------------------------------
  // Name picker (exact + prefix autocomplete)
  // ---------------------------------------------------------------------------
  function namePicker(client, cfg) {
    const listId = "lx-ac-" + Math.random().toString(36).slice(2, 9);
    const input = h("input", {
      class: "input lx-input", type: "search", placeholder: cfg.placeholder || "Declaration name",
      "aria-label": cfg.label || "Declaration name", autocomplete: "off", spellcheck: "false",
      role: "combobox", "aria-autocomplete": "list", "aria-expanded": "false", "aria-controls": listId
    });
    const list = h("ul", { class: "lx-ac hidden", id: listId, role: "listbox" });
    const wrap = h("div", { class: "lx-picker" }, [input, list]);
    let items = [];
    let active = -1;
    let timer = null;
    let tok = 0;
    const close = () => { list.classList.add("hidden"); input.setAttribute("aria-expanded", "false"); active = -1; };
    const pick = (r) => { close(); input.value = r.name; cfg.onPick(r); };
    const paint = () => {
      clear(list);
      items.forEach((r, i) => {
        const li = h("li", { role: "option", class: "lx-ac-item" + (i === active ? " active" : ""), "aria-selected": i === active ? "true" : "false", title: r.name }, [
          h("span", { class: "lx-ac-name" }, r.name),
          h("span", { class: "lx-ac-meta" }, (r.kind ? r.kind + " · " : "") + "used by " + fmt(r.fan_in))
        ]);
        li.addEventListener("mousedown", (e) => { e.preventDefault(); pick(r); });
        list.appendChild(li);
      });
      const q = input.value.trim();
      let hasMissRow = false;
      if (!items.length && q && cfg.onMiss) {
        hasMissRow = true;
        const total = cfg.getTotal ? cfg.getTotal() : (client.manifest ? client.manifest.n_decls : 0);
        const totalStr = total ? fmt(total) + " " : "";
        const missText = "No qualified prefix match for “" + q + "” — press Enter or click here to search all " + totalStr + "names (contains)";
        const li = h("li", { role: "option", class: "lx-ac-item lx-ac-miss", "aria-selected": "false" }, [
          h("span", { class: "lx-ac-miss-text" }, missText)
        ]);
        li.addEventListener("mousedown", (e) => { e.preventDefault(); close(); cfg.onMiss(q); });
        list.appendChild(li);
      }
      const open = items.length > 0 || hasMissRow;
      list.classList.toggle("hidden", !open);
      input.setAttribute("aria-expanded", open ? "true" : "false");
    };
    const run = async () => {
      const q = input.value.trim();
      const my = ++tok;
      if (!q) { items = []; paint(); return; }
      try {
        const quick = typeof cfg.getQuickMatches === "function" ? cfg.getQuickMatches(q) : [];
        const res = await client.searchPrefix(q, 12);
        if (my !== tok) return;
        const seen = new Set();
        const merged = [];
        for (const r of quick.concat(res)) {
          if (!r || seen.has(r.name)) continue;
          seen.add(r.name);
          merged.push(r);
          if (merged.length >= 12) break;
        }
        items = merged;
        active = -1;
        paint();
      } catch (_) { /* ignore autocomplete errors */ }
    };
    input.addEventListener("input", () => { clearTimeout(timer); timer = setTimeout(run, 140); });
    input.addEventListener("blur", () => setTimeout(close, 120));
    input.addEventListener("keydown", async (e) => {
      if (e.key === "ArrowDown" && items.length) { e.preventDefault(); active = (active + 1) % items.length; paint(); }
      else if (e.key === "ArrowUp" && items.length) { e.preventDefault(); active = (active - 1 + items.length) % items.length; paint(); }
      else if (e.key === "Escape") { close(); }
      else if (e.key === "Enter") {
        e.preventDefault();
        if (active >= 0 && items[active]) { pick(items[active]); return; }
        const q = input.value.trim();
        if (!q) return;
        const exact = await client.lookupName(q).catch(() => null);
        if (exact) { pick(exact); return; }
        const quick = typeof cfg.getQuickMatches === "function" ? cfg.getQuickMatches(q) : [];
        if (quick.length) { pick(quick[0]); return; }
        if (items.length) { pick(items[0]); return; }
        const pre = await client.searchPrefix(q, 1).catch(() => []);
        if (pre.length) { pick(pre[0]); return; }
        if (cfg.onMiss) { close(); cfg.onMiss(q); }
      }
    });
    return { wrap, input, close, setValue: (v) => { input.value = v || ""; } };
  }

  // ---------------------------------------------------------------------------
  // Explorer
  // ---------------------------------------------------------------------------
  const RH_LANDMARKS = [
    "allChi", "UpperTheory.FinalTheorems.everyCharacter", "Formalism.ZeroFreeDirichlet.siegelLower",
    "Eq", "Nat"
  ];
  const sessions = new Map();
  let markerSeq = 0;

  function renderExplorer(host, opts) {
    if (!hasDoc) throw new Error("renderExplorer needs a DOM");
    const o = Object.assign({}, opts || {});
    const base = normBase(o.baseUrl || "data/xrefs/");
    const prev = host.__lxExplorer;
    if (prev && prev.baseUrl === base && host.contains(prev.root)) {
      prev.update(o);
      return prev;
    }
    const ctl = new Explorer(host, o, base);
    host.__lxExplorer = ctl;
    return ctl;
  }

  class Explorer {
    constructor(host, opts, base) {
      this.host = host;
      this.opts = opts;
      this.baseUrl = base;
      this.client = getClient(base, opts.manifest);
      if (!sessions.has(base)) sessions.set(base, { trail: [] });
      this.session = sessions.get(base);
      this.sel = null; // meta of selected declaration
      this.selTok = 0;
      this.tab = opts.initialCompare ? "compare" : "connections";
      this.cols = { rev: this._colState(), fwd: this._colState() };
      this.ego = { rev: null, fwd: null };
      this.searchAbort = null;
      this._build();
      this._start(opts.initialName, opts.initialCompare);
    }

    _colState() { return { kindMask: ALL_KINDS, origin: "all", sort: "fan_in", desc: true, pageSize: 50, page: 0, filter: "" }; }

    update(opts) {
      Object.assign(this.opts, opts || {});
      if (opts && opts.initialName && (!this.sel || this.sel.name !== opts.initialName)) {
        this.select(opts.initialName, { fromHost: true });
      }
      if (opts && opts.initialCompare) { this.tab = "compare"; this.cmpB = opts.initialCompare; this._paintTabs(); this._renderBody(); }
    }

    destroy() {
      if (this.searchAbort) this.searchAbort.abort();
      if (this._egoRO) this._egoRO.disconnect();
      if (this.egoWrap && this.egoWrap.classList.contains("lx-ego-full") && typeof document !== "undefined" && document.body) {
        document.body.classList.remove("fs-lock");
      }
      document.removeEventListener("keydown", this._onKey);
      if (this.root && this.root.parentNode) this.root.parentNode.removeChild(this.root);
      if (this.host.__lxExplorer === this) this.host.__lxExplorer = null;
    }

    _quickLandmarkMatches(q) {
      const ql = String(q || "").trim().toLowerCase();
      if (!ql || !Array.isArray(this.landmarks)) return [];
      return this.landmarks.filter((r) => {
        const leaf = shortName(r.name).toLowerCase();
        return leaf.startsWith(ql) || r.name.toLowerCase().startsWith(ql);
      });
    }

    _build() {
      const root = h("section", { class: "lx-root", "aria-label": "Cross-references" });
      this.root = root;
      this.subEl = h("p", { class: "lx-sub" }, "Loading the declaration index…");
      this.kindBar = h("div", { class: "lx-kindbar" });
      root.appendChild(h("header", { class: "lx-head" }, [
        h("div", { class: "lx-title-row" }, [
          h("h1", { class: "lx-title" }, "Cross-references"),
          h("span", { class: "pill lx-trust", title: "Every list is read directly from the exported dependency graph, a small file at a time." }, "Generated by leanre · loaded on demand")
        ]),
        this.subEl,
        this.kindBar
      ]));

      // search
      this.picker = namePicker(this.client, {
        placeholder: "Jump to a declaration (exact name or prefix)…",
        label: "Jump to a declaration",
        onPick: (r) => this.select(r.name, { push: true }),
        onMiss: (q) => this._runContains(q),
        getQuickMatches: (q) => this._quickLandmarkMatches(q),
        getTotal: () => (this.client.manifest ? this.client.manifest.n_decls : 0)
      });
      this.containsBtn = h("button", { type: "button", class: "btn sm", onclick: () => this._runContains(this.picker.input.value) }, "Search all names (contains)");
      this.cancelBtn = h("button", { type: "button", class: "btn sm hidden", onclick: () => { if (this.searchAbort) this.searchAbort.abort(); } }, "Cancel");
      this.progBar = h("div", { class: "lx-prog-fill" });
      this.progText = h("span", { class: "lx-prog-text" });
      this.progWrap = h("div", { class: "lx-prog hidden", role: "status", "aria-live": "polite" }, [h("div", { class: "lx-prog-track" }, [this.progBar]), this.progText]);
      this.searchRes = h("div", { class: "lx-sres hidden" });
      this.chips = h("div", { class: "lx-chips", "aria-label": "Starting points" });
      root.appendChild(h("div", { class: "lx-search" }, [
        h("div", { class: "lx-search-row" }, [this.picker.wrap, this.containsBtn, this.cancelBtn]),
        this.progWrap,
        this.searchRes,
        this.chips
      ]));

      this.trailEl = h("nav", { class: "lx-trail hidden", "aria-label": "Navigation trail" });
      root.appendChild(this.trailEl);

      this.tabsEl = h("div", { class: "seg lx-tabs", role: "tablist" });
      root.appendChild(this.tabsEl);
      this.body = h("div", { class: "lx-body" });
      root.appendChild(this.body);
      this.host.appendChild(root);

      this._onKey = (e) => {
        if (e.key === "Escape" && !e.defaultPrevented && this.egoWrap && this.egoWrap.classList.contains("lx-ego-full")) {
          const sd = document.getElementById("srcDrawer");
          if (sd && !sd.hidden) return;
          e.preventDefault();
          e.stopPropagation();
          this._toggleFull(false);
        }
      };
      document.addEventListener("keydown", this._onKey);
    }

    async _start(initialName, initialCompare) {
      try {
        const m = await this.client.init();
        this._paintHead(m);
        const landmarks = await this._landmarks(m);
        this.landmarks = landmarks;
        this._paintChips(landmarks);
        if (initialCompare) this.cmpB = initialCompare;
        if (initialName) this.session.trail = [];
        const first = initialName || (this.session.trail.length ? this.session.trail[this.session.trail.length - 1] : (landmarks[0] && landmarks[0].name));
        this._paintTabs();
        if (first) await this.select(first, { fromHost: !!initialName });
        else this._renderBody();
      } catch (err) {
        clear(this.body);
        this.subEl.textContent = "The cross-reference index could not be loaded.";
        this.body.appendChild(errBox(String(err && err.message || err)));
      }
    }

    _paintHead(m) {
      const unit = m.mode === "source" ? "nodes (modules & declarations)" : "declarations";
      const parts = [fmt(m.n_decls) + " " + unit, fmt(m.n_edges) + " references"];
      this.subEl.textContent = parts.join(" · ");
      // Largest hub among the ones sharing the first metadata file.
      const hubs = (m.rev_hub_ids || []).filter((id) => id < m.meta_shard_size).slice(0, 400);
      if (hubs.length) {
        this.client.getMetaBatch(hubs).then((mm) => {
          let best = null;
          for (const v of mm.values()) if (!best || v.fan_in > best.fan_in) best = v;
          if (best) this.subEl.textContent = parts.join(" · ") + " (" + fmt(best.fan_in) + " direct references to " + best.name + " alone)";
        }).catch(() => {});
      }
      const k = m.edge_kind_counts || {};
      const tot = (k.type || 0) + (k.value || 0) + (k.both || 0);
      clear(this.kindBar);
      if (tot > 0) {
        const bar = h("div", { class: "lx-kb-track", role: "img", "aria-label": "Share of references by role" }, [
          h("span", { class: "lx-kb lx-kb1", style: "width:" + (100 * k.type / tot) + "%" }),
          h("span", { class: "lx-kb lx-kb2", style: "width:" + (100 * k.value / tot) + "%" }),
          h("span", { class: "lx-kb lx-kb3", style: "width:" + (100 * k.both / tot) + "%" })
        ]);
        this.kindBar.appendChild(bar);
        this.kindBar.appendChild(h("div", { class: "lx-kb-legend" }, [
          h("span", null, [h("i", { class: "lx-dot lx-d1" }), "Statement only " + pct(k.type, tot)]),
          h("span", null, [h("i", { class: "lx-dot lx-d2" }), "Proof only " + pct(k.value, tot)]),
          h("span", null, [h("i", { class: "lx-dot lx-d3" }), "Both " + pct(k.both, tot)])
        ]));
      }
    }

    async _landmarks(m) {
      const isSource = m.mode === "source";
      const hasCustom = Array.isArray(this.opts.landmarks) && this.opts.landmarks.length > 0;
      const names = hasCustom ? this.opts.landmarks : (isSource ? ["Solution", "Main", "NavierStokes", "Euler", "FLT", "Carleson", "PrimeNumberTheoremAnd", "SpherePacking"] : RH_LANDMARKS);
      const found = (await Promise.all(names.map((n) => this.client.lookupName(n).catch(() => null)))).filter(Boolean);
      const seen = new Set(found.map((r) => r.name));
      const add = (r) => {
        if (!r || seen.has(r.name)) return;
        seen.add(r.name);
        found.push({ name: r.name, decl_id: r.decl_id, kind: r.kind, fan_in: r.fan_in, fan_out: r.fan_out });
      };
      if (found.length >= 2) return found;

      if (isSource && (m.n_modules || 0) > 0) {
        const cap = Math.min(m.n_modules, m.meta_shard_size || 16384);
        const ids = new Array(cap);
        for (let i = 0; i < cap; i++) ids[i] = i;
        const mm = await this.client.getMetaBatch(ids).catch(() => new Map());
        const mods = Array.from(mm.values()).filter((x) => !x.kind || x.kind === "module");
        if (mods.length) {
          const roots = mods.slice().sort((a, b) =>
            ((b.live_mask > 0 ? 1 : 0) - (a.live_mask > 0 ? 1 : 0)) ||
            (b.dom_size - a.dom_size) ||
            ((b.name.includes(".") ? 0 : 1) - (a.name.includes(".") ? 0 : 1)) ||
            (b.fan_out - a.fan_out) ||
            (b.fan_in - a.fan_in)
          );
          const byOut = mods.slice().sort((a, b) => (b.fan_out - a.fan_out) || (b.dom_size - a.dom_size));
          const byIn = mods.slice().sort((a, b) => (b.fan_in - a.fan_in) || (b.fan_out - a.fan_out));
          for (const x of roots.slice(0, 2)) add(x);
          for (const x of byOut.slice(0, 3)) { if (found.length >= 5) break; add(x); }
          for (const x of byIn.slice(0, 3)) { if (found.length >= 5) break; add(x); }
          if (found.length >= 2) return found;
        }
      }

      const hubs = (m.rev_hub_ids || []).slice(0, 6);
      if (hubs.length) {
        const mm = await this.client.getMetaBatch(hubs).catch(() => new Map());
        for (const x of Array.from(mm.values()).sort((a, b) => b.fan_in - a.fan_in)) add(x);
        if (found.length >= 2) return found;
      }

      const sampleN = Math.min(m.n_decls || 0, 256);
      if (sampleN > 0) {
        const ids = new Array(sampleN);
        for (let i = 0; i < sampleN; i++) ids[i] = i;
        const mm = await this.client.getMetaBatch(ids).catch(() => new Map());
        const ranked = Array.from(mm.values()).sort((a, b) =>
          ((b.live_mask > 0 ? 1 : 0) - (a.live_mask > 0 ? 1 : 0)) ||
          (b.dom_size - a.dom_size) ||
          ((b.fan_in + b.fan_out) - (a.fan_in + a.fan_out))
        );
        for (const x of ranked.slice(0, 5)) { if (found.length >= 5) break; add(x); }
      }

      if (!found.length && m.name_ranges && m.name_ranges.length) {
        const r = await this.client.lookupName(m.name_ranges[0][0]).catch(() => null);
        if (r) add(r);
      }
      return found;
    }

    _paintChips(list) {
      clear(this.chips);
      if (!list.length) return;
      this.chips.appendChild(h("span", { class: "lx-chips-lbl" }, "Try:"));
      for (const r of list) {
        this.chips.appendChild(h("button", { type: "button", class: "lx-chip", title: r.name, onclick: () => this.select(r.name, { push: true }) }, shortName(r.name)));
      }
    }

    _paintTabs() {
      clear(this.tabsEl);
      const tabs = [["connections", "Connections"], ["compare", "Compare A vs B"]];
      for (const [k, lbl] of tabs) {
        this.tabsEl.appendChild(h("button", {
          type: "button", role: "tab", class: this.tab === k ? "active" : "", "aria-selected": this.tab === k ? "true" : "false",
          onclick: () => { if (this.tab !== k) { this.tab = k; this._paintTabs(); this._renderBody(); } }
        }, lbl));
      }
    }

    _paintTrail() {
      const t = this.session.trail;
      clear(this.trailEl);
      this.trailEl.classList.toggle("hidden", t.length < 2);
      if (t.length < 2) return;
      this.trailEl.appendChild(h("span", { class: "lx-trail-lbl" }, "Trail"));
      t.forEach((name, i) => {
        if (i) this.trailEl.appendChild(h("span", { class: "lx-trail-sep", "aria-hidden": "true" }, "→"));
        const cur = i === t.length - 1;
        this.trailEl.appendChild(cur
          ? h("span", { class: "lx-trail-cur", title: name, "aria-current": "page" }, shortName(name))
          : h("a", { href: "#xrefs/" + enc(name), class: "lx-trail-link", title: name, onclick: (e) => { e.preventDefault(); this.select(name, { push: true, hop: true }); } }, shortName(name)));
      });
      this.trailEl.appendChild(h("button", { type: "button", class: "lx-trail-clear", onclick: () => { this.session.trail = this.sel ? [this.sel.name] : []; this._paintTrail(); } }, "Clear"));
    }

    _pushTrail(name) {
      const t = this.session.trail;
      const at = t.indexOf(name);
      if (at >= 0) t.length = at + 1;
      else t.push(name);
      while (t.length > 14) t.shift();
    }

    /** Select a declaration by exact name. */
    async select(name, how) {
      const hw = how || {};
      const my = ++this.selTok;
      const q = String(name || "").trim();
      if (!q) return;
      if (this.sel && this.sel.name === q && !hw.force) return;
      clear(this.body);
      this.body.appendChild(skeleton(5));
      let meta = null;
      try {
        const entry = await this.client.lookupName(q);
        if (my !== this.selTok) return;
        if (!entry) { this._notFound(q); return; }
        meta = await this.client.getMeta(entry.decl_id);
        if (meta.mod_idx >= 0) {
          await this.client.getModules().catch(() => null);
          meta.module = this.client.moduleName(meta.mod_idx);
        }
      } catch (err) {
        if (my !== this.selTok) return;
        clear(this.body);
        this.body.appendChild(errBox("Could not load " + q + ": " + (err && err.message || err)));
        return;
      }
      if (my !== this.selTok) return;
      this.sel = meta;
      this.cols.rev = Object.assign(this._colState(), { pageSize: this.cols.rev.pageSize });
      this.cols.fwd = Object.assign(this._colState(), { pageSize: this.cols.fwd.pageSize });
      if (!hw.hop) this.session.trail = [];
      this._pushTrail(meta.name);
      this._paintTrail();
      this.picker.setValue(meta.name);
      if (hw.push && typeof this.opts.onNavigateXref === "function") {
        try { this.opts.onNavigateXref(meta.name); } catch (_) { /* host routing errors are not ours */ }
      }
      this._renderBody();
    }

    async _notFound(q) {
      clear(this.body);
      const box = h("div", { class: "lx-empty" }, [
        h("p", { class: "lx-empty-title" }, "No declaration named “" + q + "” in this index."),
        h("p", { class: "lx-muted" }, "Names are matched exactly. Try a prefix in the box above, or search all names for any part of it.")
      ]);
      const btn = h("button", { type: "button", class: "btn sm", onclick: () => this._runContains(shortName(q)) }, "Search all names for “" + shortName(q) + "”");
      box.appendChild(btn);
      this.body.appendChild(box);
      const near = await this.client.searchPrefix(q.slice(0, Math.max(1, q.length - 1)), 8).catch(() => []);
      if (near.length) box.appendChild(h("ul", { class: "lx-near" }, near.map((r) => h("li", null, [
        h("a", { href: "#xrefs/" + enc(r.name), onclick: (e) => { e.preventDefault(); this.select(r.name, { push: true }); } }, r.name)
      ]))));
    }

    // ----- "contains" search across every name -----
    async _runContains(query) {
      const q = String(query || "").trim();
      if (!q) { this.picker.input.focus(); return; }
      if (this.searchAbort) this.searchAbort.abort();
      const ac = typeof AbortController === "function" ? new AbortController() : { signal: { aborted: false }, abort() { this.signal.aborted = true; } };
      this.searchAbort = ac;
      this.picker.close();
      this.progWrap.classList.remove("hidden");
      this.cancelBtn.classList.remove("hidden");
      this.containsBtn.disabled = true;
      this.searchRes.classList.add("hidden");
      const total = this.client.manifest ? this.client.manifest.name_ranges.length : 0;
      this.progText.textContent = "Scanning block 0 / " + fmt(total) + "…";
      this.progBar.style.width = "0%";
      let res;
      try {
        res = await this.client.searchSubstring(q, {
          signal: ac.signal, limit: 100, concurrency: 4,
          onProgress: (p) => {
            if (this.searchAbort !== ac) return;
            this.progBar.style.width = (100 * p.done / p.total).toFixed(1) + "%";
            this.progText.textContent = "Scanning block " + fmt(p.done) + " / " + fmt(p.total) + "… " + fmt(p.matches) + " matches";
          }
        });
      } catch (err) {
        res = { error: err };
      }
      if (this.searchAbort !== ac) return;
      this.searchAbort = null;
      this.cancelBtn.classList.add("hidden");
      this.containsBtn.disabled = false;
      this.progWrap.classList.add("hidden");
      this._paintContains(q, res);
    }

    _paintContains(q, res) {
      const box = this.searchRes;
      clear(box);
      box.classList.remove("hidden");
      const close = h("button", { type: "button", class: "lx-x", "aria-label": "Close results", onclick: () => box.classList.add("hidden") }, "×");
      if (res.error) { box.appendChild(h("div", { class: "lx-sres-hd" }, [errBox(String(res.error.message || res.error)), close])); return; }
      const head = res.cancelled
        ? "Stopped after " + fmt(res.scanned) + " of " + fmt(res.total) + " blocks: " + fmt(res.matches) + " names contain “" + q + "” so far"
        : fmt(res.matches) + " names contain “" + q + "” (" + fmt(this.client.manifest.n_decls) + " searched in " + fmt(res.ms) + " ms)";
      box.appendChild(h("div", { class: "lx-sres-hd" }, [h("span", null, head + (res.matches > res.results.length ? "; showing the best " + fmt(res.results.length) : "")), close]));
      if (!res.results.length) return;
      box.appendChild(h("ol", { class: "lx-sres-list" }, res.results.map((r) => h("li", null, [
        h("a", { href: "#xrefs/" + enc(r.name), title: r.name, class: "lx-sres-name", onclick: (e) => { e.preventDefault(); box.classList.add("hidden"); this.select(r.name, { push: true }); } }, r.name),
        h("span", { class: "lx-muted lx-sres-meta" }, (r.kind ? r.kind + " · " : "") + "used by " + fmt(r.fan_in))
      ]))));
    }

    // ----- body -----
    _renderBody() {
      if (this.egoWrap && this.egoWrap.classList.contains("lx-ego-full") && typeof document !== "undefined" && document.body) {
        document.body.classList.remove("fs-lock");
      }
      this.egoWrap = null;
      this.fullBtn = null;
      clear(this.body);
      if (!this.sel) {
        this.body.appendChild(h("div", { class: "lx-empty" }, [h("p", { class: "lx-empty-title" }, "Pick a declaration to see what uses it and what it depends on.")]));
        return;
      }
      this.body.appendChild(this._card(this.sel));
      if (this.tab === "compare") {
        const host = h("div", { class: "lx-cmp-host" });
        this.body.appendChild(host);
        this.cmp = renderCompare(host, Object.assign({}, this.opts, {
          baseUrl: this.baseUrl, nameA: this.sel.name, nameB: this.cmpB || "",
          onSelect: (name) => { this.tab = "connections"; this._paintTabs(); this.select(name, { push: true, hop: true, force: true }); },
          onPickB: (name) => { this.cmpB = name; }
        }));
        return;
      }
      this.body.appendChild(this._egoBox());
      const grid = h("div", { class: "lx-cols" });
      this.colEls = { rev: h("section", { class: "lx-col", "aria-label": "Used by" }), fwd: h("section", { class: "lx-col", "aria-label": "Depends on" }) };
      grid.appendChild(this.colEls.rev);
      grid.appendChild(this.colEls.fwd);
      this.body.appendChild(grid);
      this._renderCol("rev");
      this._renderCol("fwd");
    }

    _card(m) {
      const o = this.opts;
      const manifest = this.client.manifest || {};
      const isSource = manifest.mode === "source";
      const gh = githubFor(o, m.module, m.line_no);
      const acts = h("div", { class: "lx-card-acts" });
      if (gh) acts.appendChild(h("a", { class: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer" }, "Proof file ↗"));
      if (m.module && typeof o.onPeekSource === "function") acts.appendChild(h("button", { type: "button", class: "btn sm", onclick: () => o.onPeekSource(m.module, m.line_no, m.name) }, "Peek"));
      acts.appendChild(h("a", { class: "btn sm", href: "#item/" + enc(m.name), onclick: (e) => this._itemClick(e, m.name) }, "Inspect item ›"));
      const hubThr = manifest.hub_threshold || Infinity;
      const orig = declOrigin(m, manifest);
      const loc = m.module
        ? m.module + (m.line_no > 0 ? ":" + m.line_no : "")
        : (orig && orig.key === "core" ? "Lean 4 core declaration" : "No source file (library declaration)");
      const stat = (k, v, title) => h("div", { class: "lx-stat", title: title || null }, [h("div", { class: "lx-stat-v" }, v), h("div", { class: "lx-stat-k" }, k)]);
      const reachPill = isSource
        ? h("span", { class: "pill lx-source-pill", title: "Source scan indexes modules and declaration membership without kernel reachability" }, "Source scan")
        : (m.live_mask === 0 ? h("span", { class: "pill amber" }, "Unreachable from the main theorems") : h("span", { class: "pill emerald" }, "Reachable"));
      const origPill = !isSource && orig
        ? h("span", { class: "pill lx-orig lx-orig-" + orig.key }, orig.label)
        : null;
      const isMetaKind = m.kind === "inductive" || m.kind === "quot" || m.kind === "axiom";
      const sizeLabel = isSource ? "Statement / proof size" : (isMetaKind ? "Type / metadata AST nodes" : "Statement / proof size");
      const sizeVal = isSource ? "—" : (fmt(m.type_nodes) + " / " + fmt(m.value_nodes) + (isMetaKind ? " AST nodes" : ""));
      const sizeTitle = isSource
        ? "AST sizes are not available in source-scan mode"
        : (isMetaKind ? "Expression AST nodes (type / constructor metadata)" : "Expression AST nodes in the type and in the proof");
      return h("section", { class: "lx-card", "aria-label": "Selected declaration" }, [
        h("div", { class: "lx-card-top" }, [
          h("div", { class: "lx-card-names" }, [
            h("h2", { class: "lx-card-title", title: m.name }, shortName(m.name)),
            m.name !== shortName(m.name) ? h("div", { class: "lx-card-full" }, m.name) : null,
            h("div", { class: "lx-card-meta" }, [
              kindPill(m.kind),
              origPill,
              reachPill,
              h("span", { class: "lx-loc", title: loc }, loc)
            ])
          ]),
          acts
        ]),
        h("div", { class: "lx-stats" }, [
          stat("Used by", fmt(m.fan_in), isSource ? "Nodes that import or refer to this item" : "Declarations that refer to this one"),
          stat("Depends on", fmt(m.fan_out), isSource ? "Module imports or containing module" : (fmt(m.fan_out_type) + " in the statement, " + fmt(m.fan_out_value) + " in the proof")),
          stat("In the statement", fmt(m.fan_out_type)),
          stat("In the proof", fmt(m.fan_out_value)),
          stat("Exclusive subtree", isSource ? "—" : fmt(m.dom_size), isSource ? "Exclusive declaration subtree is not computed in source-scan mode" : "Declarations reachable only through this one"),
          stat(sizeLabel, sizeVal, sizeTitle)
        ]),
        m.fan_in >= hubThr
          ? h("p", { class: "lx-hub-note" }, "Heavily used: " + fmt(m.fan_in) + " declarations refer to " + shortName(m.name) + ". Its users are listed page by page in ID order, which keeps the page responsive.")
          : null
      ]);
    }

    _itemClick(e, name) {
      if (typeof this.opts.onNavigateItem === "function") { e.preventDefault(); this.opts.onNavigateItem(name); }
    }
    _hop(e, name) {
      if (e) e.preventDefault();
      this.select(name, { push: true, hop: true });
      try { if (this.root && this.root.scrollIntoView && this.root.getBoundingClientRect().top < 0) this.root.scrollIntoView({ block: "start" }); } catch (_) { /* ignore */ }
    }

    // ----- columns -----
    async _renderCol(dir) {
      const el = this.colEls[dir];
      const st = this.cols[dir];
      const sel = this.sel;
      const tok = (this["_colTok" + dir] = (this["_colTok" + dir] || 0) + 1);
      clear(el);
      const isRev = dir === "rev";
      el.appendChild(h("div", { class: "lx-col-hd" }, [
        h("h3", null, isRev ? "Used by ↑" : "Depends on ↓"),
        h("span", { class: "lx-count" }, fmt(isRev ? sel.fan_in : sel.fan_out))
      ]));
      const list = h("div", { class: "lx-list" }, skeleton(6));
      el.appendChild(list);
      let res;
      try {
        res = await this.client.getEdges(sel.decl_id, dir, {
          offset: st.page * st.pageSize, limit: st.pageSize, kindMask: st.kindMask,
          origin: st.origin, sort: st.sort, desc: st.desc, filterText: st.filter
        });
      } catch (err) {
        if (tok !== this["_colTok" + dir] || sel !== this.sel) return;
        clear(list);
        list.appendChild(errBox(String(err && err.message || err)));
        return;
      }
      if (tok !== this["_colTok" + dir] || sel !== this.sel) return;
      if (res.rows.some((r) => r.mod_idx >= 0) && !this.client._modules) {
        await this.client.getModules().catch(() => null);
        if (tok !== this["_colTok" + dir] || sel !== this.sel) return;
      }
      for (const r of res.rows) r.module = this.client.moduleName(r.mod_idx);
      // controls (built after load so counts are known)
      const ctr = h("div", { class: "lx-ctrls" });
      const roles = h("div", { class: "seg lx-roles", role: "group", "aria-label": "Role" });
      const roleBtn = (mask, lbl, n) => h("button", {
        type: "button", class: st.kindMask === mask ? "active" : "", "aria-pressed": st.kindMask === mask ? "true" : "false",
        onclick: () => { st.kindMask = mask; st.page = 0; this._renderCol(dir); }
      }, lbl + " " + fmt(n));
      roles.appendChild(roleBtn(ALL_KINDS, "All", res.degree));
      roles.appendChild(roleBtn(1 << 1, "Statement", res.counts.type));
      roles.appendChild(roleBtn(1 << 2, "Proof", res.counts.value));
      roles.appendChild(roleBtn(1 << 3, "Both", res.counts.both));
      ctr.appendChild(roles);
      const hubDis = !res.metaAvailable;
      const hubReason = "Disabled above " + fmt(META_SORT_MAX_ROWS) + " rows to keep navigation instant";
      const sel2 = (label, value, options, onchange, disabled, title) => {
        const s = h("select", { class: "select lx-sel", "aria-label": label, disabled: !!disabled, title: title || null, onchange: (e) => onchange(e.target.value) });
        for (const [v, t] of options) s.appendChild(h("option", { value: v, selected: String(v) === String(value) }, t));
        return h("label", { class: "lx-ctl", title: title || null }, [h("span", { class: "lx-ctl-lbl" }, label), s]);
      };
      const sortOpts = hubDis
        ? [["id_hub", "ID order (large hub)"]]
        : [["fan_in", "Most referenced"], ["name", "Name"], ["id", "ID"]];
      const row2 = h("div", { class: "lx-ctrls-row" }, [
        sel2("Sort", hubDis ? "id_hub" : st.sort, sortOpts, (v) => { st.sort = v; st.desc = v === "fan_in"; st.page = 0; this._renderCol(dir); }, hubDis, hubDis ? hubReason : null),
        h("button", { type: "button", class: "btn sm lx-dir", title: "Reverse the order", "aria-label": st.desc ? "Descending order, click to reverse" : "Ascending order, click to reverse", onclick: () => { st.desc = !st.desc; st.page = 0; this._renderCol(dir); } }, st.desc ? "↓" : "↑"),
        sel2("Origin", hubDis ? "all" : st.origin, [["all", "All"], ["project", "This project"], ["external", "External library"]], (v) => { st.origin = v; st.page = 0; this._renderCol(dir); }, hubDis, hubDis ? hubReason : null),
        sel2("Rows", st.pageSize, [[50, "50"], [100, "100"], [250, "250"]], (v) => { st.pageSize = +v; st.page = 0; this._renderCol(dir); })
      ]);
      ctr.appendChild(row2);
      const filt = h("input", {
        class: "input lx-filter", type: "search",
        placeholder: hubDis ? "Filter disabled above " + fmt(META_SORT_MAX_ROWS) + " rows" : "Filter this list by name",
        "aria-label": "Filter this list by name",
        title: hubDis ? hubReason : null,
        disabled: hubDis,
        value: hubDis ? "" : st.filter
      });
      let ft = null;
      filt.addEventListener("input", () => { clearTimeout(ft); ft = setTimeout(() => { st.filter = filt.value; st.page = 0; this._renderCol(dir); }, 260); });
      ctr.appendChild(filt);
      el.insertBefore(ctr, list);
      if (!hubDis && st.filter && document.activeElement !== filt && this._refocus === dir) { filt.focus(); filt.setSelectionRange(filt.value.length, filt.value.length); }
      filt.addEventListener("focus", () => { this._refocus = dir; });
      filt.addEventListener("blur", () => { if (this._refocus === dir) this._refocus = null; });

      clear(list);
      const notes = [];
      if (res.note) notes.push(res.note);
      else if (res.isHub && st.sort === "id") notes.push("Shown in ID order.");
      if (notes.length) list.appendChild(h("p", { class: "lx-note" }, notes.join(" ")));
      if (!res.rows.length) {
        list.appendChild(h("p", { class: "lx-muted lx-none" }, res.degree === 0
          ? (isRev ? "Nothing in this index refers to this declaration." : "This declaration refers to nothing else in this index.")
          : "No entries match these filters."));
      } else {
        list.appendChild(h("ol", { class: "lx-rows", start: String(res.offset + 1) }, res.rows.map((r) => this._row(r))));
      }
      // pager
      const pages = Math.max(1, Math.ceil(res.total / st.pageSize));
      if (st.page >= pages) st.page = pages - 1;
      const go = (p) => { st.page = Math.max(0, Math.min(pages - 1, p)); this._renderCol(dir); };
      const jump = h("input", { class: "input lx-jump", type: "number", min: "1", max: String(pages), value: String(st.page + 1), "aria-label": "Go to page" });
      jump.addEventListener("keydown", (e) => { if (e.key === "Enter") { const v = parseInt(jump.value, 10); if (v >= 1) go(v - 1); } });
      const startIdx = res.rows.length ? res.offset + 1 : 0;
      const endIdx = res.offset + res.rows.length;
      const countText = res.total > 0
        ? ("Showing " + fmt(startIdx) + "–" + fmt(endIdx) + " of " + fmt(res.total))
        : "0 matching entries";
      list.appendChild(h("div", { class: "lx-pager" }, [
        h("button", { type: "button", class: "btn sm", disabled: st.page <= 0, onclick: () => go(st.page - 1) }, "‹ Prev"),
        h("span", { class: "lx-page" }, "Page " + fmt(st.page + 1) + " of " + fmt(pages)),
        h("button", { type: "button", class: "btn sm", disabled: st.page >= pages - 1, onclick: () => go(st.page + 1) }, "Next ›"),
        pages > 2 ? h("label", { class: "lx-ctl lx-jump-wrap" }, [h("span", { class: "lx-ctl-lbl" }, "Go to"), jump]) : null,
        h("span", { class: "lx-muted lx-ms" }, countText + " · " + fmt(res.ms) + " ms")
      ]));
      this._updateEgo(dir, res);
    }

    _row(r) {
      const gh = githubFor(this.opts, r.module, r.line_no);
      const acts = h("span", { class: "lx-acts" }, [
        h("a", { href: "#item/" + enc(r.name), class: "lx-act", title: "Open the item page", onclick: (e) => this._itemClick(e, r.name) }, "Item ›"),
        gh ? h("a", { href: gh, class: "lx-act", target: "_blank", rel: "noopener noreferrer", title: "Proof file at line " + r.line_no }, "Source ↗") : null,
        (r.module && typeof this.opts.onPeekSource === "function") ? h("button", { type: "button", class: "lx-act lx-act-btn", onclick: () => this.opts.onPeekSource(r.module, r.line_no, r.name) }, "Peek") : null
      ]);
      const tags = h("span", { class: "lx-row-tags" }, [
        originBadge(r, this.client.manifest),
        roleTag(r.role)
      ]);
      return h("li", { class: "lx-row" }, [
        h("div", { class: "lx-row-main" }, [
          h("a", { href: "#xrefs/" + enc(r.name), class: "lx-hop", "data-name": r.name, title: "Hop to " + r.name, onclick: (e) => this._hop(e, r.name) }, qualNameNodes(r.name))
        ]),
        tags,
        h("span", { class: "lx-fan", title: "Used by " + fmt(r.fan_in) + " declarations" }, "↑ " + fmt(r.fan_in)),
        acts
      ]);
    }

    // ----- ego graph -----
    _egoBox() {
      this.egoSvgHost = h("div", { class: "lx-ego-svg" }, skeleton(3));
      this.fullBtn = h("button", {
        type: "button", class: "btn sm lx-full-btn",
        title: "Full screen (Esc to exit)", "aria-label": "Full screen", "aria-pressed": "false",
        onclick: () => this._toggleFull()
      }, "⛶ Full screen");
      this.egoWrap = h("section", { class: "lx-ego", "aria-label": "Neighborhood graph" }, [
        h("div", { class: "lx-ego-hd" }, [
          h("h3", null, "Neighborhood"),
          h("div", { class: "lx-ego-legend" }, [
            h("span", null, [h("i", { class: "lx-dot lx-d1" }), "Statement"]),
            h("span", null, [h("i", { class: "lx-dot lx-d2" }), "Proof"]),
            h("span", null, [h("i", { class: "lx-dot lx-d3" }), "Both"])
          ]),
          this.fullBtn
        ]),
        this.egoSvgHost
      ]);
      this.ego = { rev: null, fwd: null };
      if (typeof ResizeObserver === "function") {
        if (this._egoRO) this._egoRO.disconnect();
        this._egoRO = new ResizeObserver(() => {
          const w = this.egoSvgHost.clientWidth;
          if (w && (w < 600) !== this._egoNarrow && this.ego.rev && this.ego.fwd) this._drawEgo();
        });
        this._egoRO.observe(this.egoSvgHost);
      }
      return this.egoWrap;
    }

    _egoMarkers(id) {
      return sv("defs", null, [1, 2, 3].map((k) => sv("marker", { id: id + "-" + k, viewBox: "0 0 10 10", refX: "9", refY: "5", markerWidth: "7", markerHeight: "7", orient: "auto-start-reverse" }, [
        sv("path", { d: "M0,0 L10,5 L0,10 z", class: "lx-mk lx-mk" + k })
      ])));
    }

    _egoNode(x, y, w, r, cls, maxChars) {
      const g = sv("g", { class: "lx-node " + cls, tabindex: "0", role: "link", "aria-label": r.name });
      g.appendChild(sv("title", { text: r.name + (r.fan_in != null ? " · used by " + fmt(r.fan_in) : "") }));
      g.appendChild(sv("rect", { x, y, width: w, height: 26, rx: 6 }));
      g.appendChild(sv("text", { x: x + 10, y: y + 17, text: truncate(shortName(r.name), maxChars || 30) }));
      const go = () => this._hop(null, r.name);
      g.addEventListener("click", go);
      g.addEventListener("keydown", (e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); go(); } });
      return g;
    }

    /** Narrow screens: users above, the declaration in the middle, dependencies below. */
    _drawEgoVertical(host, L, R) {
      const W = 380, x0 = 40, nodeW = 300, rowH = 32;
      const id = "lxm" + (++markerSeq);
      const parts = [];
      let y = 8;
      parts.push(sv("text", { x: x0, y: y + 12, class: "lx-axis", text: "Used by ↑" }));
      y += 22;
      const lY = L.map((_, i) => y + i * rowH);
      y += Math.max(1, L.length) * rowH;
      const moreL = this.ego.rev.total > L.length;
      if (moreL) { parts.push(sv("text", { x: x0, y: y + 8, class: "lx-more", text: "+ " + fmt(this.ego.rev.total - L.length) + " more in the list below" })); y += 18; }
      if (!L.length) parts.push(sv("text", { x: x0, y: lY.length ? lY[0] : y - rowH + 17, class: "lx-more", text: "Nothing uses this" }));
      y += 14;
      const cy = y, cyc = cy + 22;
      y += 44 + 18;
      parts.push(sv("text", { x: x0, y: y + 12, class: "lx-axis", text: "Depends on ↓" }));
      y += 22;
      const rY = R.map((_, i) => y + i * rowH);
      if (!R.length) parts.push(sv("text", { x: x0, y: y + 17, class: "lx-more", text: "No dependencies" }));
      y += Math.max(1, R.length) * rowH;
      if (this.ego.fwd.total > R.length) { parts.push(sv("text", { x: x0, y: y + 8, class: "lx-more", text: "+ " + fmt(this.ego.fwd.total - R.length) + " more in the list below" })); y += 18; }
      const H = y + 8;
      const isFull = this.egoWrap && this.egoWrap.classList.contains("lx-ego-full");
      const svg = sv("svg", { viewBox: "0 0 " + W + " " + H, class: "lx-ego-g lx-ego-v", role: "img", "aria-label": "Declarations that use " + this.sel.name + " (top) and that it depends on (bottom)", preserveAspectRatio: isFull ? "xMidYMid meet" : "xMidYMin meet" }, [this._egoMarkers(id)]);
      const edges = sv("g", { class: "lx-edges" });
      svg.appendChild(edges);
      L.forEach((r, i) => {
        const yc = lY[i] + 13;
        edges.appendChild(sv("path", { d: "M" + x0 + "," + yc + " C" + (x0 - 30) + "," + yc + " " + (x0 - 30) + "," + cyc + " " + x0 + "," + cyc, class: "lx-edge lx-e" + r.role, "marker-end": "url(#" + id + "-" + r.role + ")" }));
        svg.appendChild(this._egoNode(x0, lY[i], nodeW, r, "lx-n-in", 36));
      });
      R.forEach((r, i) => {
        const yc = rY[i] + 13, xr = x0 + nodeW;
        edges.appendChild(sv("path", { d: "M" + xr + "," + cyc + " C" + (xr + 30) + "," + cyc + " " + (xr + 30) + "," + yc + " " + xr + "," + yc, class: "lx-edge lx-e" + r.role, "marker-end": "url(#" + id + "-" + r.role + ")" }));
        svg.appendChild(this._egoNode(x0, rY[i], nodeW, r, "lx-n-out", 36));
      });
      svg.appendChild(sv("g", { class: "lx-node lx-n-self" }, [
        sv("title", { text: this.sel.name }),
        sv("rect", { x: x0, y: cy, width: nodeW, height: 44, rx: 8 }),
        sv("text", { x: x0 + nodeW / 2, y: cy + 19, "text-anchor": "middle", class: "lx-n-self-t", text: truncate(shortName(this.sel.name), 34) }),
        sv("text", { x: x0 + nodeW / 2, y: cy + 35, "text-anchor": "middle", class: "lx-n-self-s", text: "used by " + fmt(this.sel.fan_in) + " · depends on " + fmt(this.sel.fan_out) })
      ]));
      parts.forEach((p) => svg.appendChild(p));
      host.appendChild(svg);
    }

    _toggleFull(force) {
      if (!this.egoWrap) return;
      const on = force == null ? !this.egoWrap.classList.contains("lx-ego-full") : !!force;
      this.egoWrap.classList.toggle("lx-ego-full", on);
      this.egoWrap.classList.toggle("lx-fs", on);
      if (this.root) this.root.classList.toggle("lx-has-full", on);
      if (typeof document !== "undefined" && document.body) document.body.classList.toggle("fs-lock", on);
      if (this.fullBtn) {
        this.fullBtn.textContent = on ? "✕ Exit full screen" : "⛶ Full screen";
        this.fullBtn.title = on ? "Exit full screen (Esc)" : "Full screen (Esc to exit)";
        this.fullBtn.setAttribute("aria-label", on ? "Exit full screen" : "Full screen");
        this.fullBtn.setAttribute("aria-pressed", on ? "true" : "false");
      }
      this._drawEgo();
    }

    _updateEgo(dir, res) {
      this.ego[dir] = { rows: res.rows.slice(0, 8), total: res.total };
      if (this.ego.rev && this.ego.fwd) this._drawEgo();
    }

    _drawEgo() {
      const host = this.egoSvgHost;
      if (!host || !this.ego.rev || !this.ego.fwd || !this.sel) return;
      clear(host);
      const L = this.ego.rev.rows, R = this.ego.fwd.rows;
      const hw = host.clientWidth || (this.egoWrap && this.egoWrap.clientWidth) || 960;
      this._egoNarrow = hw < 600;
      if (this._egoNarrow) { this._drawEgoVertical(host, L, R); return; }
      const W = 960, rowH = 34, nodeW = 250, cW = 260;
      const H = Math.max(160, Math.max(L.length, R.length) * rowH + 64);
      const id = "lxm" + (++markerSeq);
      const svg = sv("svg", { viewBox: "0 0 " + W + " " + H, class: "lx-ego-g", role: "img", "aria-label": "Declarations that use " + this.sel.name + " (left) and that it depends on (right)", preserveAspectRatio: "xMidYMid meet" }, [this._egoMarkers(id)]);
      const cx = (W - cW) / 2, cy = H / 2 - 22;
      const node = (x, y, w, r, cls) => this._egoNode(x, y, w, r, cls, 30);
      const yFor = (i, n) => H / 2 - (n * rowH) / 2 + i * rowH + 4;
      const edges = sv("g", { class: "lx-edges" });
      svg.appendChild(edges);
      L.forEach((r, i) => {
        const y = yFor(i, L.length) + 13;
        const x1 = 20 + nodeW, x2 = cx;
        edges.appendChild(sv("path", { d: "M" + x1 + "," + y + " C" + (x1 + 90) + "," + y + " " + (x2 - 90) + "," + (cy + 22) + " " + x2 + "," + (cy + 22), class: "lx-edge lx-e" + r.role, "marker-end": "url(#" + id + "-" + r.role + ")" }));
        svg.appendChild(node(20, yFor(i, L.length), nodeW, r, "lx-n-in"));
      });
      R.forEach((r, i) => {
        const y = yFor(i, R.length) + 13;
        const x1 = cx + cW, x2 = W - 20 - nodeW;
        edges.appendChild(sv("path", { d: "M" + x1 + "," + (cy + 22) + " C" + (x1 + 90) + "," + (cy + 22) + " " + (x2 - 90) + "," + y + " " + x2 + "," + y, class: "lx-edge lx-e" + r.role, "marker-end": "url(#" + id + "-" + r.role + ")" }));
        svg.appendChild(node(W - 20 - nodeW, yFor(i, R.length), nodeW, r, "lx-n-out"));
      });
      const c = sv("g", { class: "lx-node lx-n-self" }, [
        sv("title", { text: this.sel.name }),
        sv("rect", { x: cx, y: cy, width: cW, height: 44, rx: 8 }),
        sv("text", { x: cx + cW / 2, y: cy + 19, "text-anchor": "middle", class: "lx-n-self-t", text: truncate(shortName(this.sel.name), 30) }),
        sv("text", { x: cx + cW / 2, y: cy + 35, "text-anchor": "middle", class: "lx-n-self-s", text: "used by " + fmt(this.sel.fan_in) + " · depends on " + fmt(this.sel.fan_out) })
      ]);
      svg.appendChild(c);
      const more = (x, anchor, shown, total, word) => {
        if (total > shown) svg.appendChild(sv("text", { x, y: H - 10, "text-anchor": anchor, class: "lx-more", text: "+ " + fmt(total - shown) + " more " + word }));
      };
      svg.appendChild(sv("text", { x: 20, y: 16, class: "lx-axis", text: "Used by ↑" }));
      svg.appendChild(sv("text", { x: W - 20, y: 16, "text-anchor": "end", class: "lx-axis", text: "Depends on ↓" }));
      more(20, "start", L.length, this.ego.rev.total, "in the list below");
      more(W - 20, "end", R.length, this.ego.fwd.total, "in the list below");
      if (!L.length) svg.appendChild(sv("text", { x: 20 + nodeW / 2, y: H / 2, "text-anchor": "middle", class: "lx-more", text: "Nothing uses this" }));
      if (!R.length) svg.appendChild(sv("text", { x: W - 20 - nodeW / 2, y: H / 2, "text-anchor": "middle", class: "lx-more", text: "No dependencies" }));
      host.appendChild(svg);
    }
  }

  // ---------------------------------------------------------------------------
  // Compare A vs B (stand-alone; also used inside the explorer)
  // ---------------------------------------------------------------------------
  function renderCompare(host, opts) {
    if (!hasDoc) throw new Error("renderCompare needs a DOM");
    const o = Object.assign({}, opts || {});
    const client = getClient(o.baseUrl || "data/xrefs/", o.manifest);
    const st = { a: o.nameA || "", b: o.nameB || "", cat: "removed", page: 0, pageSize: 100, res: null, metaA: null, metaB: null, tok: 0 };
    const root = h("section", { class: "lx-cmp", "aria-label": "Compare two declarations" });
    host.appendChild(root);
    const aPick = namePicker(client, { placeholder: "Declaration A", label: "Declaration A", onPick: (r) => { st.a = r.name; run(); } });
    const bPick = namePicker(client, { placeholder: "Declaration B (type a name)", label: "Declaration B", onPick: (r) => { st.b = r.name; if (o.onPickB) o.onPickB(r.name); run(); } });
    aPick.setValue(st.a);
    bPick.setValue(st.b);
    const swap = h("button", { type: "button", class: "btn sm", title: "Swap A and B", onclick: () => { const t = st.a; st.a = st.b; st.b = t; aPick.setValue(st.a); bPick.setValue(st.b); run(); } }, "⇄ Swap");
    root.appendChild(h("div", { class: "lx-cmp-pick" }, [
      h("label", { class: "lx-cmp-slot" }, [h("span", { class: "lx-cmp-ab" }, "A"), aPick.wrap]),
      swap,
      h("label", { class: "lx-cmp-slot" }, [h("span", { class: "lx-cmp-ab" }, "B"), bPick.wrap])
    ]));
    root.appendChild(h("p", { class: "lx-muted lx-cmp-help" }, "Compares the complete lists of what A and B depend on, with the role of each dependency (statement, proof or both)."));
    const out = h("div", { class: "lx-cmp-out" });
    root.appendChild(out);

    async function run() {
      const my = ++st.tok;
      clear(out);
      if (!st.a || !st.b) { out.appendChild(h("p", { class: "lx-muted" }, "Choose a second declaration B to compare with A.")); return; }
      out.appendChild(skeleton(4));
      try {
        const [ea, eb] = await Promise.all([client.lookupName(st.a), client.lookupName(st.b)]);
        if (my !== st.tok) return;
        if (!ea || !eb) { clear(out); out.appendChild(errBox("Not in this index: " + [!ea ? st.a : null, !eb ? st.b : null].filter(Boolean).join(", "))); return; }
        const [res, mm] = await Promise.all([client.compareDecls(ea.decl_id, eb.decl_id), client.getMetaBatch([ea.decl_id, eb.decl_id])]);
        if (my !== st.tok) return;
        st.res = res; st.metaA = mm.get(ea.decl_id); st.metaB = mm.get(eb.decl_id); st.page = 0;
        if (!res[st.cat].length) st.cat = ["removed", "added", "role_changed", "shared"].find((k) => res[k].length) || "removed";
        paint();
      } catch (err) {
        if (my !== st.tok) return;
        clear(out);
        out.appendChild(errBox(String(err && err.message || err)));
      }
    }

    const CATS = [
      ["removed", "−", "Only A", "A depends on it, B does not"],
      ["added", "+", "Only B", "B depends on it, A does not"],
      ["role_changed", "⇄", "Role changed", "Both depend on it, in a different role"],
      ["shared", "=", "Shared", "Both depend on it in the same role"]
    ];

    async function paint() {
      const res = st.res;
      const my = st.tok;
      clear(out);
      const fmtJ = (j, inter, uni) => (uni > 0 && j != null) ? (j.toFixed(3) + " (" + fmt(inter) + " / " + fmt(uni) + ")") : "n/a";
      out.appendChild(h("p", { class: "lx-cmp-sum" }, [
        h("b", null, shortName(st.metaA.name)), " depends on " + fmt(res.degreeA) + " declarations, ",
        h("b", null, shortName(st.metaB.name)), " on " + fmt(res.degreeB) + ". ",
        h("span", { class: "lx-cmp-j" }, [
          "Proof-only overlap J: ", h("strong", null, fmtJ(res.proof_jaccard, res.proof_inter, res.proof_union)),
          " · All references J: ", h("strong", null, fmtJ(res.jaccard, res.all_inter, res.all_union))
        ]),
        " · computed in " + fmt(res.ms) + " ms."
      ]));
      const boxes = h("div", { class: "lx-cmp-boxes", role: "tablist" });
      for (const [k, sym, lbl, help] of CATS) {
        boxes.appendChild(h("button", {
          type: "button", role: "tab", class: "lx-cmp-box lx-cb-" + k + (st.cat === k ? " active" : ""), "aria-selected": st.cat === k ? "true" : "false", title: help,
          onclick: () => { st.cat = k; st.page = 0; paint(); }
        }, [h("span", { class: "lx-cb-sym" }, sym), h("span", { class: "lx-cb-n" }, fmt(res.counts[k])), h("span", { class: "lx-cb-l" }, lbl)]));
      }
      out.appendChild(boxes);
      const items = res[st.cat];
      const pages = Math.max(1, Math.ceil(items.length / st.pageSize));
      const slice = items.slice(st.page * st.pageSize, (st.page + 1) * st.pageSize);
      const listHost = h("div", { class: "lx-list" }, skeleton(4));
      out.appendChild(listHost);
      const mm = slice.length ? await client.getMetaBatch(slice.map((x) => x.id)) : new Map();
      if (my !== st.tok) return;
      clear(listHost);
      if (!slice.length) { listHost.appendChild(h("p", { class: "lx-muted lx-none" }, "Nothing in this group.")); return; }
      const ol = h("ol", { class: "lx-rows lx-cmp-rows", start: String(st.page * st.pageSize + 1) });
      for (const x of slice) {
        const m = mm.get(x.id);
        const roleEl = st.cat === "role_changed"
          ? h("span", { class: "lx-rolechg" }, [roleTag(x.from), h("span", { class: "lx-muted" }, " → "), roleTag(x.to)])
          : roleTag(x.kind);
        const tags = h("span", { class: "lx-row-tags" }, [
          originBadge(m, client.manifest),
          roleEl
        ]);
        ol.appendChild(h("li", { class: "lx-row" }, [
          h("div", { class: "lx-row-main" }, [
            h("a", { href: "#xrefs/" + enc(m.name), class: "lx-hop", "data-name": m.name, title: m.name, onclick: (e) => { if (o.onSelect) { e.preventDefault(); o.onSelect(m.name); } } }, qualNameNodes(m.name))
          ]),
          tags,
          h("span", { class: "lx-fan", title: "Used by " + fmt(m.fan_in) }, "↑ " + fmt(m.fan_in)),
          h("span", { class: "lx-acts" }, [h("a", { href: "#item/" + enc(m.name), class: "lx-act", onclick: (e) => { if (typeof o.onNavigateItem === "function") { e.preventDefault(); o.onNavigateItem(m.name); } } }, "Item ›")])
        ]));
      }
      listHost.appendChild(ol);
      if (pages > 1) {
        listHost.appendChild(h("div", { class: "lx-pager" }, [
          h("button", { type: "button", class: "btn sm", disabled: st.page <= 0, onclick: () => { st.page--; paint(); } }, "‹ Prev"),
          h("span", { class: "lx-page" }, "Page " + fmt(st.page + 1) + " of " + fmt(pages)),
          h("button", { type: "button", class: "btn sm", disabled: st.page >= pages - 1, onclick: () => { st.page++; paint(); } }, "Next ›")
        ]));
      }
    }

    run();
    return {
      root,
      setA(n) { st.a = n; aPick.setValue(n); return run(); },
      setB(n) { st.b = n; bPick.setValue(n); return run(); },
      get result() { return st.res; }
    };
  }

  // ---------------------------------------------------------------------------
  // #item/<name> connections strip
  // ---------------------------------------------------------------------------
  /**
   * Fill the "Used by / Depends on" strip of an item page with live data.
   * `stripHost` is the `.nb-strip` section (its first and last `.nb-col`
   * that are not `.nb-self` are replaced). Leaves the strip untouched when the
   * name is not in the index or the data cannot be loaded.
   */
  async function hydrateItemConnections(stripHost, opts) {
    if (!hasDoc || !stripHost) return { found: false };
    const o = opts || {};
    const name = String(o.name || "").trim();
    if (!name) return { found: false };
    const client = getClient(o.baseUrl || "data/xrefs/", o.manifest);
    const limit = o.limit || 8;
    const tok = (stripHost.__lxTok = (stripHost.__lxTok || 0) + 1);
    let cols = Array.from(stripHost.querySelectorAll(".nb-col")).filter((c) => !c.classList.contains("nb-self"));
    if (cols.length < 2) {
      const a = h("div", { class: "nb-col" }), b = h("div", { class: "nb-col" });
      stripHost.appendChild(a); stripHost.appendChild(b);
      cols = [a, b];
    }
    const useCol = cols[0], depCol = cols[cols.length - 1];
    const saved = [useCol, depCol].map((c) => Array.from(c.childNodes));
    const restore = () => [useCol, depCol].forEach((c, i) => { clear(c); saved[i].forEach((n) => c.appendChild(n)); });
    const head = (c, title) => { clear(c); c.appendChild(h("div", { class: "nb-hd" }, title)); c.appendChild(skeleton(4)); };
    head(useCol, "Used by ↑");
    head(depCol, "Depends on ↓");
    stripHost.classList.add("lx-hydrating");
    try {
      const entry = await client.lookupName(name);
      if (tok !== stripHost.__lxTok) return { found: false, stale: true };
      if (!entry) { restore(); stripHost.classList.remove("lx-hydrating"); return { found: false }; }
      const q = { limit, sort: "fan_in", desc: true };
      const [u, d] = await Promise.all([client.getEdges(entry.decl_id, "rev", q), client.getEdges(entry.decl_id, "fwd", q)]);
      if (tok !== stripHost.__lxTok) return { found: true, stale: true };
      const fill = (c, title, arrow, res) => {
        clear(c);
        c.appendChild(h("div", { class: "nb-hd" }, title + " " + arrow + " · " + fmt(res.degree)));
        if (!res.rows.length) {
          c.appendChild(h("p", { class: "nb-empty" }, title === "Used by" ? "Nothing in the index refers to it." : "It refers to nothing else in the index."));
          return;
        }
        c.appendChild(h("ul", { class: "nb-list" }, res.rows.map((r) => h("li", null, [
          h("a", { href: "#item/" + enc(r.name), title: r.name }, shortName(r.name)),
          h("span", { class: "nb-rel" }, ROLE_LONG[r.role])
        ]))));
        const label = res.degree > res.rows.length ? "Open all " + fmt(res.degree) + " in Cross-references ›" : "Open in Cross-references ›";
        c.appendChild(h("a", { class: "lx-nb-all", href: "#xrefs/" + enc(name) }, label));
      };
      fill(useCol, "Used by", "↑", u);
      fill(depCol, "Depends on", "↓", d);
      stripHost.classList.remove("lx-hydrating");
      stripHost.classList.add("lx-hydrated");
      return { found: true, decl_id: entry.decl_id, used_by: u.degree, depends_on: d.degree };
    } catch (err) {
      if (tok === stripHost.__lxTok) { restore(); stripHost.classList.remove("lx-hydrating"); }
      return { found: false, error: String(err && err.message || err) };
    }
  }

  // ---------------------------------------------------------------------------
  // Self-test (for #selftest=1). `assert(cond, message)`.
  // ---------------------------------------------------------------------------
  function encodeAdjForTest(dir, start, rows) {
    const bytes = [];
    const u32 = (v) => { bytes.push(v & 255, (v >>> 8) & 255, (v >>> 16) & 255, (v >>> 24) & 255); };
    bytes.push(0x4c, 0x58, 0x52, 0x46, 1, dir, 0, 0);
    u32(start); u32(rows.length);
    let total = 0;
    for (const r of rows) { if (r === null) u32(HUB_SENTINEL); else { u32(r.length); total += r.length; } }
    const leb = (v) => { while (v >= 0x80) { bytes.push((v % 128) | 0x80); v = Math.floor(v / 128); } bytes.push(v); };
    for (const r of rows) {
      if (!r || !r.length) continue;
      leb(r[0][0]);
      for (let k = 1; k < r.length; k++) leb(r[k][0] - r[k - 1][0] - 1);
    }
    const kb = new Array(Math.floor((total + 3) / 4)).fill(0);
    let e = 0;
    for (const r of rows) { if (!r) continue; for (const [, kd] of r) { kb[e >> 2] |= kd << ((e & 3) * 2); e++; } }
    return new Uint8Array(bytes.concat(kb));
  }

  async function runSelfTest(assert, opts) {
    const o = opts || {};
    const t0 = now();
    const results = { pass: true, checks: 0, timings: {} };
    const ok = (c, msg) => { results.checks++; if (!c) results.pass = false; assert(!!c, "xrefs: " + msg); };
    // Codec round trip
    const rowsIn = [[[0, 1], [5, 2], [300, 3], [70000, 1], [4294967294, 2]], [], null, [[7, 3]]];
    const sh = parseAdjShard(encodeAdjForTest(DIR_REV, 4096, rowsIn));
    ok(sh.start === 4096 && sh.count === 4 && sh.total === 6, "header decodes start/count/total");
    const r0 = decodeAdjShard(sh, 0);
    ok(Array.from(r0.targets).join(",") === "0,5,300,70000,4294967294" && Array.from(r0.kinds).join(",") === "1,2,3,1,2", "varint deltas and 2-bit kinds decode");
    ok(decodeAdjShard(sh, 1).degree === 0 && decodeAdjShard(sh, 2).hub === true && decodeAdjShard(sh, 3).targets[0] === 7, "empty row, hub marker and trailing row decode");
    let threw = false;
    try { parseAdjShard(encodeAdjForTest(DIR_FWD, 0, [null])); } catch (_) { threw = true; }
    ok(threw, "hub marker is rejected outside reverse files");
    threw = false;
    try { const b = encodeAdjForTest(DIR_FWD, 0, [[[1, 1], [2, 2]]]); parseAdjShard(b.slice(0, b.length - 2)); } catch (_) { threw = true; }
    ok(threw, "truncated file is rejected");
    ok(cmp16("\ud835\udcb0", "\uffff") === -1 && cmp16("Z", "a") === -1 && cmp16("a", "a") === 0, "UTF-16 code-unit order");
    ok(isLeanCoreName("And.right") && isLeanCoreName("Eq") && isLeanCoreName("OfNat.ofNat") && !isLeanCoreName("CategoryTheory.Over.left"), "Lean core prefix detection");
    const raw = new Uint8Array([1, 2, 3]);
    ok((await gunzipIfNeeded(raw)) === raw, "non-gzip bytes pass through");
    if (typeof CompressionStream === "function") {
      const gz = new Uint8Array(await new Response(new Blob([raw]).stream().pipeThrough(new CompressionStream("gzip"))).arrayBuffer());
      ok(Array.from(await gunzipIfNeeded(gz)).join(",") === "1,2,3", "gzip bytes are unpacked");
    }
    if (o.baseUrl) {
      const client = o.client || getClient(o.baseUrl, o.manifest);
      const m = await client.init();
      ok(m.schema === SCHEMA, "manifest schema");
      const first = m.name_ranges && m.name_ranges.length ? m.name_ranges[0][0] : null;
      if (first) {
        let t = now();
        const e = await client.lookupName(first);
        results.timings.lookup = Math.round(now() - t);
        ok(e && e.name === first, "exact lookup of the first name");
        const meta = await client.getMeta(e.decl_id);
        ok(meta.name === first && meta.fan_in === e.fan_in && meta.fan_out === e.fan_out, "metadata agrees with the name index");
        t = now();
        const f = await client.getRow(e.decl_id, "fwd");
        results.timings.fwd = Math.round(now() - t);
        ok(f.degree === meta.fan_out, "forward degree matches fan_out");
        for (const tgt of Array.from(f.targets).slice(0, 3)) {
          const rv = await client.getRow(tgt, "rev");
          ok(hasSorted(rv.targets, e.decl_id), "reverse list of " + tgt + " contains " + e.decl_id);
        }
        const pre = await client.searchPrefix(first.slice(0, 3), 5);
        ok(pre.length > 0 && pre.every((r) => r.name.startsWith(first.slice(0, 3))), "prefix search");
      }
      for (const nm of (o.names || ["Eq", "allChi"])) {
        const e = await client.lookupName(nm);
        if (!e) continue;
        const t = now();
        const rv = await client.getEdges(e.decl_id, "rev", { limit: 100 });
        results.timings["rev:" + nm] = Math.round(now() - t);
        ok(rv.degree === e.fan_in && rv.rows.length === Math.min(100, e.fan_in), nm + ": reverse degree matches fan_in (" + rv.degree + ")");
      }
    }
    results.ms = Math.round(now() - t0);
    return results;
  }

  const api = {
    version: VERSION,
    SCHEMA,
    ROLE_LABEL,
    ROLE_LONG,
    ALL_KINDS,
    KIND_MASK: { all: ALL_KINDS, type: 1 << 1, value: 1 << 2, both: 1 << 3 },
    XrefClient,
    LRU,
    getClient,
    fetchGunzip,
    gunzipIfNeeded,
    parseAdjShard,
    decodeAdjShard,
    cmp16,
    shortName,
    isLeanCoreName,
    declOrigin,
    renderExplorer,
    renderCompare,
    hydrateItemConnections,
    runSelfTest,
    _encodeAdjForTest: encodeAdjForTest
  };
  root.LeanreXrefs = api;
  if (typeof module !== "undefined" && module.exports) module.exports = api;
})(typeof window !== "undefined" ? window : globalThis);
