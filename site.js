/* ==========================================================================
   leanre static site frontend (site.js)
   Hash-routed, no third-party scripts, data files fetched on demand, and all
   untrusted text rendered through textContent / sanitizers.
   Compatible with manifest schema `leanre.site_manifest/1` (both the RH
   showcase and generic / --demo Lean 4 repositories).
   ========================================================================== */
(function () {
  "use strict";

  const $ = (sel, root) => (root || document).querySelector(sel);
  const $$ = (sel, root) => Array.from((root || document).querySelectorAll(sel));

  // ---------- State, fetch telemetry (internal only) & caches ----------
  const state = {
    manifest: null,
    theme: "dark",
    route: { tab: "overview", sub: "", arg: "" },
    loadedBytes: 0,
    loadedFiles: new Set(),
    cacheJson: new Map(),
    cacheText: new Map(),
    searchShards: new Map(),
    circuit: {
      mode: "macro",
      target: "",
      data: null,
      history: [],
      scale: 1,
      tx: 16,
      ty: 16,
      filter: "",
      selectorFilter: "",
      selectedItem: null,
      hoveredItem: null,
      dragMoved: 0,
      stageWired: false
    },
    findingSlug: "",
    dossierMode: "analysis", // "analysis" | "research"
    dossierSlug: "",
    dossierQ: "",
    dossierCat: "all",
    bpId: "",
    bpQ: "",
    bpStatus: "all",
    bpSort: { key: "dom", dir: "desc" },
    bpPage: 0,
    bpSelectedNode: "",
    flirt: { status: "all", severity: "all", q: "", page: 0, expanded: "" },
    atlas: { hicMode: "ratio", showTerra: true, showStreaks: true, showNamed: true, twinScope: "all", twinSort: "jaccard" },
    portability: { island: "" },
    search: { q: "", scope: "all", lastShardPrefix: "" },
    selftestRunning: false,
    base: "",            // "" for a standalone export, "p/<slug>/" inside a gallery
    registry: null,      // parsed projects.json (leanre.projects_registry/1) or null
    outline: null,       // parsed data/outline.json once fetched
    rail: { open: true, mode: "spine", mobileOpen: false },
    overviewLens: "spine",
    map2d: { proj: "knn", layer: "landmarks", color: "pillar", sel: -1 },
    item: { name: "", view: "summary" },
    rootManifest: null
  };

  const SHOWCASE_ORDER = [
    { mode: "macro", target: "", label: "Whole repository", desc: "The main parts of the proof and how they connect", tag: "Map" },
    { mode: "bundle", target: "OpenLiteratureStatements", label: "OpenLiteratureStatements", desc: "Most consumers ignore the hypotheses they receive (152 of 195)", tag: "Structure" },
    { mode: "theorem", target: "llOf_alt", label: "llOf_alt", desc: "11 hypotheses are accepted but never used", tag: "Theorem" },
    { mode: "bundle", target: "RealInAlt", label: "RealInAlt", desc: "Three fields that only hold under a side condition", tag: "Structure" },
    { mode: "bundle", target: "HypsAlt", label: "HypsAlt", desc: "The 46-field record that feeds part A", tag: "Structure" },
    { mode: "theorem", target: "ch_balance", label: "ch_balance", desc: "An exact Fourier balance identity", tag: "Theorem" },
    { mode: "theorem", target: "linkGLOBAL7_items", label: "linkGLOBAL7_items", desc: "How the global bridge is wired together", tag: "Theorem" },
    { mode: "theorem", target: "sEEofTT", label: "sEEofTT", desc: "An evaluation step with five case splits", tag: "Theorem" }
  ];

  const MODE_LABEL = { macro: "Repository map", bundle: "Structure", theorem: "Theorem" };

  // ---------- Security & Escaping Utilities ----------
  function escapeHtml(value) {
    return String(value == null ? "" : value)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;")
      .replace(/'/g, "&#39;");
  }

  function safeHref(url) {
    const raw = String(url == null ? "" : url).trim();
    if (!raw || /[\x00-\x1f\x7f]/.test(raw)) return null;
    if (raw.startsWith("#")) return raw;
    if (/^https?:\/\//i.test(raw)) return raw;
    if (raw.startsWith("//")) return null;
    if (/^[a-zA-Z][a-zA-Z0-9+.-]*:/.test(raw)) return null;
    return raw;
  }

  function formatBytes(bytes) {
    const n = Number(bytes) || 0;
    if (n < 1024) return n + " B";
    if (n < 1024 * 1024) return (n / 1024).toFixed(1) + " KB";
    return (n / (1024 * 1024)).toFixed(2) + " MB";
  }

  function fmtInt(n) {
    const num = Number(n);
    if (!Number.isFinite(num)) return "—";
    return num.toLocaleString("en-US");
  }

  // "1 module", "2 modules". Pass the plural form when it is irregular.
  function plural(n, one, many) {
    const num = Number(n);
    return fmtInt(num) + " " + (num === 1 ? one : (many || one + "s"));
  }

  // Long Lean identifiers: allow line breaks after "." and "_" instead of
  // chopping mid-word. Returns a DocumentFragment (text nodes and <wbr>).
  function identWbr(text) {
    const frag = document.createDocumentFragment();
    String(text == null ? "" : text).split(/(?<=[._])/).forEach((part, i) => {
      if (i) frag.appendChild(document.createElement("wbr"));
      frag.appendChild(document.createTextNode(part));
    });
    return frag;
  }

  function shortName(name) {
    const s = String(name || "");
    const idx = s.lastIndexOf(".");
    return idx >= 0 ? s.slice(idx + 1) : s;
  }

  function el(tag, attrs, children) {
    const node = document.createElement(tag);
    if (attrs) {
      for (const [k, v] of Object.entries(attrs)) {
        if (v == null || v === false) continue;
        if (k === "className") node.className = String(v);
        else if (k === "textContent") node.textContent = String(v);
        else if (k === "style" && typeof v === "object") Object.assign(node.style, v);
        else if (k.startsWith("on") && typeof v === "function") node.addEventListener(k.slice(2).toLowerCase(), v);
        else if (k === "href") {
          const safe = safeHref(v);
          if (safe) {
            node.setAttribute("href", safe);
            if (tag === "a" && !attrs.title) {
              const up = upstreamRepoOf(safe);
              if (up) node.setAttribute("title", "Upstream proof repository " + up + " at the pinned commit (independent of leanre)");
            }
          }
        } else if (v === true) node.setAttribute(k, "");
        else node.setAttribute(k, String(v));
      }
    }
    if (children != null) {
      const list = Array.isArray(children) ? children : [children];
      for (const ch of list) {
        if (ch == null || ch === false) continue;
        node.appendChild(typeof ch === "string" ? document.createTextNode(ch) : ch);
      }
    }
    return node;
  }

  const LEANRE_REPO_URL = "https://github.com/bohemian-miser/leanre";

  // "owner/repo" for GitHub links that are not leanre's own repository.
  function upstreamRepoOf(url) {
    const m = String(url || "").match(/^https:\/\/github\.com\/([A-Za-z0-9-]+)\/([A-Za-z0-9._-]+)/);
    if (!m) return "";
    const slug = m[1] + "/" + m[2];
    return slug.toLowerCase() === "bohemian-miser/leanre" ? "" : slug;
  }

  function clearEl(node) {
    while (node && node.firstChild) node.removeChild(node.firstChild);
  }

  function normalizeRelPath(p) {
    const s = String(p || "").trim();
    if (!s) return "";
    if (s.startsWith("./")) return s;
    return "./" + s.replace(/^\/+/, "");
  }

  // Resolve a manifest-relative path against the active project directory.
  function projectRelPath(p) {
    const s = String(p || "").trim().replace(/^\.\//, "").replace(/^\/+/, "");
    if (!s) return "";
    return normalizeRelPath(state.base + s);
  }

  // Internal telemetry only (read by #selftest=1); never shown in the UI.
  function recordLoad(key, byteLen) {
    if (!state.loadedFiles.has(key)) {
      state.loadedFiles.add(key);
      state.loadedBytes += Math.max(0, Number(byteLen) || 0);
    }
  }

  async function fetchText(relPath) {
    const key = projectRelPath(relPath);
    if (!key) throw new Error("Empty file path");
    if (state.cacheText.has(key)) return state.cacheText.get(key);
    const resp = await fetch(key, { credentials: "same-origin" });
    if (!resp.ok) throw new Error("HTTP " + resp.status + " for " + key);
    const txt = await resp.text();
    const blen = new TextEncoder().encode(txt).length;
    recordLoad(key, blen);
    state.cacheText.set(key, txt);
    return txt;
  }

  async function fetchJson(relPath, opts) {
    const key = (opts && opts.root) ? normalizeRelPath(relPath) : projectRelPath(relPath);
    if (!key) throw new Error("Empty file path");
    if (state.cacheJson.has(key)) return state.cacheJson.get(key);
    const resp = await fetch(key, { credentials: "same-origin" });
    if (!resp.ok) throw new Error("HTTP " + resp.status + " for " + key);
    const txt = await resp.text();
    const blen = new TextEncoder().encode(txt).length;
    recordLoad(key, blen);
    const obj = JSON.parse(txt);
    state.cacheJson.set(key, obj);
    return obj;
  }

  // ---------- Pinned GitHub Link Builder ----------
  function buildGithubUrl(pathOrAnchor, lineOpt) {
    const m = state.manifest;
    if (!m || !m.repo_url) return null;
    const base = safeHref(String(m.repo_url).replace(/\/+$/, ""));
    if (!base || !/^https?:\/\//i.test(base)) return null;
    const commit = String(m.pinned_commit || "main").trim();
    const prefix = String(m.src_prefix || "").replace(/^\/+/, "");
    let raw = String(pathOrAnchor || "").trim();
    if (!raw) return null;

    let frag = "";
    const mHash = raw.match(/^([^#]+)#L(\d+)(?:-L?(\d+))?$/);
    const mCol = raw.match(/^([^:]+):(\d+)(?:-(\d+))?$/);
    if (mHash) {
      raw = mHash[1];
      frag = "#L" + mHash[2] + (mHash[3] ? "-L" + mHash[3] : "");
    } else if (mCol) {
      raw = mCol[1];
      frag = "#L" + mCol[2] + (mCol[3] ? "-L" + mCol[3] : "");
    }
    if (!frag && lineOpt && Number(lineOpt) > 0) {
      frag = "#L" + Math.floor(Number(lineOpt));
    }

    raw = raw.replace(/^\/+/, "");
    if (raw.includes("..")) return null;
    // Convert module name like Development.Foo.Bar into Development/Foo/Bar.lean
    if (!raw.endsWith(".lean") && !raw.includes("/") && /^[A-Za-z0-9_'.]+$/.test(raw)) {
      raw = raw.replace(/\./g, "/") + ".lean";
    }
    if (prefix && !raw.startsWith(prefix)) {
      raw = prefix + raw;
    }
    return safeHref(base + "/blob/" + encodeURIComponent(commit) + "/" + raw + frag);
  }

  function makeGithubAnchor(pathOrAnchor, lineOpt, labelOpt) {
    const url = buildGithubUrl(pathOrAnchor, lineOpt);
    const text = labelOpt || (pathOrAnchor ? String(pathOrAnchor) + (lineOpt && !String(pathOrAnchor).includes(":") && !String(pathOrAnchor).includes("#L") ? ":" + lineOpt : "") : "");
    if (!url) return el("code", { textContent: text || "—" });
    return el("a", { href: url, target: "_blank", rel: "noopener noreferrer", className: "mono", textContent: text });
  }

  // Anchor link plus a small inline "src" preview button (when the link is a
  // public GitHub .lean blob that the source viewer can open).
  function makeSourceLink(pathOrAnchor, lineOpt, labelOpt, titleOpt) {
    const a = makeGithubAnchor(pathOrAnchor, lineOpt, labelOpt);
    const url = buildGithubUrl(pathOrAnchor, lineOpt);
    const btn = url ? makeSrcButton(url, titleOpt || labelOpt || String(pathOrAnchor || "")) : null;
    return btn ? el("span", { className: "src-link" }, [a, btn]) : a;
  }

  // ==========================================================================
  // LIVE LEAN 4 SOURCE VIEWER
  // Files are fetched from raw.githubusercontent.com only when the reader asks
  // for a preview. Nothing is fetched on page load, and no upstream source is
  // stored in this repository.
  // ==========================================================================
  const RAW_HOST = "raw.githubusercontent.com";
  const RAW_CACHE_CAP = 40;
  const rawCache = new Map(); // rawUrl -> text (insertion order = LRU order)
  const SRC_CONTEXT = { "15": 15, "40": 40, full: Infinity };

  // Strictly convert https://github.com/<owner>/<repo>/blob/<ref>/<path>[#Ln[-Lm]]
  // into its raw.githubusercontent.com equivalent. Anything else returns null.
  function githubBlobToRaw(blobUrl) {
    const s = String(blobUrl == null ? "" : blobUrl).trim();
    if (!s || s.length > 2048 || /[\s\x00-\x1f\x7f\\<>"`]/.test(s)) return null;
    const m = s.match(/^https:\/\/github\.com\/([A-Za-z0-9](?:[A-Za-z0-9-]{0,38}))\/([A-Za-z0-9._-]{1,100})\/blob\/([A-Za-z0-9._-]{1,100})\/([^#?]{1,1500})(?:#L(\d{1,7})(?:-L(\d{1,7}))?)?$/);
    if (!m) return null;
    const [, owner, repo, ref, path, l1, l2] = m;
    if (repo === "." || repo === ".." || ref === "." || ref === "..") return null;
    const segs = path.split("/");
    for (const seg of segs) {
      if (!seg || seg === "." || seg === "..") return null;
      if (!/^(?:[\p{L}\p{N}._'+~=,@!-]|%[0-9A-Fa-f]{2})+$/u.test(seg)) return null;
      let dec;
      try { dec = decodeURIComponent(seg); } catch (_) { return null; }
      if (dec === "." || dec === ".." || /[\/\\\x00-\x1f]/.test(dec)) return null;
    }
    const raw = "https://" + RAW_HOST + "/" + owner + "/" + repo + "/" + ref + "/" + path;
    let parsed;
    try { parsed = new URL(raw); } catch (_) { return null; }
    if (parsed.protocol !== "https:" || parsed.hostname !== RAW_HOST || parsed.username || parsed.password || parsed.port) return null;
    const line = l1 ? Number(l1) : null;
    const lineEnd = l2 ? Number(l2) : null;
    return {
      raw,
      blob: "https://github.com/" + owner + "/" + repo + "/blob/" + ref + "/" + path,
      owner, repo, ref, path,
      line: line && line > 0 ? line : null,
      lineEnd: lineEnd && line && lineEnd >= line ? lineEnd : null
    };
  }

  function isLeanBlob(url) {
    const p = githubBlobToRaw(url);
    return Boolean(p && /\.lean$/i.test(p.path));
  }

  async function fetchRawSource(rawUrl) {
    if (rawCache.has(rawUrl)) {
      const txt = rawCache.get(rawUrl);
      rawCache.delete(rawUrl);
      rawCache.set(rawUrl, txt);
      return txt;
    }
    const resp = await fetch(rawUrl, { mode: "cors", credentials: "omit", referrerPolicy: "no-referrer", cache: "force-cache" });
    if (!resp.ok) {
      const err = new Error("HTTP " + resp.status);
      err.status = resp.status;
      throw err;
    }
    const txt = await resp.text();
    rawCache.set(rawUrl, txt);
    while (rawCache.size > RAW_CACHE_CAP) rawCache.delete(rawCache.keys().next().value);
    return txt;
  }

  // ---- Lean 4 tokenizer (pure; emits [className|null, text] pairs) ----
  const LEAN_DECL_KW = new Set([
    "theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "instance", "axiom", "example",
    "opaque", "noncomputable", "private", "protected", "partial", "unsafe", "namespace", "section", "end",
    "open", "variable", "universe", "import", "where", "deriving", "mutual", "set_option", "attribute",
    "macro", "syntax", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "local", "scoped", "extends", "export"
  ]);
  const LEAN_NAME_AFTER = new Set(["theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "instance", "axiom", "opaque", "namespace", "section"]);
  const LEAN_TACTIC_KW = new Set([
    "by", "have", "let", "show", "obtain", "rcases", "exact", "refine", "refine'", "apply", "rw", "rwa", "erw", "simp", "simp_all",
    "simpa", "dsimp", "intro", "intros", "rintro", "fun", "match", "with", "if", "then", "else", "calc", "constructor",
    "cases", "induction", "use", "exists", "linarith", "nlinarith", "omega", "norm_num", "positivity", "ring", "ring_nf",
    "field_simp", "gcongr", "unfold", "specialize", "exfalso", "contradiction", "assumption", "trivial", "decide",
    "aesop", "filter_upwards", "convert", "congr", "ext", "funext", "push_neg", "by_contra", "by_cases", "split",
    "at", "from", "do", "return", "for", "in", "suffices", "change", "subst", "nofun", "nomatch", "termination_by", "decreasing_by"
  ]);
  const LEAN_SORRY = new Set(["sorry", "admit"]);
  const LEAN_PUNCT = new Set("()[]{}⟨⟩,:;|←→↔∀∃λ·•$<>=+-*/^&∧∨¬≤≥≠∈∉⊆⊂∘×⁻¹∑∏∫∣%!?@#.".split(""));
  const LEAN_IDENT_RX = /^(?:«[^»\n]*»|[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]*)(?:\.(?:«[^»\n]*»|[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]*))*/u;
  const LEAN_NUM_RX = /^(?:0x[0-9A-Fa-f_]+|0b[01_]+|\d[\d_]*(?:\.\d+)?(?:[eE][+-]?\d+)?)/;

  function tokenizeLeanLine(line, st) {
    const out = [];
    const push = (cls, txt) => {
      if (!txt) return;
      const last = out[out.length - 1];
      if (last && last[0] === cls) last[1] += txt;
      else out.push([cls, txt]);
    };
    const n = line.length;
    let i = 0;
    while (i < n) {
      if (st.depth > 0) {
        const start = i;
        while (i < n && st.depth > 0) {
          if (line.startsWith("/-", i)) { st.depth++; i += 2; }
          else if (line.startsWith("-/", i)) { st.depth--; i += 2; }
          else i++;
        }
        push("tok-com", line.slice(start, i));
        continue;
      }
      const rest = line.slice(i);
      if (rest.startsWith("--")) { push("tok-com", rest); break; }
      if (rest.startsWith("/-")) { st.depth = 1; push("tok-com", "/-"); i += 2; continue; }
      const c = line[i];
      if (c === "\"") {
        let j = i + 1;
        while (j < n && line[j] !== "\"") j += line[j] === "\\" ? 2 : 1;
        push("tok-str", line.slice(i, Math.min(n, j + 1)));
        i = Math.min(n, j + 1);
        continue;
      }
      if (c === "'") {
        const mc = rest.match(/^'(?:\\.|[^'\\])'/);
        if (mc) { push("tok-str", mc[0]); i += mc[0].length; continue; }
      }
      if (rest.startsWith("@[")) {
        const close = rest.indexOf("]");
        const seg = close > 0 ? rest.slice(0, close + 1) : rest;
        push("tok-attr", seg);
        i += seg.length;
        continue;
      }
      if (/[0-9]/.test(c)) {
        const mn = rest.match(LEAN_NUM_RX);
        if (mn) { push("tok-num", mn[0]); i += mn[0].length; continue; }
      }
      const mi = rest.match(LEAN_IDENT_RX);
      if (mi) {
        let word = mi[0];
        let cls = "";
        if (LEAN_SORRY.has(word)) cls = "tok-sorry";
        else if (LEAN_DECL_KW.has(word)) cls = "tok-kw";
        else if (LEAN_TACTIC_KW.has(word)) cls = "tok-tac";
        else if (st.expectName) cls = "tok-name";
        st.expectName = LEAN_NAME_AFTER.has(word);
        push(cls, word);
        i += word.length;
        continue;
      }
      if (rest.startsWith(":=")) { push("tok-punct", ":="); i += 2; st.expectName = false; continue; }
      if (LEAN_PUNCT.has(c)) { push("tok-punct", c); i += 1; if (c !== "." ) st.expectName = false; continue; }
      push(null, c);
      i += 1;
    }
    return out;
  }

  // Identifiers carry class "" (or "tok-name"); when `links` maps an identifier
  // to a verified declaration name, it becomes an in-page link to #item/<name>.
  function renderLeanTokens(tokens, links) {
    const frag = document.createDocumentFragment();
    for (const [cls, txt] of tokens) {
      if ((cls === "" || cls === "tok-name") && links && links.has(txt)) {
        const full = links.get(txt);
        const a = document.createElement("a");
        a.className = "src-sym" + (cls ? " " + cls : "");
        a.setAttribute("href", "#item/" + encodeURIComponent(full));
        a.setAttribute("title", "Inspect " + full);
        a.textContent = txt;
        frag.appendChild(a);
      } else if (cls) {
        const sp = document.createElement("span");
        sp.className = cls;
        sp.textContent = txt;
        frag.appendChild(sp);
      } else {
        frag.appendChild(document.createTextNode(txt));
      }
    }
    return frag;
  }

  function copyText(txt) {
    try {
      if (navigator.clipboard && navigator.clipboard.writeText) return navigator.clipboard.writeText(txt).then(() => true, () => false);
    } catch (_) { /* fall through */ }
    return Promise.resolve(false);
  }

  // ---- Drawer chrome ----
  // pair / swapped / tab / view / back belong to the proof diff view (v2.5).
  const srcView = {
    root: null, backdrop: null, mode: "single", specs: [], ctx: "15", seq: 0, lastFocus: null, texts: [],
    pair: null, swapped: false, tab: "source", view: "side", back: null, loadingSeq: 0, ldHunks: []
  };

  function ensureSourceDrawer() {
    if (srcView.root) {
      if (!document.contains(srcView.root)) placeSourceDrawer(true);
      return srcView.root;
    }
    const backdrop = el("div", { className: "src-backdrop", hidden: true, onclick: closeSourceDrawer });
    const root = el("aside", { className: "src-drawer", id: "srcDrawer", role: "dialog", "aria-modal": "true", "aria-labelledby": "srcDrawerTitle", hidden: true }, [
      el("header", { className: "src-hd" }, [
        el("div", { className: "src-hd-main" }, [
          el("div", { className: "src-title", id: "srcDrawerTitle" }),
          el("div", { className: "src-path", id: "srcDrawerPath" })
        ]),
        el("button", { type: "button", className: "icon-btn src-close", id: "srcDrawerClose", "aria-label": "Close source viewer", title: "Close (Esc)", textContent: "×", onclick: closeSourceDrawer })
      ]),
      el("div", { className: "src-toolbar" }, [
        el("div", { className: "seg", id: "srcCtxSeg", role: "group", "aria-label": "Lines of context" }, [["15", "±15"], ["40", "±40"], ["full", "Full file"]].map(([k, lbl]) =>
          el("button", { type: "button", "data-ctx": k, textContent: lbl, onclick: () => { srcView.ctx = k; rerenderSourcePanes(); } })
        )),
        el("span", { className: "src-status", id: "srcStatus", "aria-live": "polite" }),
        el("div", { className: "spacer" }),
        el("button", { type: "button", className: "btn sm", id: "srcCopyBtn", textContent: "Copy snippet", onclick: (ev) => copySourceSnippet(0, ev.currentTarget) }),
        el("a", { className: "btn sm primary", id: "srcGhBtn", target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" })
      ]),
      el("div", { className: "src-body", id: "srcBody" }),
      el("footer", { className: "src-foot", textContent: "Fetched live from raw.githubusercontent.com (not hosted in this repository)." })
    ]);
    document.body.appendChild(backdrop);
    document.body.appendChild(root);
    srcView.root = root;
    srcView.backdrop = backdrop;
    // Escape is handled by the single ordered handler in the global chrome wiring.
    return root;
  }

  // Keep the drawer above a full-screen chart or diagram: a native full-screen
  // element only paints its own subtree, so the drawer moves inside it while open.
  function placeSourceDrawer(toBody) {
    if (!srcView.root) return;
    const fsEl = !toBody && fsState.el && document.contains(fsState.el) ? fsState.el : null;
    const host = fsEl || document.body;
    if (srcView.backdrop.parentNode !== host) host.appendChild(srcView.backdrop);
    if (srcView.root.parentNode !== host) host.appendChild(srcView.root);
  }

  // Show a short status message (and a "Copied" state on the clicked button)
  // that clears itself.
  function flashStatus(node, msg, btn, ms) {
    const wait = ms || 2400;
    if (node) {
      node.textContent = msg;
      clearTimeout(node._flashT);
      node._flashT = setTimeout(() => { if (node.textContent === msg) node.textContent = ""; }, wait);
    }
    if (btn) {
      if (!btn.dataset.label) btn.dataset.label = btn.textContent;
      btn.textContent = "✓ Copied";
      btn.classList.add("copied");
      clearTimeout(btn._flashT);
      btn._flashT = setTimeout(() => { btn.textContent = btn.dataset.label; btn.classList.remove("copied"); }, Math.min(wait, 1800));
    }
  }

  function normalizeSourceSpec(spec) {
    const s = spec || {};
    const parsed = githubBlobToRaw(s.url);
    const line = Number(s.line) > 0 ? Math.floor(Number(s.line)) : (parsed && parsed.line) || null;
    return {
      url: s.url || "",
      parsed,
      title: String(s.title || (parsed ? parsed.path.split("/").pop() : "Source")),
      label: s.label ? String(s.label) : "",
      line,
      lineEnd: parsed && parsed.lineEnd && line === parsed.line ? parsed.lineEnd : null,
      fallbackUrl: s.fallbackUrl || "",
      fallbackLabel: s.fallbackLabel || "",
      links: s.links instanceof Map ? s.links : null,
      fixtureText: typeof s._fixtureText === "string" ? s._fixtureText : null
    };
  }

  function blobLineUrl(spec, line) {
    if (!spec.parsed) return spec.url || spec.fallbackUrl || "";
    return spec.parsed.blob + (line ? "#L" + line : "");
  }

  function openSourcePeek(spec) {
    return openSourceViewer("single", [normalizeSourceSpec(spec)]);
  }

  // opts (optional): { pair, swap, tab: "lemmas"|"source", view: "side"|"unified"|"split", filter }
  function openSourceCompare(leftSpec, rightSpec, opts) {
    return openSourceViewer("compare", [normalizeSourceSpec(leftSpec), normalizeSourceSpec(rightSpec)], opts);
  }

  async function openSourceViewer(mode, specs, opts) {
    const o = opts || {};
    const root = ensureSourceDrawer();
    placeSourceDrawer();
    srcView.mode = mode;
    srcView.specs = specs;
    srcView.texts = Array.isArray(o.texts) && o.texts.length === specs.length ? o.texts.slice() : specs.map(() => null);
    srcView.errors = Array.isArray(o.errors) && o.errors.length === specs.length ? o.errors.slice() : specs.map(() => null);
    pdiffPrepare(mode, o);
    const seq = ++srcView.seq;
    if (root.hidden) srcView.lastFocus = document.activeElement;
    root.classList.toggle("compare", mode === "compare");
    root.hidden = false;
    srcView.backdrop.hidden = false;
    document.body.classList.add("src-open");
    requestAnimationFrame(() => root.classList.add("open"));

    const first = specs[0];
    $("#srcDrawerTitle").textContent = mode === "compare" ? (srcView.pair ? "Compare proofs" : "Compare sources") : first.title;
    $("#srcDrawerPath").textContent = mode === "compare"
      ? specs.map((s) => (s.label ? s.label + ": " : "") + s.title).join("  ·  ")
      : (first.parsed ? first.parsed.path + (first.line ? ":" + first.line : "") : (first.label || ""));
    const gh = $("#srcGhBtn");
    const copyBtn = $("#srcCopyBtn");
    gh.classList.toggle("hidden", mode === "compare" || !blobLineUrl(first, first.line));
    copyBtn.classList.toggle("hidden", mode === "compare");
    if (mode !== "compare") {
      const u = safeHref(blobLineUrl(first, first.line));
      if (u) gh.setAttribute("href", u); else gh.removeAttribute("href");
    }
    $("#srcStatus").textContent = "";
    pdiffSyncChrome();

    if (pdiffOwnsBody()) pdiffRenderBody();
    else buildSourcePanesShell();
    const closeBtn = $("#srcDrawerClose");
    if (closeBtn) closeBtn.focus({ preventScroll: true });

    // The offline lemma diff needs no source; files are fetched only when the
    // reader switches to the Lean source tab.
    if (srcView.tab === "lemmas") return true;
    return loadSourceTexts(seq);
  }

  function buildSourcePanesShell() {
    const body = $("#srcBody");
    clearEl(body);
    body.classList.remove("pdiff-host");
    srcView.specs.forEach((s, idx) => {
      body.appendChild(el("section", { className: "src-pane", "data-pane": String(idx) }, [
        srcView.mode === "compare" ? buildPaneHeader(s, idx) : null,
        el("div", { className: "src-scroll" }, [
          el("div", { className: "src-loading" }, [el("div", { className: "spinner" }), el("span", { textContent: "Loading source…" })])
        ])
      ]));
    });
  }

  // Fetch each pane's file once. Specs are matched by identity so a swap while
  // loading still lands each text on the right side.
  async function loadSourceTexts(seq) {
    if (srcView.loadingSeq === seq) return seq === srcView.seq;
    srcView.loadingSeq = seq;
    await Promise.all(srcView.specs.slice().map(async (s) => {
      let idx = srcView.specs.indexOf(s);
      if (idx >= 0 && (srcView.texts[idx] != null || srcView.errors[idx])) {
        if (seq === srcView.seq) renderSourcePane(idx);
        return;
      }
      let text = null, error = null;
      try {
        if (s.fixtureText != null) text = s.fixtureText;
        else if (!s.parsed) throw Object.assign(new Error("not-github"), { code: "not-github" });
        else text = await fetchRawSource(s.parsed.raw);
      } catch (err) {
        error = err;
      }
      if (seq !== srcView.seq) return;
      idx = srcView.specs.indexOf(s);
      if (idx < 0) return;
      if (error) srcView.errors[idx] = error; else srcView.texts[idx] = text;
      renderSourcePane(idx);
    }));
    return seq === srcView.seq;
  }

  function buildPaneHeader(spec, idx) {
    const u = safeHref(blobLineUrl(spec, spec.line));
    return el("div", { className: "src-pane-hd" }, [
      el("div", { className: "src-pane-id" }, [
        spec.label ? el("span", { className: "src-pane-tag", textContent: spec.label }) : null,
        el("span", { className: "src-pane-title", textContent: spec.title, title: spec.title })
      ]),
      el("div", { className: "src-pane-acts" }, [
        spec.parsed ? el("button", { type: "button", className: "btn sm", textContent: "Copy", onclick: (ev) => copySourceSnippet(idx, ev.currentTarget) }) : null,
        u ? el("a", { className: "btn sm", href: u, target: "_blank", rel: "noopener noreferrer", textContent: "Proof file ↗" }) : null
      ])
    ]);
  }

  function sourceErrorMessage(spec, err) {
    if (err && err.code === "not-github") {
      return spec.fallbackUrl
        ? "This declaration lives outside the pinned repository, so there is no inline preview."
        : "Inline preview is only available for files in public GitHub repositories.";
    }
    const st = err && err.status;
    if (st === 404) return "The file was not found at this commit, or the repository is private.";
    if (st === 429 || st === 403) return "GitHub is limiting requests right now. Try again in a moment.";
    if (st) return "GitHub returned an error (HTTP " + st + ").";
    return "The file could not be fetched. You may be offline.";
  }

  function rerenderSourcePanes() {
    srcView.specs.forEach((_, idx) => renderSourcePane(idx));
  }

  function sliceBounds(spec, total, ctxKey) {
    const target = Math.min(Math.max(1, spec.line || 1), Math.max(1, total));
    const end = Math.min(Math.max(target, spec.lineEnd || target), Math.max(1, total));
    const k = SRC_CONTEXT[ctxKey || srcView.ctx] ?? 15;
    if (!Number.isFinite(k) || !spec.line) {
      if (!spec.line && Number.isFinite(k)) return { from: 1, to: Math.min(total, 2 * k + 1), target: null, end: null };
      return { from: 1, to: total, target: spec.line ? target : null, end: spec.line ? end : null };
    }
    return { from: Math.max(1, target - k), to: Math.min(total, end + k), target, end };
  }

  // Build the highlighted code block for one file. Shared by the drawer and the
  // docked pane on #item pages.
  function buildSourceCode(spec, text, ctxKey, opts) {
    const o = opts || {};
    const lines = String(text).replace(/\r\n?/g, "\n").split("\n");
    if (lines.length > 1 && lines[lines.length - 1] === "") lines.pop();
    const total = lines.length;
    const b = sliceBounds(spec, total, ctxKey);
    const st = { depth: 0, expectName: false };
    for (let i = 0; i < b.from - 1; i++) tokenizeLeanLine(lines[i], st);
    const links = spec.links || null;

    const code = el("div", { className: "src-code", role: "table", "aria-label": "Source lines " + b.from + " to " + b.to });
    if (b.from > 1) {
      code.appendChild(el("button", { type: "button", className: "src-more", textContent: "Show " + fmtInt(b.from - 1) + " earlier lines", onclick: () => o.onExpand && o.onExpand() }));
    }
    let hlRow = null;
    for (let ln = b.from; ln <= b.to; ln++) {
      const isHl = b.target != null && ln >= b.target && ln <= b.end;
      const href = safeHref(blobLineUrl(spec, ln));
      const row = el("div", { className: "src-line" + (isHl ? " hl" : ""), "data-line": String(ln), role: "row" }, [
        el("a", {
          className: "src-ln", href: href || null, role: "rowheader", title: "Highlight line " + ln + " and copy its link", textContent: String(ln),
          onclick: (ev) => { ev.preventDefault(); if (o.onSelectLine) o.onSelectLine(ln); }
        }),
        el("span", { className: "src-text", role: "cell" }, [renderLeanTokens(tokenizeLeanLine(lines[ln - 1], st), links)])
      ]);
      if (isHl && !hlRow) hlRow = row;
      code.appendChild(row);
    }
    if (b.to < total) {
      code.appendChild(el("button", { type: "button", className: "src-more", textContent: "Show " + fmtInt(total - b.to) + " later lines", onclick: () => o.onExpand && o.onExpand() }));
    }
    return { code, hlRow, bounds: b, total };
  }

  function scrollToHighlight(scroller, hlRow, smooth) {
    if (!scroller || !hlRow) return;
    requestAnimationFrame(() => {
      const top = hlRow.offsetTop - scroller.clientHeight / 2 + hlRow.offsetHeight;
      try { scroller.scrollTo({ top: Math.max(0, top), behavior: smooth ? "smooth" : "auto" }); }
      catch (_) { scroller.scrollTop = Math.max(0, top); }
    });
  }

  function renderSourcePane(idx) {
    if (srcView.mode === "compare" && srcView.tab === "lemmas") return;
    if (srcView.mode === "compare" && srcView.view !== "side") { pdiffRenderSourceDiff(); return; }
    const pane = srcView.root && srcView.root.querySelector('.src-pane[data-pane="' + idx + '"]');
    if (!pane) return;
    const scroller = pane.querySelector(".src-scroll");
    clearEl(scroller);
    $$("#srcCtxSeg button").forEach((b) => b.classList.toggle("active", b.dataset.ctx === srcView.ctx));
    const spec = srcView.specs[idx];
    const err = srcView.errors[idx];
    const text = srcView.texts[idx];
    if (err || text == null) {
      if (!err) {
        scroller.appendChild(el("div", { className: "src-loading" }, [el("div", { className: "spinner" }), el("span", { textContent: "Loading source…" })]));
        return;
      }
      scroller.appendChild(buildSourceError(spec, err));
      return;
    }
    const built = buildSourceCode(spec, text, srcView.ctx, {
      onExpand: () => { srcView.ctx = "full"; rerenderSourcePanes(); },
      onSelectLine: (ln) => selectSourceLine(idx, ln)
    });
    scroller.appendChild(built.code);
    scrollToHighlight(scroller, built.hlRow, srcView.ctx === "full");
  }

  function buildSourceError(spec, err) {
    const u = safeHref(blobLineUrl(spec, spec.line));
    const alt = safeHref(spec.fallbackUrl);
    return el("div", { className: "src-error" }, [
      el("h4", { textContent: "Couldn't show this file inline" }),
      el("p", { textContent: sourceErrorMessage(spec, err) }),
      u && spec.parsed ? el("a", { className: "btn primary", href: u, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }) : null,
      alt ? el("a", { className: "btn", href: alt, target: "_blank", rel: "noopener noreferrer", textContent: spec.fallbackLabel || "Open documentation ↗" }) : null
    ]);
  }

  // Docked (in-page) source pane used on #item pages. Fetches only when called.
  async function renderDockedSource(container, rawSpec, ctxKey) {
    const spec = normalizeSourceSpec(rawSpec);
    let ctx = ctxKey || "15";
    clearEl(container);
    const status = el("span", { className: "src-status", "aria-live": "polite" });
    const seg = el("div", { className: "seg", role: "group", "aria-label": "Lines of context" });
    const scroller = el("div", { className: "src-scroll docked" }, [
      el("div", { className: "src-loading" }, [el("div", { className: "spinner" }), el("span", { textContent: "Loading source…" })])
    ]);
    const ghHref = safeHref(blobLineUrl(spec, spec.line));
    container.appendChild(el("div", { className: "src-toolbar docked" }, [
      seg, status, el("div", { className: "spacer" }),
      ghHref ? el("a", { className: "btn sm", href: ghHref, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }) : null
    ]));
    container.appendChild(scroller);
    container.appendChild(el("div", { className: "src-foot", textContent: "Fetched live from raw.githubusercontent.com (not hosted in this repository)." }));
    let text = null;
    try {
      if (spec.fixtureText != null) text = spec.fixtureText;
      else if (!spec.parsed) throw Object.assign(new Error("not-github"), { code: "not-github" });
      else text = await fetchRawSource(spec.parsed.raw);
    } catch (err) {
      clearEl(scroller);
      scroller.appendChild(buildSourceError(spec, err));
      return false;
    }
    const draw = () => {
      clearEl(seg);
      [["15", "±15"], ["40", "±40"], ["full", "Full file"]].forEach(([k, lbl]) => seg.appendChild(el("button", {
        type: "button", className: ctx === k ? "active" : "", textContent: lbl, onclick: () => { ctx = k; draw(); }
      })));
      clearEl(scroller);
      const built = buildSourceCode(spec, text, ctx, {
        onExpand: () => { ctx = "full"; draw(); },
        onSelectLine: (ln) => {
          spec.line = ln; spec.lineEnd = null;
          $$(".src-line", scroller).forEach((r) => r.classList.toggle("hl", r.dataset.line === String(ln)));
          copyText(blobLineUrl(spec, ln)).then((ok) => { flashStatus(status, ok ? "Link to line " + ln + " copied" : "Line " + ln); });
        }
      });
      scroller.appendChild(built.code);
      scrollToHighlight(scroller, built.hlRow, false);
    };
    draw();
    return true;
  }

  function selectSourceLine(idx, ln) {
    const spec = srcView.specs[idx];
    if (!spec) return;
    spec.line = ln;
    spec.lineEnd = null;
    const pane = srcView.root.querySelector('.src-pane[data-pane="' + idx + '"]');
    if (pane) $$(".src-line", pane).forEach((r) => r.classList.toggle("hl", r.dataset.line === String(ln)));
    const u = blobLineUrl(spec, ln);
    if (srcView.mode !== "compare") {
      const gh = $("#srcGhBtn");
      const safe = safeHref(u);
      if (gh && safe) gh.setAttribute("href", safe);
      if (spec.parsed) $("#srcDrawerPath").textContent = spec.parsed.path + ":" + ln;
    }
    copyText(u).then((ok) => {
      flashStatus($("#srcStatus"), ok ? "Link to line " + ln + " copied" : "Line " + ln);
    });
  }

  function copySourceSnippet(idx, btn) {
    const spec = srcView.specs[idx];
    const text = srcView.texts[idx];
    if (!spec || text == null) return;
    const lines = text.replace(/\r\n?/g, "\n").split("\n");
    const b = sliceBounds(spec, lines.length);
    const snippet = lines.slice(b.from - 1, b.to).join("\n");
    const which = srcView.mode === "compare" && spec.label ? " from " + spec.label : "";
    copyText(snippet).then((ok) => {
      flashStatus($("#srcStatus"), ok ? "Copied lines " + b.from + "–" + b.to + which : "Copy is not available in this browser", ok ? btn : null);
    });
  }

  function closeSourceDrawer() {
    if (!srcView.root || srcView.root.hidden) return;
    srcView.seq++;
    srcView.root.classList.remove("open");
    srcView.root.hidden = true;
    srcView.backdrop.hidden = true;
    placeSourceDrawer(true);
    document.body.classList.remove("src-open");
    const f = srcView.lastFocus;
    srcView.lastFocus = null;
    if (f && typeof f.focus === "function" && document.contains(f)) f.focus({ preventScroll: true });
  }

  // One label for inline source previews across the site: "Peek" on the small
  // inline button, "Peek source" on toolbar buttons.
  function srcButtonLabel(text, className) {
    const t = String(text == null ? "" : text).trim();
    if (!t || /^(src|source|show source inline|peek|peek source)$/i.test(t)) return /\bbtn\b/.test(className || "") ? "Peek source" : "Peek";
    return t;
  }

  function makeSrcButton(url, title, opts) {
    if (!isLeanBlob(url)) return null;
    const o = opts || {};
    return el("button", {
      type: "button",
      className: o.className || "src-peek-btn",
      title: "Preview Lean source inline",
      "aria-label": "Preview " + (title || "source") + " inline",
      textContent: srcButtonLabel(o.text, o.className),
      onclick: (ev) => { ev.preventDefault(); ev.stopPropagation(); openSourcePeek({ url, title, line: o.line, label: o.label, links: o.links }); }
    });
  }

  // Add a small preview button after every GitHub .lean link inside rendered Markdown.
  function decorateLeanLinks(container) {
    if (!container) return 0;
    let count = 0;
    $$("a[href]", container).forEach((a) => {
      if (a.dataset.srcDecorated === "1") return;
      const href = a.getAttribute("href") || "";
      if (!isLeanBlob(href)) return;
      a.dataset.srcDecorated = "1";
      const label = (a.textContent || "").trim();
      const btn = makeSrcButton(href, label || undefined);
      if (btn) {
        a.insertAdjacentElement("afterend", btn);
        count++;
      }
    });
    return count;
  }

  // ---------- Strict XSS-Safe SVG Mounter (DOMParser + Allowlist Strip) ----------
  const FORBIDDEN_SVG_TAGS = new Set(["script", "foreignobject", "iframe", "object", "embed", "link", "meta", "audio", "video"]);

  function sanitizeSvgTree(rootEl) {
    const stack = [rootEl];
    while (stack.length) {
      const node = stack.pop();
      if (!node || node.nodeType !== 1) continue;
      const tag = String(node.localName || node.tagName || "").toLowerCase();
      if (FORBIDDEN_SVG_TAGS.has(tag)) {
        node.remove();
        continue;
      }
      const attrs = Array.from(node.attributes || []);
      for (const attr of attrs) {
        const name = attr.name.toLowerCase();
        const val = attr.value || "";
        if (name.startsWith("on") || name === "srcdoc") {
          node.removeAttribute(attr.name);
        } else if (name === "href" || name === "xlink:href") {
          if (!val.trim().startsWith("#")) node.removeAttribute(attr.name);
        } else if (/javascript:|vbscript:|data:text\/html/i.test(val)) {
          node.removeAttribute(attr.name);
        }
      }
      for (const ch of Array.from(node.children || [])) {
        stack.push(ch);
      }
    }
  }

  // Plain words for internal circuit labels baked into the diagram data.
  function circuitPlainLabel(s) {
    return String(s == null ? "" : s)
      .replace(/Default-0 \/ refl \/ True pin/g, "trivial proof input")
      .replace(/Dropped \/ Unplugged Binder \(0 wires\)/g, "unused argument")
      .replace(/\bTrue pin\b/g, "trivial proof input")
      .replace(/\bshell shell\b/g, "shell")
      .replace(/\(raw ×([\d,]+) excluded\), value_nodes=([\d,]+)/g, (_, n, v) => "(" + n + " trivial uses hidden) · " + v + " AST nodes")
      .replace(/\bvalue_nodes=([\d,]+)/g, "$1 AST nodes");
  }

  function mountSafeSvg(container, svgText) {
    clearEl(container);
    if (!svgText || typeof svgText !== "string") return null;
    const parser = new DOMParser();
    const doc = parser.parseFromString(svgText, "image/svg+xml");
    if (doc.querySelector("parsererror")) {
      container.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "This diagram could not be displayed" }),
        el("p", { textContent: "The diagram file is not well-formed SVG." })
      ]));
      return null;
    }
    const svgEl = doc.documentElement;
    if (!svgEl || String(svgEl.localName || "").toLowerCase() !== "svg") return null;
    sanitizeSvgTree(svgEl);
    // Rewrite internal labels in visible text and hover titles.
    svgEl.querySelectorAll("text, tspan, title").forEach((n) => {
      if (n.children.length) return;
      const v = circuitPlainLabel(n.textContent);
      if (v !== n.textContent) n.textContent = v;
    });
    const imported = document.importNode(svgEl, true);
    container.appendChild(imported);
    return imported;
  }

  // ---------- Strict XSS-Safe Markdown & Math Renderer (no third-party code) ----------
  // ---- TeX engine begin ----
  // A small TeX-math parser: source -> node list -> element tree. The tree is
  // emitted as an escaped HTML string (Markdown path), as DOM nodes built with
  // createElement/textContent (cards), or as plain Unicode text (titles,
  // search). Only <span>/<sup>/<sub>/<b> elements with fixed class names are
  // ever produced, and every text run is escaped or set as a text node.
  const TEX_BB = { R: "ℝ", C: "ℂ", Q: "ℚ", Z: "ℤ", N: "ℕ", F: "𝔽", A: "𝔸", P: "ℙ", H: "ℍ", T: "𝕋", K: "𝕂" };
  const TEX_CAL = { A: "𝒜", B: "ℬ", C: "𝒞", D: "𝒟", E: "ℰ", F: "ℱ", G: "𝒢", H: "ℋ", I: "ℐ", J: "𝒥", K: "𝒦", L: "ℒ", M: "ℳ", N: "𝒩", O: "𝒪", P: "𝒫", Q: "𝒬", R: "ℛ", S: "𝒮", T: "𝒯", U: "𝒰", V: "𝒱", W: "𝒲", X: "𝒳", Y: "𝒴", Z: "𝒵" };
  const TEX_FRAK_X = { C: "ℭ", H: "ℌ", I: "ℑ", R: "ℜ", Z: "ℨ" };
  const TEX_BB_X = { C: "ℂ", H: "ℍ", N: "ℕ", P: "ℙ", Q: "ℚ", R: "ℝ", Z: "ℤ" };
  function texFontChar(font, ch) {
    const c = ch.charCodeAt(0);
    const up = c >= 65 && c <= 90;
    const lo = c >= 97 && c <= 122;
    const dg = c >= 48 && c <= 57;
    if (font === "bb") {
      if (up) return TEX_BB_X[ch] || String.fromCodePoint(0x1d538 + c - 65);
      if (lo) return String.fromCodePoint(0x1d552 + c - 97);
      if (dg) return String.fromCodePoint(0x1d7d8 + c - 48);
    } else if (font === "cal") {
      if (up) return TEX_CAL[ch];
    } else if (font === "frak") {
      if (up) return TEX_FRAK_X[ch] || String.fromCodePoint(0x1d504 + c - 65);
      if (lo) return String.fromCodePoint(0x1d51e + c - 97);
    }
    return ch;
  }

  // name -> [character, class]; class is TeX's atom class (ord, bin, rel, op,
  // open, close, punct), which drives the spacing between atoms.
  const TEX_SYM = Object.create(null);
  const texDef = (cls, pairs) => pairs.trim().split(/\s+/).forEach((p) => {
    const k = p.indexOf("=");
    TEX_SYM[p.slice(0, k)] = [p.slice(k + 1), cls];
  });
  texDef("ord", "alpha=α beta=β gamma=γ delta=δ epsilon=ε varepsilon=ε zeta=ζ eta=η theta=θ vartheta=ϑ iota=ι kappa=κ lambda=λ mu=μ nu=ν xi=ξ pi=π varpi=ϖ rho=ρ varrho=ϱ sigma=σ varsigma=ς tau=τ upsilon=υ phi=φ varphi=φ chi=χ psi=ψ omega=ω digamma=ϝ " +
    "Gamma=Γ Delta=Δ Theta=Θ Lambda=Λ Xi=Ξ Pi=Π Sigma=Σ Upsilon=Υ Phi=Φ Psi=Ψ Omega=Ω " +
    "infty=∞ partial=∂ nabla=∇ ell=ℓ hbar=ℏ emptyset=∅ varnothing=∅ prime=′ flat=♭ sharp=♯ natural=♮ top=⊤ bot=⊥ aleph=ℵ beth=ℶ wp=℘ Re=ℜ Im=ℑ " +
    "forall=∀ exists=∃ nexists=∄ neg=¬ lnot=¬ angle=∠ triangle=△ square=□ Box=□ Diamond=◇ dagger=† ddagger=‡ " +
    "cdots=⋯ ldots=… dots=… dotsc=… dotsb=⋯ vdots=⋮ ddots=⋱ backslash=\\ lvert=| rvert=| vert=| lVert=‖ rVert=‖ Vert=‖ surd=√ checkmark=✓ " +
    "imath=ı jmath=ȷ mho=℧ infin=∞ degree=° clubsuit=♣ heartsuit=♡ spadesuit=♠ diamondsuit=♢");
  texDef("open", "langle=⟨ lceil=⌈ lfloor=⌊ lbrace={ lbrack=[ lgroup=⟮");
  texDef("close", "rangle=⟩ rceil=⌉ rfloor=⌋ rbrace=} rbrack=] rgroup=⟯");
  texDef("punct", "colon=: cdotp=·");
  texDef("bin", "bullet=• circ=∘ star=⋆ ast=∗ cdot=· times=× div=÷ pm=± mp=∓ setminus=∖ smallsetminus=∖ cup=∪ cap=∩ sqcup=⊔ sqcap=⊓ uplus=⊎ " +
    "vee=∨ lor=∨ wedge=∧ land=∧ otimes=⊗ oplus=⊕ ominus=⊖ odot=⊙ oslash=⊘ triangleleft=◁ triangleright=▷ amalg=⨿ wr=≀ diamond=⋄");
  texDef("rel", "leq=≤ le=≤ geq=≥ ge=≥ leqslant=≤ geqslant=≥ leqq=≦ geqq=≧ neq=≠ ne=≠ approx=≈ approxeq=≊ asymp=≍ simeq=≃ cong=≅ sim=∼ equiv=≡ ll=≪ gg=≫ lll=⋘ ggg=⋙ " +
    "lesssim=≲ gtrsim=≳ prec=≺ succ=≻ preceq=⪯ succeq=⪰ propto=∝ in=∈ notin=∉ ni=∋ owns=∋ subset=⊂ supset=⊃ subseteq=⊆ supseteq=⊇ subsetneq=⊊ supsetneq=⊋ " +
    "sqsubseteq=⊑ sqsupseteq=⊒ sqsubset=⊏ sqsupset=⊐ mid=| nmid=∤ parallel=∥ nparallel=∦ perp=⊥ vdash=⊢ dashv=⊣ models=⊨ vDash=⊨ Vdash=⊩ " +
    "to=→ rightarrow=→ leftarrow=← gets=← leftrightarrow=↔ Rightarrow=⇒ Leftarrow=⇐ Leftrightarrow=⇔ longrightarrow=⟶ longleftarrow=⟵ " +
    "Longrightarrow=⟹ Longleftarrow=⟸ longleftrightarrow=⟷ Longleftrightarrow=⟺ iff=⟺ implies=⟹ impliedby=⟸ mapsto=↦ longmapsto=⟼ " +
    "hookrightarrow=↪ hookleftarrow=↩ twoheadrightarrow=↠ rightharpoonup=⇀ rightleftharpoons=⇌ uparrow=↑ downarrow=↓ Uparrow=⇑ Downarrow=⇓ updownarrow=↕ " +
    "nearrow=↗ searrow=↘ leadsto=⇝ rightsquigarrow=⇝ coloneqq=≔ coloneq=≔ eqqcolon=≕ doteq=≐ triangleq=≜ nleq=≰ ngeq=≱ nsim=≁ ncong=≇ nsubseteq=⊈ " +
    "lneq=⪇ gneq=⪈ bowtie=⋈ smile=⌣ frown=⌢ nless=≮ ngtr=≯ ne=≠");
  texDef("op", "sum=∑ prod=∏ coprod=∐ int=∫ iint=∬ iiint=∭ oint=∮ bigcup=⋃ bigcap=⋂ bigsqcup=⨆ bigoplus=⨁ bigotimes=⨂ bigodot=⨀ biguplus=⨄ bigwedge=⋀ bigvee=⋁");
  const TEX_NOLIMITS = new Set(["int", "iint", "iiint", "oint"]);
  const TEX_OPNAMES = new Set("log ln lg exp sin cos tan cot sec csc sinh cosh tanh coth arcsin arccos arctan arg deg det dim gcd lcm hom ker lim liminf limsup max min Pr sup inf injlim projlim Tr tr rank sgn".split(" "));
  const TEX_OPLIMITS = new Set("lim liminf limsup max min Pr sup inf det gcd injlim projlim".split(" "));
  const TEX_TEXTCMD = new Set("text textrm textup textnormal mbox hbox textit textbf textsf texttt emph textsc".split(" "));
  const TEX_FONTCMD = { mathrm: "rm", mathup: "rm", mathbf: "bf", boldsymbol: "bf", bm: "bf", mathbb: "bb", Bbb: "bb", mathcal: "cal", mathscr: "cal", mathfrak: "frak", mathit: "it", mathsf: "rm", mathtt: "rm", mathnormal: "it" };
  const TEX_ACCENT = { hat: "\u0302", widehat: "\u0302", tilde: "\u0303", widetilde: "\u0303", bar: "\u0304", overline: "\u0305", check: "\u030c", acute: "\u0301", grave: "\u0300", vec: "\u20d7", dot: "\u0307", ddot: "\u0308", breve: "\u0306", mathring: "\u030a", underline: "\u0332" };
  const TEX_ACCENT_MARK = { hat: "ˆ", widehat: "ˆ", tilde: "˜", widetilde: "˜", check: "ˇ", acute: "ˊ", grave: "ˋ", vec: "→", dot: "˙", ddot: "¨", breve: "˘", mathring: "˚" };
  const TEX_IGNORE = new Set("displaystyle textstyle scriptstyle scriptscriptstyle limits nolimits nonumber notag label hline vphantom phantom hphantom strut allowbreak".split(" "));
  const TEX_CHAR_CLS = { "+": "bin", "-": "bin", "−": "bin", "∗": "bin", "*": "bin", "·": "bin", "×": "bin", "±": "bin", "∪": "bin", "∩": "bin", "∘": "bin", "⊗": "bin", "⊕": "bin", "∖": "bin",
    "=": "rel", "<": "rel", ">": "rel", ":": "rel", "≤": "rel", "≥": "rel", "≠": "rel", "≈": "rel", "≡": "rel", "∈": "rel", "∉": "rel", "⊂": "rel", "⊆": "rel", "→": "rel", "←": "rel", "↦": "rel", "⇒": "rel", "⇔": "rel", "≍": "rel", "∼": "rel", "≪": "rel", "≫": "rel",
    ",": "punct", ";": "punct", "(": "open", "[": "open", ")": "close", "]": "close", "∑": "op", "∏": "op", "∫": "op" };
  // Unknown command names seen while parsing (read by tests; never shown).
  const TEX_UNKNOWN = new Set();

  function texTokenize(src) {
    const toks = [];
    const s = String(src == null ? "" : src);
    let i = 0;
    while (i < s.length) {
      const c = s[i];
      if (c === "\\") {
        const m = /^\\([A-Za-z]+)(\*?)/.exec(s.slice(i, i + 40));
        if (m) {
          toks.push({ t: "cmd", v: m[1], star: !!m[2] && /^(operatorname|begin|end)$/.test(m[1]) });
          i += m[1].length + 1 + (m[2] && /^(operatorname|begin|end)$/.test(m[1]) ? 1 : 0);
        } else if (i + 1 < s.length) {
          const cp = String.fromCodePoint(s.codePointAt(i + 1));
          toks.push({ t: "cmd", v: cp, sym: true });
          i += 1 + cp.length;
        } else { i++; }
        continue;
      }
      if (/\s/.test(c)) {
        while (i < s.length && /\s/.test(s[i])) i++;
        toks.push({ t: "sp" });
        continue;
      }
      if (c === "{" || c === "}" || c === "^" || c === "_" || c === "&" || c === "~") { toks.push({ t: c }); i++; continue; }
      const cp = String.fromCodePoint(s.codePointAt(i));
      toks.push({ t: "ch", v: cp });
      i += cp.length;
    }
    return toks;
  }

  function texChar(v, cls) {
    if (v === "-") v = "−";
    else if (v === "*") v = "∗";
    else if (v === "'") v = "′";
    return { t: "ch", v, cls: cls || TEX_CHAR_CLS[v] || "ord" };
  }

  function texParse(src) {
    const toks = texTokenize(src);
    let pos = 0;
    const peek = () => toks[pos];
    const skipSp = () => { while (pos < toks.length && toks[pos].t === "sp") pos++; };
    const isCmd = (tk, name) => tk && tk.t === "cmd" && tk.v === name;

    // Raw text of a braced group (for \text, \begin{env}, \color ...).
    function readRawGroup() {
      skipSp();
      if (!peek() || peek().t !== "{") {
        const tk = toks[pos++];
        return tk ? (tk.t === "ch" ? tk.v : "") : "";
      }
      pos++;
      let depth = 1;
      let out = "";
      while (pos < toks.length) {
        const tk = toks[pos++];
        if (tk.t === "{") { depth++; continue; }
        if (tk.t === "}") { if (--depth === 0) break; continue; }
        if (tk.t === "sp" || tk.t === "~") out += " ";
        else if (tk.t === "ch") out += tk.v;
        else if (tk.t === "cmd") {
          if (tk.sym) out += tk.v === "\\" ? " " : (tk.v === "," || tk.v === ";" || tk.v === " " ? " " : tk.v);
          else if (TEX_SYM[tk.v]) out += TEX_SYM[tk.v][0];
          else if (tk.v === "quad" || tk.v === "qquad") out += " ";
          else if (!TEX_IGNORE.has(tk.v)) out += tk.v;
        } else out += tk.t === "&" ? " " : tk.t;
      }
      return out;
    }
    function readOptional() {
      const save = pos;
      skipSp();
      const tk = peek();
      if (!tk || tk.t !== "ch" || tk.v !== "[") { pos = save; return null; }
      pos++;
      const out = [];
      while (pos < toks.length && !(toks[pos].t === "ch" && toks[pos].v === "]")) {
        const a = parseAtom();
        if (a) out.push(parseScripts(a));
      }
      pos++;
      return out;
    }
    function readDelim() {
      skipSp();
      const tk = toks[pos++];
      if (!tk) return "";
      if (tk.t === "ch") return tk.v === "." ? "" : tk.v;
      if (tk.t === "cmd") {
        if (tk.sym) return tk.v === "|" ? "‖" : tk.v;
        if (TEX_SYM[tk.v]) return TEX_SYM[tk.v][0];
      }
      return "";
    }
    function parseArg() {
      skipSp();
      const tk = peek();
      if (!tk) return [];
      if (tk.t === "{") {
        pos++;
        const list = parseList(new Set(["}"]));
        if (peek() && peek().t === "}") pos++;
        return list;
      }
      if (tk.t === "cmd") { const a = parseAtom(); return a ? [a] : []; }
      if (tk.t === "ch") { pos++; return [texChar(tk.v)]; }
      return [];
    }
    function parseRows(stopEnd) {
      const rows = [[[]]];
      const stops = new Set(["&", "nl", stopEnd ? "end" : "}"]);
      for (;;) {
        const cells = rows[rows.length - 1];
        cells[cells.length - 1].push(...parseList(stops));
        const tk = peek();
        if (!tk) break;
        if (tk.t === "&") { pos++; cells.push([]); continue; }
        if (isCmd(tk, "\\")) { pos++; readOptional(); rows.push([[]]); continue; }
        break;
      }
      // Drop a trailing empty row left by a final "\\".
      const last = rows[rows.length - 1];
      if (rows.length > 1 && last.length === 1 && !last[0].some((n) => n.t !== "sp")) rows.pop();
      return rows;
    }
    function parseScripts(base) {
      let node = base;
      for (;;) {
        const save = pos;
        skipSp();
        const tk = peek();
        if (!tk || (tk.t !== "^" && tk.t !== "_")) { pos = save; break; }
        pos++;
        const arg = parseArg();
        if (node.t !== "scr") node = { t: "scr", base: node, sup: null, sub: null };
        const key = tk.t === "^" ? "sup" : "sub";
        node[key] = node[key] ? node[key].concat(arg) : arg;
      }
      return node;
    }
    function parseList(stops) {
      const out = [];
      while (pos < toks.length) {
        const tk = peek();
        if (tk.t === "}") { if (stops.has("}")) break; pos++; continue; }
        if (tk.t === "&") { if (stops.has("&")) break; pos++; out.push({ t: "space", v: " " }); continue; }
        if (isCmd(tk, "\\")) { if (stops.has("nl")) break; pos++; readOptional(); out.push({ t: "br" }); continue; }
        if (isCmd(tk, "end")) { if (stops.has("end")) break; pos++; readRawGroup(); continue; }
        if (isCmd(tk, "right") && stops.has("right")) break;
        const a = parseAtom();
        if (a) out.push(a.t === "sp" ? a : parseScripts(a));
      }
      return out;
    }
    function parseAtom() {
      const tk = toks[pos];
      if (!tk) return null;
      if (tk.t === "sp") { pos++; return { t: "sp" }; }
      if (tk.t === "{") {
        pos++;
        const kids = parseList(new Set(["}"]));
        if (peek() && peek().t === "}") pos++;
        return { t: "grp", kids };
      }
      if (tk.t === "^" || tk.t === "_") return { t: "grp", kids: [] };
      if (tk.t === "~") { pos++; return { t: "space", v: "\u00a0" }; }
      if (tk.t === "ch") { pos++; return texChar(tk.v); }
      if (tk.t !== "cmd") { pos++; return null; }
      pos++;
      return parseCommand(tk);
    }
    function parseCommand(tk) {
      const name = tk.v;
      if (tk.sym) {
        switch (name) {
          case "{": return texChar("{", "open");
          case "}": return texChar("}", "close");
          case "|": return texChar("‖", "ord");
          case ",": return { t: "space", v: "\u2009" };
          case ":": case ">": return { t: "space", v: "\u2005" };
          case ";": return { t: "space", v: "\u2004" };
          case "!": return { t: "space", v: "" };
          case " ": return { t: "space", v: " " };
          case "\\": return { t: "br" };
          default: return texChar(name, "ord");
        }
      }
      if (TEX_SYM[name]) {
        const [v, cls] = TEX_SYM[name];
        return cls === "op" ? { t: "ch", v, cls: "op", big: true, limits: !TEX_NOLIMITS.has(name) } : { t: "ch", v, cls };
      }
      if (TEX_OPNAMES.has(name)) return { t: "opname", kids: [{ t: "text", v: name }], limits: TEX_OPLIMITS.has(name) };
      if (name === "varprojlim" || name === "varinjlim") {
        return { t: "under", body: [{ t: "opname", kids: [{ t: "text", v: "lim" }], limits: true }], bot: [texChar(name === "varprojlim" ? "←" : "→", "ord")], cls: "op" };
      }
      if (name === "operatorname") return { t: "opname", kids: parseArg(), limits: !!tk.star };
      if (TEX_TEXTCMD.has(name)) return { t: "text", v: readRawGroup(), font: name === "textbf" ? "bf" : (name === "textit" || name === "emph" ? "it" : (name === "texttt" ? "tt" : "")) };
      if (TEX_FONTCMD[name]) return { t: "font", font: TEX_FONTCMD[name], kids: parseArg() };
      if (TEX_ACCENT[name]) return { t: "acc", kind: name, body: parseArg() };
      if (TEX_IGNORE.has(name)) {
        if (/phantom|label/.test(name)) parseArg();
        return null;
      }
      switch (name) {
        case "frac": case "tfrac": case "dfrac": case "cfrac": {
          const num = parseArg();
          const den = parseArg();
          return { t: "frac", num, den, style: name === "tfrac" ? "t" : (name === "dfrac" || name === "cfrac" ? "d" : "") };
        }
        case "binom": case "tbinom": case "dbinom": case "choose": {
          const top = parseArg();
          const bot = parseArg();
          return { t: "frac", num: top, den: bot, binom: true, style: name === "tbinom" ? "t" : (name === "dbinom" ? "d" : "") };
        }
        case "sqrt": {
          const idx = readOptional();
          return { t: "sqrt", idx, body: parseArg() };
        }
        case "overset": case "stackrel": { const top = parseArg(); const body = parseArg(); return { t: "over", top, body }; }
        case "underset": { const bot = parseArg(); const body = parseArg(); return { t: "under", bot, body }; }
        case "xrightarrow": case "xleftarrow": case "xmapsto": case "xLeftarrow": case "xRightarrow": {
          const below = readOptional();
          const top = parseArg();
          const arrow = { xrightarrow: "⟶", xleftarrow: "⟵", xmapsto: "⟼", xLeftarrow: "⟸", xRightarrow: "⟹" }[name];
          const over = { t: "over", top, body: [texChar(arrow, "ord")], cls: "rel" };
          return below && below.length ? { t: "under", bot: below, body: [over], cls: "rel" } : over;
        }
        case "underbrace": case "overbrace": return { t: "brace", dir: name === "underbrace" ? "under" : "over", body: parseArg() };
        case "substack": {
          skipSp();
          if (peek() && peek().t === "{") {
            pos++;
            const rows = parseRows(false);
            if (peek() && peek().t === "}") pos++;
            return { t: "stack", rows: rows.map((r) => [].concat(...r.map((c, k) => (k ? [{ t: "space", v: " " }] : []).concat(c)))) };
          }
          return { t: "grp", kids: parseArg() };
        }
        case "begin": {
          const env = readRawGroup().trim();
          if (/^(array|alignedat|alignat\*?|tabular)$/.test(env)) readRawGroup();
          const rows = parseRows(true);
          if (isCmd(peek(), "end")) { pos++; readRawGroup(); }
          return { t: "env", env, rows };
        }
        case "left": {
          const open = readDelim();
          const body = parseList(new Set(["right", "}"]));
          let close = "";
          if (isCmd(peek(), "right")) { pos++; close = readDelim(); }
          return { t: "lr", open, close, body };
        }
        case "right": return texChar(readDelim(), "close");
        case "middle": return texChar(readDelim(), "rel");
        case "bigl": case "Bigl": case "biggl": case "Biggl":
          return { t: "ch", v: readDelim(), cls: "open", size: /^bigg/i.test(name) ? 3 : (name[0] === "B" ? 2 : 1) };
        case "bigr": case "Bigr": case "biggr": case "Biggr":
          return { t: "ch", v: readDelim(), cls: "close", size: /^bigg/i.test(name) ? 3 : (name[0] === "B" ? 2 : 1) };
        case "bigm": case "Bigm": case "biggm": case "Biggm":
          return { t: "ch", v: readDelim(), cls: "rel", size: /^bigg/i.test(name) ? 3 : (name[0] === "B" ? 2 : 1) };
        case "big": case "Big": case "bigg": case "Bigg":
          return { t: "ch", v: readDelim(), cls: "ord", size: /^bigg/i.test(name) ? 3 : (name[0] === "B" ? 2 : 1) };
        case "quad": return { t: "space", v: "\u2003" };
        case "qquad": return { t: "space", v: "\u2003\u2003" };
        case "enspace": case "enskip": return { t: "space", v: "\u2002" };
        case "thinspace": return { t: "space", v: "\u2009" };
        case "medspace": return { t: "space", v: "\u2005" };
        case "thickspace": return { t: "space", v: "\u2004" };
        case "negthinspace": case "negmedspace": case "negthickspace": return { t: "space", v: "" };
        case "hspace": case "hskip": case "kern": case "mkern": readRawGroup(); return { t: "space", v: " " };
        case "pmod": { const arg = parseArg(); return { t: "grp", kids: [{ t: "space", v: "\u2003" }, texChar("(", "open"), { t: "opname", kids: [{ t: "text", v: "mod" }] }, { t: "space", v: "\u2009" }].concat(arg, [texChar(")", "close")]) }; }
        case "bmod": case "mod": return { t: "opname", kids: [{ t: "text", v: "mod" }], cls: "bin" };
        case "not": {
          const nx = parseAtom();
          if (nx && nx.t === "ch") {
            const neg = { "=": "≠", "<": "≮", ">": "≯", "≤": "≰", "≥": "≱", "∈": "∉", "⊆": "⊈", "⊂": "⊄", "∼": "≁", "≡": "≢", "|": "∤" }[nx.v];
            return { t: "ch", v: neg || nx.v + "\u0338", cls: nx.cls };
          }
          return nx;
        }
        case "color": readRawGroup(); return null;
        case "textcolor": case "colorbox": readRawGroup(); return { t: "grp", kids: parseArg() };
        case "boxed": case "fbox": return { t: "grp", kids: parseArg() };
        case "tag": return { t: "text", v: "\u2003(" + readRawGroup() + ")" };
        case "dagger": return texChar("†", "ord");
        default:
          TEX_UNKNOWN.add(name);
          return { t: "text", v: name, unknown: true };
      }
    }

    const out = [];
    while (pos < toks.length) {
      out.push(...parseList(new Set()));
      if (pos < toks.length) pos++;
    }
    return out;
  }

  // ---- Element tree: { tag, c (class), k (children) } or plain strings ----
  const texEl = (tag, c, k) => ({ tag, c, k: k || [] });
  const TEX_THIN = "\u2009";

  function texIsSimple(nodes) {
    const list = nodes.filter((n) => n.t !== "sp");
    if (!list.length || list.length > 3) return false;
    return list.every((n) => (n.t === "ch" && n.cls === "ord") || (n.t === "text" && n.v.length <= 3));
  }
  function texIsTall(nodes) {
    return nodes.some((n) => n.t === "frac" || n.t === "env" || n.t === "stack" || (n.t === "scr" && (texIsTall([n.base]) || (n.base && n.base.big))) || (n.t === "lr" && texIsTall(n.body)) || (n.t === "grp" && texIsTall(n.kids)));
  }
  function texGap(prev, cur, ctx) {
    if (!prev || prev === "space" || cur === "space") return "";
    if (ctx.script) return (prev === "punct") ? TEX_THIN : "";
    if (prev === "rel" || cur === "rel") return prev === cur ? "" : (prev === "open" || cur === "close" || cur === "punct" ? "" : " ");
    if (prev === "bin" || cur === "bin") return " ";
    if (prev === "punct") return TEX_THIN;
    if ((prev === "op" && (cur === "ord" || cur === "op" || cur === "inner")) || (cur === "op" && (prev === "ord" || prev === "close" || prev === "inner"))) return TEX_THIN;
    if ((prev === "inner" && (cur === "ord" || cur === "inner" || cur === "open")) || (cur === "inner" && (prev === "ord" || prev === "close"))) return ctx.display ? TEX_THIN : "";
    return "";
  }
  function texBuild(nodes, ctx) {
    const items = [];
    for (const n of nodes) {
      if (n.t === "sp") continue;
      const it = texBuildNode(n, ctx);
      if (it) items.push(it);
    }
    const out = [];
    let prev = null;
    items.forEach((it, idx) => {
      let cls = it.cls;
      if (cls === "bin" && (!prev || prev === "bin" || prev === "rel" || prev === "open" || prev === "punct" || prev === "op" || idx === items.length - 1)) cls = "ord";
      if (!prev && ctx.lead && (cls === "rel" || cls === "bin")) out.push(" ");
      const gap = texGap(prev, cls, ctx);
      if (gap) out.push(gap);
      out.push(...it.out);
      prev = cls;
    });
    return out;
  }
  function texScripts(base, sup, sub, ctx) {
    const sctx = Object.assign({}, ctx, { script: true, lead: false });
    const supT = sup ? texBuild(sup, sctx) : null;
    const subT = sub ? texBuild(sub, sctx) : null;
    if (supT && subT) return base.concat([texEl("span", "tx-ss", [texEl("sup", "", supT), texEl("sub", "", subT)])]);
    if (supT) return base.concat([texEl("sup", "", supT)]);
    if (subT) return base.concat([texEl("sub", "", subT)]);
    return base;
  }
  function texBuildNode(n, ctx) {
    switch (n.t) {
      case "ch": {
        if (!n.v) return { cls: n.cls, out: [] };
        return { cls: n.cls, out: [n.size ? texEl("span", "tx-d" + n.size, [n.v]) : (n.big && ctx.display && !ctx.script ? texEl("span", "tx-bigop", [n.v]) : n.v)] };
      }
      case "space": return { cls: "space", out: n.v ? [n.v] : [] };
      case "br": return { cls: "space", out: [ctx.display ? texEl("span", "tx-br") : " "] };
      case "text": {
        const v = n.v;
        if (n.unknown) return { cls: "ord", out: [texEl("span", "tx-rm", [v])] };
        return { cls: "ord", out: [texEl(n.font === "bf" ? "b" : "span", n.font === "it" ? "tx-it" : (n.font === "tt" ? "tx-tt" : "tx-text"), [v])] };
      }
      case "grp": return { cls: n.kids.length === 1 && n.kids[0].t === "ch" ? n.kids[0].cls : "ord", out: texBuild(n.kids, Object.assign({}, ctx, { lead: false })) };
      case "font": {
        if (n.font === "bb" || n.font === "cal" || n.font === "frak") {
          const map = (list) => list.map((k) => (k.t === "ch" ? Object.assign({}, k, { v: Array.from(k.v).map((c) => texFontChar(n.font, c)).join("") }) : (k.t === "grp" ? Object.assign({}, k, { kids: map(k.kids) }) : k)));
          return { cls: "ord", out: texBuild(map(n.kids), ctx) };
        }
        const inner = texBuild(n.kids, Object.assign({}, ctx, { lead: false }));
        return { cls: "ord", out: [texEl(n.font === "bf" ? "b" : "span", n.font === "bf" ? "tx-bf" : (n.font === "it" ? "tx-it" : "tx-rm"), inner)] };
      }
      case "opname": {
        const inner = texBuild(n.kids, Object.assign({}, ctx, { lead: false }));
        return { cls: n.cls || "op", out: [texEl("span", "tx-op", inner)], opname: true };
      }
      case "scr": {
        const b = n.base;
        if (b && b.t === "brace") {
          const label = b.dir === "under" ? n.sub : n.sup;
          const rest = b.dir === "under" ? n.sup : n.sub;
          const body = texBuild(b.body, ctx);
          const lab = label ? texBuild(label, Object.assign({}, ctx, { script: true, lead: false })) : [];
          const box = b.dir === "under"
            ? texEl("span", "tx-v3", [texEl("span", "tx-v3-pad"), texEl("span", "tx-ub", body), texEl("span", "tx-v3-lo", lab)])
            : texEl("span", "tx-v3", [texEl("span", "tx-v3-hi", lab), texEl("span", "tx-ob", body), texEl("span", "tx-v3-pad")]);
          return { cls: "ord", out: texScripts([box], b.dir === "under" ? rest : null, b.dir === "under" ? null : rest, ctx) };
        }
        const baseIt = b ? texBuildNode(b, ctx) : { cls: "ord", out: [] };
        const limits = b && ctx.display && !ctx.script && ((b.t === "ch" && b.big && b.limits) || (b.t === "opname" && b.limits));
        if (limits) {
          const sctx = Object.assign({}, ctx, { script: true, lead: false });
          return {
            cls: "op",
            out: [texEl("span", "tx-v3 tx-lim", [
              texEl("span", "tx-v3-hi", n.sup ? texBuild(n.sup, sctx) : []),
              texEl("span", "tx-lim-op", baseIt.out),
              texEl("span", "tx-v3-lo", n.sub ? texBuild(n.sub, sctx) : [])
            ])]
          };
        }
        return { cls: baseIt.cls === "bin" || baseIt.cls === "rel" ? baseIt.cls : (baseIt.cls === "op" ? "op" : (baseIt.cls === "inner" ? "inner" : "ord")), out: texScripts(baseIt.out, n.sup, n.sub, ctx) };
      }
      case "frac": {
        const display = n.style === "d" || (ctx.display && n.style !== "t" && !ctx.script);
        if (!n.binom && !display && texIsSimple(n.num) && texIsSimple(n.den)) {
          const fctx = Object.assign({}, ctx, { lead: false });
          return { cls: "ord", out: texBuild(n.num, fctx).concat(["/"], texBuild(n.den, fctx)) };
        }
        const pctx = Object.assign({}, ctx, { display, script: !display || ctx.script, lead: false });
        const frac = texEl("span", "tx-frac" + (display ? "" : " tx-frac-t") + (n.binom ? " tx-nobar" : ""), [
          texEl("span", "tx-num", texBuild(n.num, pctx)),
          texEl("span", "tx-sr", [n.binom ? "," : "/"]),
          texEl("span", "tx-den", texBuild(n.den, pctx))
        ]);
        return { cls: "inner", out: n.binom ? [texEl("span", "tx-d2", ["("]), frac, texEl("span", "tx-d2", [")"])] : [frac] };
      }
      case "sqrt": {
        const out = [];
        if (n.idx && n.idx.length) out.push(texEl("sup", "tx-root", texBuild(n.idx, Object.assign({}, ctx, { script: true }))));
        out.push("√", texEl("span", "tx-sqrt", texBuild(n.body, Object.assign({}, ctx, { lead: false }))));
        return { cls: "ord", out };
      }
      case "acc": {
        const body = n.body.filter((k) => k.t !== "sp");
        const single = body.length === 1 && body[0].t === "ch" && Array.from(body[0].v).length === 1;
        if (single && n.kind !== "underline") return { cls: "ord", out: [body[0].v + TEX_ACCENT[n.kind]] };
        const inner = texBuild(body, Object.assign({}, ctx, { lead: false }));
        if (n.kind === "overline" || n.kind === "bar") return { cls: "ord", out: [texEl("span", "tx-ovl", inner)] };
        if (n.kind === "underline") return { cls: "ord", out: [texEl("span", "tx-unl", inner)] };
        return { cls: "ord", out: [texEl("span", "tx-v3 tx-acc", [texEl("span", "tx-v3-hi tx-acc-mark", [TEX_ACCENT_MARK[n.kind] || ""]), texEl("span", "", inner), texEl("span", "tx-v3-pad")])] };
      }
      case "over": case "under": {
        const sctx = Object.assign({}, ctx, { script: true, lead: false });
        const body = texBuild(n.body, Object.assign({}, ctx, { lead: false }));
        const lab = texBuild(n.t === "over" ? n.top : n.bot, sctx);
        const kids = n.t === "over"
          ? [texEl("span", "tx-v3-hi", lab), texEl("span", "", body), texEl("span", "tx-v3-pad")]
          : [texEl("span", "tx-v3-pad"), texEl("span", "", body), texEl("span", "tx-v3-lo", lab)];
        return { cls: n.cls || "ord", out: [texEl("span", "tx-v3", kids)] };
      }
      case "brace": {
        const body = texBuild(n.body, ctx);
        return { cls: "ord", out: [texEl("span", n.dir === "under" ? "tx-ub" : "tx-ob", body)] };
      }
      case "stack": {
        const rctx = Object.assign({}, ctx, { lead: false });
        return { cls: "ord", out: [texEl("span", "tx-stack", n.rows.map((r) => texEl("span", "tx-stack-row", texBuild(r, rctx))))] };
      }
      case "env": {
        const env = n.env.replace(/\*$/, "");
        const aligned = /^(aligned|align|alignat|alignedat|split|eqnarray|flalign)$/.test(env);
        const cases = /^(cases|dcases|rcases)$/.test(env);
        const rows = n.rows.map((r) => texEl("span", "tx-tr", r.map((cell, ci) => texEl("span", "tx-td" + (aligned ? (ci % 2 ? " tx-al" : " tx-ar") : (cases ? " tx-al" : "")),
          texBuild(cell, Object.assign({}, ctx, { display: true, lead: aligned && ci % 2 === 1 }))))));
        const table = texEl("span", "tx-table" + (aligned ? " tx-aligned" : (cases ? " tx-cases-t" : " tx-matrix")), rows);
        const delims = { pmatrix: ["(", ")"], bmatrix: ["[", "]"], Bmatrix: ["{", "}"], vmatrix: ["|", "|"], Vmatrix: ["‖", "‖"], cases: ["{", ""], dcases: ["{", ""], rcases: ["", "}"] }[env];
        const out = [];
        const dcls = "tx-env-delim tx-rows" + Math.min(Math.max(n.rows.length, 1), 4);
        if (delims && delims[0]) out.push(texEl("span", dcls, [delims[0]]));
        out.push(table);
        if (delims && delims[1]) out.push(texEl("span", dcls, [delims[1]]));
        return { cls: "inner", out };
      }
      case "lr": {
        const tall = texIsTall(n.body);
        const body = texBuild(n.body, Object.assign({}, ctx, { lead: false }));
        const d = (v) => (v ? [tall ? texEl("span", ctx.display && !ctx.script ? "tx-d3" : "tx-d2", [v]) : v] : []);
        return { cls: "inner", out: d(n.open).concat(body, d(n.close)) };
      }
      default: return null;
    }
  }

  // Plain Unicode text from a node list (titles, cards, crumbs, search).
  const SUP_MAP = { "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹", "+": "⁺", "-": "⁻", "−": "⁻", "=": "⁼", "(": "⁽", ")": "⁾", n: "ⁿ", i: "ⁱ", k: "ᵏ", s: "ˢ", "*": "*", "∗": "*", "∨": "ᵛ", "′": "′" };
  const SUB_MAP = { "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄", "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉", "+": "₊", "-": "₋", "−": "₋", "=": "₌", "(": "₍", ")": "₎", a: "ₐ", e: "ₑ", o: "ₒ", x: "ₓ", i: "ᵢ", j: "ⱼ", k: "ₖ", n: "ₙ", m: "ₘ", p: "ₚ", s: "ₛ", t: "ₜ", r: "ᵣ" };
  const toScript = (txt, map, mark) => {
    const chars = Array.from(txt);
    return chars.length && chars.every((c) => map[c]) ? chars.map((c) => map[c]).join("") : mark + (chars.length > 1 ? "(" + txt + ")" : txt);
  };
  function texPlain(nodes) {
    let s = "";
    nodes.forEach((n, idx) => {
      const nx = nodes[idx + 1];
      switch (n.t) {
        case "sp": s += " "; break;
        case "ch": s += n.v; break;
        case "space": case "br": s += n.v ? " " : (n.t === "br" ? " " : ""); break;
        case "text": s += n.v; break;
        case "grp": s += texPlain(n.kids); break;
        case "font": {
          if (n.font === "bb" || n.font === "cal" || n.font === "frak") s += Array.from(texPlain(n.kids)).map((c) => (n.font === "bb" && TEX_BB[c]) || texFontChar(n.font, c)).join("");
          else s += texPlain(n.kids);
          break;
        }
        case "opname": s += (/[\p{L}\p{N})]$/u.test(s) ? "\u2009" : "") + texPlain(n.kids) + (nx && ((nx.t === "ch" && /^[\p{L}\p{N}]/u.test(nx.v)) || nx.t === "font" || nx.t === "opname") ? "\u2009" : ""); break;
        case "scr": {
          const base = n.base ? texPlain([n.base]) : "";
          s += base;
          if (n.sub) s += toScript(texPlain(n.sub).trim(), SUB_MAP, "_");
          if (n.sup) s += toScript(texPlain(n.sup).trim(), SUP_MAP, "^");
          break;
        }
        case "frac": {
          const a = texPlain(n.num).trim();
          const b = texPlain(n.den).trim();
          const wrap = (t) => (/^[\p{L}\p{N}′.]+$/u.test(t) ? t : "(" + t + ")");
          s += n.binom ? "C(" + a + ", " + b + ")" : wrap(a) + "/" + wrap(b);
          break;
        }
        case "sqrt": { const b = texPlain(n.body).trim(); s += "√" + (/^[\p{L}\p{N}]$/u.test(b) ? b : "(" + b + ")"); break; }
        case "acc": {
          const b = texPlain(n.body).trim();
          s += Array.from(b).length === 1 ? b + TEX_ACCENT[n.kind] : (n.kind === "overline" || n.kind === "bar" ? Array.from(b).map((c) => c + "\u0305").join("") : b);
          break;
        }
        case "over": s += texPlain(n.body); break;
        case "under": s += texPlain(n.body); break;
        case "brace": s += texPlain(n.body); break;
        case "stack": s += n.rows.map((r) => texPlain(r).trim()).join(", "); break;
        case "env": s += " " + n.rows.map((r) => r.map((c) => texPlain(c).trim()).join(" ")).join("; ") + " "; break;
        case "lr": s += n.open + texPlain(n.body) + n.close; break;
        default: break;
      }
    });
    return s;
  }
  // TeX fragment -> plain Unicode text.
  function texToPlain(tex) {
    return texPlain(texParse(tex)).replace(/\s+/g, " ").trim();
  }

  // Element tree -> escaped HTML string / DOM nodes.
  function texTreeHtml(items) {
    return items.map((it) => (typeof it === "string" ? escapeHtml(it)
      : "<" + it.tag + (it.c ? ' class="' + it.c + '"' : "") + ">" + texTreeHtml(it.k) + "</" + it.tag + ">")).join("");
  }
  function texTreeDom(items, parent) {
    items.forEach((it) => {
      if (typeof it === "string") { parent.appendChild(document.createTextNode(it)); return; }
      const node = document.createElement(it.tag);
      if (it.c) node.className = it.c;
      texTreeDom(it.k, node);
      parent.appendChild(node);
    });
    return parent;
  }
  function texTree(tex, display) {
    return texBuild(texParse(tex), { display: !!display, script: false, lead: false });
  }
  // TeX source -> escaped HTML (no wrapper element).
  function texToHtml(tex, display) {
    return texTreeHtml(texTree(tex, display));
  }

  // Inline math is $...$ with no space just inside the dollars and no digit
  // right after the closing one, so prices such as "$5 and $10" stay text.
  const INLINE_MATH_RX = /\$(?!\$)(?=\S)((?:\\.|[^$\\\n]){1,400}?)(?<=[^\s\\])\$(?![\d$])/g;
  // Display math $$...$$ written inside a paragraph, list item or table cell.
  const DISPLAY_MATH_RX = /\$\$((?:\\.|[^$\\]){1,6000}?)\$\$/g;

  function plainTextFromTex(text) {
    return String(text == null ? "" : text)
      .replace(DISPLAY_MATH_RX, (_, t) => texToPlain(t))
      .replace(INLINE_MATH_RX, (_, t) => texToPlain(t));
  }

  // TeX fragment -> DOM math span built only with createElement/textContent.
  function renderTexSafe(tex, display) {
    const span = document.createElement("span");
    span.className = display ? "math-block math-display" : "math-inline";
    return texTreeDom(texTree(tex, display), span);
  }

  // Text with $...$ segments -> DOM fragment (plain text + math spans).
  function renderTextWithTex(text) {
    const frag = document.createDocumentFragment();
    const src = String(text == null ? "" : text);
    let last = 0;
    INLINE_MATH_RX.lastIndex = 0;
    let m;
    while ((m = INLINE_MATH_RX.exec(src))) {
      if (m.index > last) frag.appendChild(document.createTextNode(src.slice(last, m.index)));
      frag.appendChild(renderTexSafe(m[1]));
      last = INLINE_MATH_RX.lastIndex;
    }
    if (last < src.length) frag.appendChild(document.createTextNode(src.slice(last)));
    return frag;
  }

  // HTML-escaped TeX (Markdown path) -> HTML string. The source is unescaped,
  // parsed, and every text run is escaped again on output.
  function unescapeHtmlEntities(s) {
    return String(s == null ? "" : s).replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&quot;/g, "\"").replace(/&#39;/g, "'").replace(/&amp;/g, "&");
  }
  function prettifyMath(escapedTex, display) {
    return texToHtml(unescapeHtmlEntities(escapedTex), display);
  }
  // ---- TeX engine end ----

  function rewriteDocHref(rawHref, sourceContext) {
    const href = String(rawHref || "").trim();
    if (!href) return null;
    if (/^https?:\/\//i.test(href)) return { href, external: true };
    if (href.startsWith("#")) {
      // "#some-heading" points inside the current document; app routes
      // ("#item/...", "#findings/...") pass through unchanged.
      if (!DOC_ROUTE_RX.test(href) && href.length > 1) {
        const anchor = docAnchorSlug(href.slice(1));
        if (anchor) return { href: "#" + anchor, external: false, anchor };
      }
      return { href, external: false };
    }
    const safe = safeHref(href);
    if (!safe) return null;

    // Rewrite relative markdown paths to SPA routes (keeping any #section).
    const hashIdx = safe.indexOf("#");
    const sec = hashIdx >= 0 ? docAnchorSlug(safe.slice(hashIdx + 1)) : "";
    const withSec = (route) => ({ href: route + (sec ? "?sec=" + encodeURIComponent(sec) : ""), external: false });
    const clean = safe.split("#")[0].replace(/^\.\//, "");
    const mFind = clean.match(/(?:^|\/)findings\/([A-Za-z0-9_.-]+)\.md$/);
    if (mFind) return withSec("#findings/" + encodeURIComponent(mFind[1]));
    const mAn = clean.match(/(?:^|\/)analysis\/([A-Za-z0-9_.-]+)\.md$/);
    if (mAn) {
      if (mAn[1].toLowerCase() === "readme") return { href: "#dossiers", external: false };
      return withSec("#dossiers/" + encodeURIComponent(mAn[1]));
    }
    const mRes = clean.match(/(?:^|\/)research\/([A-Za-z0-9_.-]+)\.md$/);
    if (mRes) return withSec("#dossiers/research/" + encodeURIComponent(mRes[1]));
    const mBare = clean.match(/^([A-Za-z0-9_.-]+)\.md$/);
    if (mBare) {
      const slug = mBare[1];
      if (slug.toLowerCase() === "readme") {
        return { href: sourceContext === "findings" ? "#findings" : "#dossiers", external: false };
      }
      if (sourceContext === "findings") return withSec("#findings/" + encodeURIComponent(slug));
      if (sourceContext === "research") return withSec("#dossiers/research/" + encodeURIComponent(slug));
      return withSec("#dossiers/" + encodeURIComponent(slug));
    }
    return { href: safe, external: false };
  }

  // Hash targets that are app routes rather than in-document anchors.
  const DOC_ROUTE_RX = /^#(overview|circuit|findings|dossiers|blueprints|flirt|atlas|xrefs|portability|benchmarks|search|experiments|item|projects|selftest)(?=[/?=]|$)/;

  // GitHub-style heading slug: lower case, punctuation dropped, spaces to "-".
  function docAnchorSlug(text) {
    let s = String(text == null ? "" : text);
    try { s = decodeURIComponent(s); } catch (_) { /* keep raw */ }
    s = s.toLowerCase().trim();
    return s.replace(/[^\p{L}\p{N}\s_-]+/gu, "").replace(/\s/g, "-").slice(0, 80);
  }

  // Plain text of a Markdown heading line (links, code, emphasis and math removed).
  function headingPlainText(md) {
    return plainTextFromTex(String(md || "")
      .replace(/\[([^\]]+)\]\([^)]*\)/g, "$1")
      .replace(/[`*_]/g, "")
      .replace(/<[^>]*>/g, ""));
  }

  // Evidence tags used in findings and dossiers. One map, used for every tooltip.
  const EV_TAG_MEANING = {
    K: "Kernel-graph fact, computed from the kernel export",
    L: "Checked directly in the pinned Lean sources or the kernel database",
    S: "Standard mathematics or Lean and Mathlib semantics",
    M: "Structural reading or heuristic inference, not a checked fact"
  };
  function evTagHtml(t) {
    return '<abbr class="ev-tag ' + t + '" title="' + escapeHtml(EV_TAG_MEANING[t] || "") + '">[' + t + "]</abbr>";
  }

  // Display-only copy fixes for rendered documents: US spelling and "≠".
  // Code and preformatted text are left exactly as written.
  function usSpelling(text) {
    return String(text == null ? "" : text)
      .replace(/\b([Cc])atalogue(s?)\b/g, "$1atalog$2")
      .replace(/\b([Rr])ealis(e|ed|es|ing|ation|ations)\b/g, "$1ealiz$2")
      .replace(/\b([Nn])ormalis(e|ed|es|ing|ation)\b/g, "$1ormaliz$2")
      .replace(/\b([Ss])ymmetris(e|ed|es|ing)\b/g, "$1ymmetriz$2");
  }
  function polishDocText(root) {
    if (!root) return;
    const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
    const edits = [];
    for (let n = walker.nextNode(); n; n = walker.nextNode()) {
      if (n.parentElement && n.parentElement.closest("code, pre, kbd, samp")) continue;
      const t = usSpelling(n.nodeValue).replace(/(\s)!=(?=\s)/g, "$1≠");
      if (t !== n.nodeValue) edits.push([n, t]);
    }
    edits.forEach(([n, t]) => { n.nodeValue = t; });
  }

  function renderInlineSafe(rawText, sourceContext) {
    // 1. Escape ALL HTML first so zero untrusted tags survive!
    let s = escapeHtml(rawText);

    // 2. Protect inline code spans
    const placeholders = [];
    const hold = (htmlStr) => {
      const id = "\u0000H" + placeholders.length + "\u0000";
      placeholders.push(htmlStr);
      return id;
    };

    // A code span holding only an evidence tag (`[L]`) renders as the tag.
    s = s.replace(/`([^`\n]+)`/g, (_, code) => hold(/^\[[KLSM]\]$/.test(code) ? evTagHtml(code.charAt(1)) : "<code>" + code + "</code>"));

    // 3. Display math $$...$$ inside a paragraph, list item, quote or table
    //    cell, then inline LaTeX $...$ (avoid matching currency like $5 and $10)
    s = s.replace(DISPLAY_MATH_RX, (m, tex) => hold('<span class="math-block math-display">' + prettifyMath(tex, true) + "</span>"));
    s = s.replace(INLINE_MATH_RX, (m, tex) => hold('<span class="math-inline">' + prettifyMath(tex) + "</span>"));

    // 4. Markdown links [label](url) — label may contain placeholder code spans
    s = s.replace(/\[([^\]]+)\]\(([^)\s]+)\)/g, (_, label, urlEsc) => {
      const decodedUrl = urlEsc.replace(/&amp;/g, "&");
      const rw = rewriteDocHref(decodedUrl, sourceContext);
      if (!rw) return label;
      const attrs = rw.external
        ? 'href="' + escapeHtml(rw.href) + '" target="_blank" rel="noopener noreferrer"'
        : 'href="' + escapeHtml(rw.href) + '"' + (rw.anchor ? ' data-doc-anchor="' + escapeHtml(rw.anchor) + '"' : "");
      return hold("<a " + attrs + ">" + label + "</a>");
    });

    // 5. Bold and italic
    s = s.replace(/\*\*([^*\n]+)\*\*/g, "<strong>$1</strong>");
    s = s.replace(/(^|[\s(])\*([^*\n]+)\*(?=[\s).,;:!?]|$)/g, "$1<em>$2</em>");

    // 6. Evidence tags [K], [S], [L], [M]
    s = s.replace(/\[([KLSM])\]/g, (_, t) => evTagHtml(t));

    // 7. Restore placeholders (nested links containing inline code expand cleanly)
    for (let pass = 0; pass < 3; pass++) {
      s = s.replace(/\u0000H(\d+)\u0000/g, (_, idx) => placeholders[Number(idx)] || "");
    }
    return s;
  }

  // Where a document's local reproduction commands live on GitHub.
  function verifyLocallyHref(docPath) {
    const p = String(docPath || "");
    if (!state.base && /^(findings|analysis|research)\/[A-Za-z0-9_.-]+\.md$/.test(p)) return "https://github.com/bohemian-miser/leanre/blob/main/" + p;
    return "https://github.com/bohemian-miser/leanre#reproducing-the-audit";
  }

  function renderMarkdownBlockSafe(md, sourceContext, docPath, ctx) {
    // ctx carries heading ids across nested blocks so each id is unique.
    ctx = ctx || { ids: new Map() };
    const lines = String(md || "").replace(/\r\n/g, "\n").split("\n");
    const out = [];
    let i = 0;

    const isTableSep = (line) => /^\s*\|?\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)+\|?\s*$/.test(line);
    // Split a table row on "|" but not inside `code`, $math$ or $$math$$,
    // and not on an escaped "\|" outside math (GFM renders that as "|").
    const splitRow = (line) => {
      let t = line.trim();
      if (t.startsWith("|")) t = t.slice(1);
      if (t.endsWith("|") && !t.endsWith("\\|")) t = t.slice(0, -1);
      const cells = [];
      let cur = "";
      let k = 0;
      while (k < t.length) {
        const ch = t[k];
        if (ch === "`") {
          const end = t.indexOf("`", k + 1);
          if (end > k) { cur += t.slice(k, end + 1); k = end + 1; continue; }
        }
        if (ch === "$") {
          const rest = t.slice(k);
          const md = rest.startsWith("$$") ? /^\$\$(?:\\.|[^$\\]){1,6000}?\$\$/.exec(rest) : null;
          const mi = md ? null : /^\$(?!\$)(?=\S)(?:\\.|[^$\\\n]){1,400}?(?<=[^\s\\])\$(?![\d$])/.exec(rest);
          const mm = md || mi;
          if (mm) { cur += mm[0]; k += mm[0].length; continue; }
        }
        if (ch === "\\" && t[k + 1] === "|") { cur += "|"; k += 2; continue; }
        if (ch === "|") { cells.push(cur.trim()); cur = ""; k++; continue; }
        cur += ch;
        k++;
      }
      cells.push(cur.trim());
      return cells;
    };

    while (i < lines.length) {
      const line = lines[i];
      const trim = line.trim();

      if (!trim) { i++; continue; }

      // Safe <details> ... </details> block support
      if (/^<details(?:\s+open)?\s*>$/i.test(trim)) {
        const isOpen = /\bopen\b/i.test(trim);
        i++;
        let summaryText = "Details";
        const inner = [];
        let depth = 1;
        while (i < lines.length && depth > 0) {
          const t = lines[i].trim();
          if (/^<details\b/i.test(t)) depth++;
          else if (/^<\/details\s*>$/i.test(t)) {
            depth--;
            if (depth === 0) { i++; break; }
          } else if (depth === 1 && /^<summary\s*>(.*)<\/summary\s*>$/i.test(t)) {
            summaryText = t.replace(/^<summary\s*>/i, "").replace(/<\/summary\s*>$/i, "").trim();
            i++;
            continue;
          }
          inner.push(lines[i]);
          i++;
        }
        summaryText = summaryText.replace(/&amp;/g, "&");
        // "Verify locally" blocks hold commands for a local clone (kernel
        // database, mirrored sources). Keep prose and anchors; replace the
        // command blocks with one quiet pointer to the repository.
        if (/^verify locally\b/i.test(summaryText)) {
          const kept = [];
          let inFence = false;
          let dropped = false;
          for (const ln of inner) {
            if (/^\s*```/.test(ln)) { inFence = !inFence; dropped = true; continue; }
            if (!inFence) kept.push(ln);
          }
          out.push(
            "<details class=\"verify-note\"" + (isOpen ? " open" : "") + "><summary>" +
            renderInlineSafe(summaryText, sourceContext) + "</summary>" +
            (dropped ? "<p class=\"md-quiet\">Commands for checking this against your own clone are kept in the source file. <a href=\"" + escapeHtml(verifyLocallyHref(docPath)) + "\" target=\"_blank\" rel=\"noopener noreferrer\">" + escapeHtml(verifyLocallyHref(docPath).includes("/blob/") ? "See verification commands in " + docPath + " on GitHub ↗" : "See verification commands on GitHub ↗") + "</a></p>" : "") +
            renderMarkdownBlockSafe(kept.join("\n"), sourceContext, docPath, ctx) +
            "</details>"
          );
          continue;
        }
        out.push(
          "<details" + (isOpen ? " open" : "") + "><summary>" +
          renderInlineSafe(summaryText, sourceContext) +
          "</summary>" + renderMarkdownBlockSafe(inner.join("\n"), sourceContext, docPath, ctx) +
          "</details>"
        );
        continue;
      }

      // Fenced code blocks
      const mFence = line.match(/^\s*```([A-Za-z0-9_+-]*)\s*$/);
      if (mFence) {
        const lang = mFence[1] || "";
        i++;
        const codeLines = [];
        while (i < lines.length && !/^\s*```\s*$/.test(lines[i])) {
          codeLines.push(lines[i]);
          i++;
        }
        if (i < lines.length) i++;
        out.push('<pre><code class="lang-' + escapeHtml(lang) + '">' + escapeHtml(codeLines.join("\n")) + "</code></pre>");
        continue;
      }

      // Display math $$ ... $$ (one line, or spread over several lines; text
      // on the opening and closing lines belongs to the formula)
      if (trim.startsWith("$$")) {
        const rest = trim.slice(2);
        const close = rest.indexOf("$$");
        const mLines = [];
        let after = "";
        if (close >= 0) {
          mLines.push(rest.slice(0, close));
          after = rest.slice(close + 2).trim();
          i++;
        } else {
          mLines.push(rest);
          i++;
          while (i < lines.length) {
            const ln = lines[i];
            const k = ln.indexOf("$$");
            i++;
            if (k >= 0) { mLines.push(ln.slice(0, k)); after = ln.slice(k + 2).trim(); break; }
            mLines.push(ln);
          }
        }
        out.push('<div class="math-block">' + prettifyMath(escapeHtml(mLines.join("\n").trim()), true) + "</div>");
        // A lone punctuation mark after the closing $$ ends the sentence; drop it.
        if (after && !/^[.,;:]$/.test(after)) out.push("<p>" + renderInlineSafe(after, sourceContext) + "</p>");
        continue;
      }

      // Headings
      const mHead = line.match(/^(#{1,4})\s+(.+?)\s*#*$/);
      if (mHead) {
        const lvl = mHead[1].length;
        const base = docAnchorSlug(headingPlainText(mHead[2])) || "section";
        const seen = ctx.ids.get(base) || 0;
        ctx.ids.set(base, seen + 1);
        const hid = "h-" + base + (seen ? "-" + seen : "");
        out.push("<h" + lvl + ' id="' + escapeHtml(hid) + '">' + renderInlineSafe(mHead[2], sourceContext) + "</h" + lvl + ">");
        i++;
        continue;
      }

      // Horizontal rule
      if (/^(\*{3,}|-{3,}|_{3,})\s*$/.test(trim)) {
        out.push("<hr>");
        i++;
        continue;
      }

      // Blockquote
      if (trim.startsWith(">")) {
        const qLines = [];
        while (i < lines.length && lines[i].trim().startsWith(">")) {
          qLines.push(lines[i].replace(/^\s*>\s?/, ""));
          i++;
        }
        out.push("<blockquote>" + renderMarkdownBlockSafe(qLines.join("\n"), sourceContext, docPath, ctx) + "</blockquote>");
        continue;
      }

      // GFM Table
      if (line.includes("|") && i + 1 < lines.length && isTableSep(lines[i + 1])) {
        const headers = splitRow(line);
        i += 2;
        const rows = [];
        while (i < lines.length && lines[i].trim() && lines[i].includes("|")) {
          rows.push(splitRow(lines[i]));
          i++;
        }
        const thead = "<thead><tr>" + headers.map((h) => "<th>" + renderInlineSafe(h, sourceContext) + "</th>").join("") + "</tr></thead>";
        const tbody = "<tbody>" + rows.map((r) => "<tr>" + headers.map((_, ci) => "<td>" + renderInlineSafe(r[ci] || "", sourceContext) + "</td>").join("") + "</tr>").join("") + "</tbody>";
        out.push('<div class="md-table-wrap"><table>' + thead + tbody + "</table></div>");
        continue;
      }

      // Lists (unordered & ordered)
      const isUl = /^\s*[-*+]\s+/.test(line);
      const isOl = /^\s*\d+\.\s+/.test(line);
      if (isUl || isOl) {
        const tag = isUl ? "ul" : "ol";
        const rx = isUl ? /^\s*[-*+]\s+(.*)$/ : /^\s*\d+\.\s+(.*)$/;
        // An ordered list interrupted by a display formula continues its numbering.
        const olStart = isOl ? parseInt(line.trim(), 10) : 1;
        const items = [];
        while (i < lines.length) {
          const m = lines[i].match(rx);
          if (!m) break;
          let itemTxt = m[1];
          i++;
          while (i < lines.length && lines[i].trim() && !/^\s*([-*+]|\d+\.)\s+/.test(lines[i]) && !/^\s*(#|```|>|\|)/.test(lines[i])) {
            itemTxt += " " + lines[i].trim();
            i++;
          }
          items.push("<li>" + renderInlineSafe(itemTxt, sourceContext) + "</li>");
        }
        out.push("<" + tag + (isOl && olStart > 1 ? ' start="' + olStart + '"' : "") + ">" + items.join("") + "</" + tag + ">");
        continue;
      }

      // Paragraph
      const pLines = [];
      while (
        i < lines.length &&
        lines[i].trim() &&
        !/^\s*(#{1,4}\s|```|\$\$|>|<details\b|[-*+]\s|\d+\.\s|[-*_]{3,}\s*$)/.test(lines[i]) &&
        !(lines[i].includes("|") && i + 1 < lines.length && isTableSep(lines[i + 1]))
      ) {
        pLines.push(lines[i].trim());
        i++;
      }
      if (pLines.length) {
        out.push("<p>" + renderInlineSafe(pLines.join(" "), sourceContext) + "</p>");
      } else {
        i++;
      }
    }
    return out.join("\n");
  }

  // ---------- Theme Handling ----------
  function initTheme() {
    let saved = "dark";
    try {
      const v = window.localStorage.getItem("leanre_site_theme");
      if (v === "light" || v === "dark") saved = v;
    } catch (_) { /* ignore */ }
    applyTheme(saved, false);
  }

  function applyTheme(theme, rerenderCircuit) {
    state.theme = theme === "light" ? "light" : "dark";
    document.documentElement.setAttribute("data-theme", state.theme);
    const icon = $("#themeIcon");
    if (icon) icon.textContent = state.theme === "dark" ? "☀" : "☾";
    try { window.localStorage.setItem("leanre_site_theme", state.theme); } catch (_) { /* ignore */ }
    if (rerenderCircuit && state.route.tab === "circuit" && state.circuit.data) {
      mountActiveCircuitSvg();
    } else if (rerenderCircuit && state.manifest && ["atlas", "overview", "item"].includes(state.route.tab)) {
      // Re-rendering the page would drop the full-screen element; repaint it in place.
      if (fsState.el && document.contains(fsState.el)) redrawFullscreenForTheme();
      else handleRoute({ keepScroll: true });
    }
  }

  // ---------- Hash Routing ----------
  function parseHash() {
    const raw = (window.location.hash || "").replace(/^#/, "");
    const [pathPart, queryPart] = raw.split("?");
    const segs = pathPart.split("/").filter(Boolean).map((s) => {
      try { return decodeURIComponent(s); } catch (_) { return s; }
    });
    const params = new URLSearchParams(queryPart || "");
    if (raw === "selftest=1" || raw.includes("selftest=1")) params.set("selftest", "1");

    const validTabs = new Set(["overview", "circuit", "findings", "dossiers", "blueprints", "flirt", "atlas", "xrefs", "portability", "benchmarks", "search", "experiments", "item", "projects"]);
    let tab = segs[0] || "overview";
    // An unrecognized route falls back to the overview with a short notice.
    const unknownTab = !validTabs.has(tab) && !/[=]/.test(tab) && !/^h-/.test(tab) && tab !== "selftest" ? tab : "";
    if (!validTabs.has(tab)) tab = "overview";
    return {
      tab,
      unknownTab,
      sub: segs[1] || "",
      arg: segs.slice(2).join("/"),
      cmp: params.get("cmp") || "",
      selftest: params.get("selftest") === "1" || window.location.search.includes("selftest=1")
    };
  }

  function navigate(hashStr, replace) {
    const target = hashStr.startsWith("#") ? hashStr : "#" + hashStr;
    if (window.location.hash === target) {
      handleRoute();
      return;
    }
    if (replace && window.history && window.history.replaceState) {
      try {
        window.history.replaceState(null, "", target);
        handleRoute();
        return;
      } catch (_) { /* fallback */ }
    }
    window.location.hash = target;
  }

  function updateNavHighlight(tab) {
    const nav = $("#mainNav");
    $$("#mainNav .nav-tab").forEach((btn) => {
      const on = btn.dataset.route === tab;
      btn.classList.toggle("active", on);
      if (on) btn.setAttribute("aria-current", "page"); else btn.removeAttribute("aria-current");
      // On narrow screens the tab strip scrolls; keep the active tab in view.
      if (on && nav && nav.scrollWidth > nav.clientWidth + 1 && !btn.classList.contains("hidden")) {
        try { btn.scrollIntoView({ behavior: "auto", inline: "center", block: "nearest" }); } catch (_) { /* old browsers */ }
      }
    });
    const main = $("#appMain");
    if (main) main.classList.toggle("full-bleed", tab === "circuit");
  }

  function populateChromeFromManifest() {
    const m = state.manifest || {};
    document.title = (m.repo_name ? m.repo_name + " — " : "") + "leanre";
    const repoBadge = $("#brandRepo");
    if (repoBadge) repoBadge.textContent = m.repo_name || "";

    const ext = $("#repoExtLink");
    let treeUrl = null;
    if (ext) {
      const url = safeHref(m.repo_url);
      if (url && /^https?:\/\//i.test(url)) {
        treeUrl = m.pinned_commit ? url.replace(/\/+$/, "") + "/tree/" + encodeURIComponent(m.pinned_commit) : url;
        ext.href = treeUrl;
        ext.classList.remove("hidden");
      } else {
        ext.classList.add("hidden");
      }
    }

    // Show only the tabs this project has data for (routes keep working).
    const a = m.assets || {};
    const cir = m.circuits || {};
    const visible = {
      circuit: Boolean(cir.macro || (cir.bundles || []).length || (cir.theorems || []).length),
      findings: (m.findings || []).length > 0,
      dossiers: (m.dossiers || []).length + (m.research || []).length > 0,
      blueprints: (m.blueprints || []).length > 0,
      flirt: Boolean(a.cluster_labels || a.flirt_tier1),
      atlas: Boolean(a.atlas || a.module_matrix || a.embedding_2d),
      xrefs: Boolean(a.xrefs && window.LeanreXrefs),
      portability: Boolean(a.portability),
      benchmarks: Boolean(a.benchmark || a.trim_report)
    };
    for (const [k, on] of Object.entries(visible)) {
      const tab = $("#tab-" + k);
      if (tab) tab.classList.toggle("hidden", !on);
    }

    const footerMeta = $("#footerMeta");
    if (footerMeta) {
      clearEl(footerMeta);
      const up = upstreamRepoOf(m.repo_url);
      const items = [
        el("span", { textContent: "leanre" }),
        el("span", { textContent: "AGPL-3.0-or-later" }),
        el("a", { href: LEANRE_REPO_URL, target: "_blank", rel: "noopener noreferrer", title: "leanre tool and explorer on GitHub", textContent: "leanre on GitHub ↗" })
      ];
      if (up && treeUrl && !m.demo_mode) {
        items.push(el("a", { className: "fm-proof", href: treeUrl, target: "_blank", rel: "noopener noreferrer", textContent: "Analyzed proof: " + up + (m.pinned_commit ? " @ " + String(m.pinned_commit).slice(0, 8) : "") + " ↗" }));
        items.push(el("span", { className: "fm-proof", textContent: "Independent analysis — not affiliated with the Lean community or the proof authors" }));
      }
      items.forEach((node, idx) => {
        if (idx) footerMeta.appendChild(el("span", { className: "sep" + (node.classList.contains("fm-proof") ? " fm-proof" : ""), textContent: "·", "aria-hidden": "true" }));
        footerMeta.appendChild(node);
      });
    }
  }

  // ---------- Circuit Manifest Lookup Helpers ----------
  function findCircuitEntry(mode, target) {
    const circuits = (state.manifest && state.manifest.circuits) || {};
    if (mode === "macro") {
      return circuits.macro ? { mode: "macro", name: "Macro", short: "Macro", path: circuits.macro } : null;
    }
    const list = mode === "bundle" ? (circuits.bundles || []) : (circuits.theorems || []);
    const q = String(target || "").trim();
    if (!q) return list[0] ? Object.assign({ mode }, list[0]) : null;
    const ql = q.toLowerCase();
    const qs = shortName(q).toLowerCase();
    const match =
      list.find((x) => x.name === q || x.short === q) ||
      list.find((x) => String(x.name || "").toLowerCase() === ql || String(x.short || "").toLowerCase() === ql) ||
      list.find((x) => shortName(x.name).toLowerCase() === qs);
    return match ? Object.assign({ mode }, match) : null;
  }

  function findAnyCircuitForSymbol(symbol, pathOpt) {
    const b = findCircuitEntry("bundle", symbol);
    if (b) return b;
    const t = findCircuitEntry("theorem", symbol);
    if (t) return t;
    if (pathOpt) {
      const circuits = (state.manifest && state.manifest.circuits) || {};
      const bm = (circuits.bundles || []).find((x) => x.path === pathOpt);
      if (bm) return Object.assign({ mode: "bundle" }, bm);
      const tm = (circuits.theorems || []).find((x) => x.path === pathOpt);
      if (tm) return Object.assign({ mode: "theorem" }, tm);
    }
    return null;
  }

  // ==========================================================================
  // PROJECTS: multi-proof gallery (projects.json + p/<slug>/)
  // ==========================================================================
  const SAFE_PROJECT_PATH = /^[A-Za-z0-9._\/-]*$/;
  const PROJECT_GROUPS = [
    ["kernel", "Kernel exports"],
    ["ai-assisted", "AI-assisted formalizations"],
    ["human-baseline", "Community formalizations"],
    ["demo", "Demo"],
    ["other", "Other"]
  ];

  function projectBaseFor(entry) {
    const p = String((entry && entry.path) || "").trim().replace(/^\.\/?/, "").replace(/\/+$/, "");
    if (!p || p === ".") return "";
    if (!SAFE_PROJECT_PATH.test(p) || p.split("/").some((seg) => seg === ".." || seg === "." || seg === "")) return null;
    return p + "/";
  }

  function parseRegistry(doc) {
    if (!doc || typeof doc !== "object" || !Array.isArray(doc.projects)) return null;
    const out = [];
    const seen = new Set();
    for (const p of doc.projects) {
      if (!p || typeof p !== "object") continue;
      const slug = String(p.slug || "").trim();
      if (!/^[A-Za-z0-9._-]{1,80}$/.test(slug) || seen.has(slug)) continue;
      const base = projectBaseFor(p);
      if (base == null) continue;
      seen.add(slug);
      out.push(Object.assign({}, p, { slug, _base: base }));
    }
    const cmp = typeof doc.comparison === "string" && /^[A-Za-z0-9._\/-]+\.json$/.test(doc.comparison) && !doc.comparison.split("/").includes("..") ? doc.comparison : null;
    return out.length ? { schema: String(doc.schema || ""), projects: out, comparison: cmp } : null;
  }

  async function loadRegistry() {
    try {
      return parseRegistry(await fetchJson("./projects.json", { root: true }));
    } catch (_) {
      return null; // standalone exports have no registry
    }
  }

  function projectFromManifest(m, base) {
    const st = (m && m.stats) || {};
    const slug = String(m.slug || m.repo_name || "project");
    const title = m.title && !/leanre/i.test(m.title) ? m.title : (m.repo_name || slug);
    const nF = (m.findings || []).length, nD = (m.dossiers || []).length;
    return {
      slug, title, _base: base, _root: base === "",
      tagline: m.tagline || m.description || (st.edges && !m.source_only ? "Kernel export with dependency diagrams" + (nF ? ", " + nF + " findings" : "") + (nD ? " and " + nD + " dossiers" : "") + "." : ""),
      repo_url: m.repo_url || "", pinned_commit: m.pinned_commit || "",
      files: st.total_files, lines: st.total_lines, decls: st.total_decls,
      sorry: st.sorry_count, sorry_files: st.sorry_files, axioms: st.axioms,
      has_kernel_export: !m.source_only && !m.demo_mode, source_only: Boolean(m.source_only),
      category: m.category || (m.demo_mode ? "demo" : (m.source_only ? "other" : "kernel")),
      license: m.license || ""
    };
  }

  // Projects shown in the switcher and on #projects: the registry, plus the
  // root export itself when it is a project the registry does not list.
  function projectList() {
    const list = state.registry ? state.registry.projects.slice() : [];
    if (state.rootManifest) {
      const rp = projectFromManifest(state.rootManifest, "");
      if (!list.some((p) => p.slug === rp.slug || p._base === "")) list.unshift(rp);
    }
    return list;
  }

  function currentProjectSlug() {
    const m = state.manifest || {};
    const hit = projectList().find((p) => p._base === state.base);
    return hit ? hit.slug : (m.slug || m.repo_name || "");
  }

  function projectUrl(p, hash) {
    const q = p && p._base ? "?p=" + encodeURIComponent(p.slug) : "";
    return window.location.pathname + q + (hash || "#overview");
  }

  function closeProjectMenu() {
    const menu = $("#projMenu");
    if (menu && !menu.hidden) {
      menu.hidden = true;
      const b = $("#projBtn");
      if (b) b.setAttribute("aria-expanded", "false");
    }
  }

  function renderProjectSwitcher() {
    const host = $("#projSwitch");
    const pill = $("#brandRepo");
    if (!host) return;
    clearEl(host);
    const list = projectList();
    if (!state.registry || !list.length) {
      host.classList.add("hidden");
      if (pill) pill.classList.remove("hidden");
      return;
    }
    if (pill) pill.classList.add("hidden");
    host.classList.remove("hidden");
    const cur = state.manifest ? currentProjectSlug() : "";
    const label = state.manifest ? (state.manifest.repo_name || state.manifest.slug || cur) : "All proofs";
    const menu = el("div", { className: "proj-menu", id: "projMenu", role: "menu", hidden: true });
    const btn = el("button", {
      type: "button", className: "proj-btn", id: "projBtn", "aria-haspopup": "menu", "aria-expanded": "false", "aria-controls": "projMenu", title: "Switch proof",
      onclick: async (ev) => {
        ev.stopPropagation();
        const opening = menu.hidden;
        if (opening && state.base && !state.rootManifest && !state.rootTried && !projectList().some((p) => p._base === "")) {
          state.rootTried = true;
          try {
            const rm = await fetchJson("./manifest.json", { root: true });
            if (rm && rm.schema) { state.rootManifest = rm; renderProjectSwitcher(); const b2 = $("#projBtn"); if (b2) b2.click(); return; }
          } catch (_) { /* no root project */ }
        }
        menu.hidden = !opening;
        btn.setAttribute("aria-expanded", opening ? "true" : "false");
        if (opening) { const f = menu.querySelector(".proj-item.active") || menu.querySelector(".proj-item"); if (f) f.focus(); }
      }
    }, [el("span", { className: "proj-btn-lbl", textContent: label }), el("span", { className: "proj-caret", "aria-hidden": "true", textContent: "▾" })]);
    for (const p of list) {
      const active = Boolean(state.manifest) && p.slug === cur;
      menu.appendChild(el("a", { className: "proj-item" + (active ? " active" : ""), role: "menuitem", href: projectUrl(p, "#overview"), "aria-current": active ? "true" : null }, [
        el("span", { className: "proj-item-slug", textContent: p.slug }),
        p.title && p.title !== p.slug ? el("span", { className: "proj-item-title", textContent: p.title }) : null
      ]));
    }
    menu.appendChild(el("div", { className: "proj-sep", role: "separator" }));
    menu.appendChild(el("a", { className: "proj-item all", role: "menuitem", href: "#projects", onclick: closeProjectMenu, textContent: "All proofs (" + list.length + ") ›" }));
    menu.addEventListener("keydown", (ev) => {
      if (ev.key === "Escape") { ev.stopPropagation(); closeProjectMenu(); btn.focus(); }
      if (ev.key === "ArrowDown" || ev.key === "ArrowUp") {
        ev.preventDefault();
        const items = $$(".proj-item", menu);
        const i = items.indexOf(document.activeElement);
        const n = items[(i + (ev.key === "ArrowDown" ? 1 : -1) + items.length) % items.length];
        if (n) n.focus();
      }
    });
    host.appendChild(btn);
    host.appendChild(menu);
  }

  async function renderProjectsHome() {
    const main = $("#appMain");
    clearEl(main);
    if (!state.rootManifest && state.base) {
      try {
        const rm = await fetchJson("./manifest.json", { root: true });
        if (rm && rm.schema) state.rootManifest = rm;
      } catch (_) { /* gallery root without its own project */ }
    }
    const list = projectList();
    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Proofs" }),
      el("p", { className: "page-lede", textContent: list.length > 1
        ? "Lean 4 formalizations read with the same tools. Kernel exports come with dependency diagrams and edge data; source-only scans map modules, imports and declarations."
        : "Only one proof is published here." })
    ]));
    const cur = state.manifest ? currentProjectSlug() : "";
    const groupOf = (p) => (p.has_kernel_export && !p.source_only && p.category !== "demo") ? "kernel" : (PROJECT_GROUPS.some(([k]) => k === p.category) ? p.category : "other");
    for (const [gk, glabel] of PROJECT_GROUPS) {
      const items = list.filter((p) => groupOf(p) === gk);
      if (!items.length) continue;
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: glabel })]));
      main.appendChild(el("div", { className: "proj-grid" }, items.map((p) => {
        const facts = [
          p.files ? plural(p.files, "file") : null,
          p.lines ? plural(p.lines, "line") : null,
          p.decls ? plural(p.decls, "declaration") : null
        ].filter(Boolean).join(" · ");
        let sorryTxt = null;
        if (p.proof_sorry != null) {
          sorryTxt = fmtInt(p.proof_sorry) + " proof sorry" + (Number(p.challenge_sorry) ? " (+" + fmtInt(p.challenge_sorry) + " in challenge specs)" : "");
        } else if (p.sorry != null) {
          sorryTxt = Number(p.sorry) ? fmtInt(p.sorry) + " sorry" + (p.sorry_files ? " in " + plural(p.sorry_files, "file") : "") : "no sorry";
        }
        const checks = [
          sorryTxt,
          p.axioms != null ? (Number(p.axioms) ? plural(p.axioms, "custom axiom") : "no custom axioms") : null
        ].filter(Boolean).join(" · ");
        const license = licenseLabel(p.license || (p.slug === "riemann-hypothesis" ? "None" : "Not stated"));
        const repo = safeHref(p.repo_url);
        const isCur = p.slug === cur;
        return el("article", { className: "proj-card" + (isCur ? " current" : "") }, [
          el("div", { className: "proj-card-top" }, [
            el("h3", { textContent: p.title || p.slug }),
            el("span", { className: "proj-card-slug", textContent: p.slug })
          ]),
          p.tagline ? el("p", { className: "proj-card-tag", textContent: p.tagline }) : null,
          facts ? el("p", { className: "proj-card-facts", textContent: facts }) : null,
          checks ? el("p", { className: "proj-card-facts", textContent: checks }) : null,
          el("p", { className: "proj-card-license" }, [el("span", { className: "license-badge", textContent: "License: " + license })]),
          el("div", { className: "cir-ins-acts" }, [
            isCur ? el("a", { className: "btn sm", href: "#overview", textContent: "Overview ›" }) : el("a", { className: "btn sm primary", href: projectUrl(p, "#overview"), textContent: "Open ›" }),
            repo ? el("a", { className: "btn sm", href: repo, target: "_blank", rel: "noopener noreferrer", textContent: "Proof source ↗" }) : null
          ])
        ]);
      })));
    }
    if (state.registry && state.registry.comparison) {
      const host = el("section", { className: "cmp-section", id: "cmpSection" });
      main.appendChild(host);
      renderComparisonTable(host);
    }
    main.appendChild(el("details", { className: "add-proof" }, [
      el("summary", { textContent: "Add your own Lean proof" }),
      el("p", { textContent: "Any public Lean 4 repository can be added. leanre scans the source (and a kernel export, if you have one) and writes a static folder that any web server can host." }),
      el("p", { textContent: "You need git and Python 3.11 or newer. A source scan needs no Lean toolchain; kernel diagrams need an NDJSON export, described in the README." }),
      el("pre", null, [el("code", { textContent: "git clone https://github.com/bohemian-miser/leanre && cd leanre\npython3 -m leanre.leanre gallery add path/to/your-repo \\\n    --out-dir site --slug your-proof --title \"Your proof\" \\\n    --repo-url https://github.com/you/your-proof --pinned-commit <sha>\npython3 -m http.server --directory site 8000" })]),
      el("p", null, [el("a", { href: LEANRE_REPO_URL + "#readme", target: "_blank", rel: "noopener noreferrer", textContent: "Read the README for kernel exports ↗" })]),
      el("p", { textContent: "This writes site/p/your-proof/ and updates site/projects.json. To publish it here, open a pull request that adds the p/your-proof/ folder and its entry in projects.json." })
    ]));
  }

  // Short headers keep the table inside the content column; the full name and
  // meaning of each column is in its tooltip.
  const CMP_SRC_DECLS_TITLE = "Source decls: top-level declarations parsed from .lean files; excludes compiled kernel auxiliaries";
  const CMP_COLUMNS = [
    { key: "title", label: "Proof", text: true },
    { key: "files", label: "Files", title: "Files: .lean source files" },
    { key: "lines", label: "Lines", title: "Lines: total lines of Lean source" },
    { key: "decls", label: "Source decls", title: CMP_SRC_DECLS_TITLE + "." },
    { key: "comment_pct", label: "Comments", fmt: (v) => (v == null ? "—" : Number(v).toFixed(1) + "%"), title: "Comments %: share of source lines that are comments" },
    { key: "proof_sorry", label: "Proof sorry", title: "Proof sorry: sorry placeholders inside proofs" },
    { key: "challenge_sorry", label: "Challenge", title: "Challenge sorry: sorry placeholders in challenge statements that are meant to stay open" },
    { key: "axioms", label: "Axioms", title: "Axioms: custom axioms declared in the project" },
    { key: "name_compress_ratio", label: "Compress.", fmt: (v) => (v == null ? "—" : Number(v).toFixed(2)), title: "Name compressibility: compressed size of all declaration names divided by their raw size. Lower means more repetitive, templated naming." },
    { key: "orphan_pct", label: "Orphan", fmt: (v) => (v == null ? "—" : Number(v).toFixed(1) + "%"), title: "Orphan %: share of modules not reached from the entry points." },
    { key: "clones", label: "Clones", get: (r) => (r.exact_clone_clusters != null || r.sig_clone_clusters != null ? (Number(r.exact_clone_clusters) || 0) + (Number(r.sig_clone_clusters) || 0) : null), title: "Clones: groups of modules with identical proof bodies or identical statement sets." },
    { key: "license", label: "License", text: true, title: "License: as stated in the proof repository" }
  ];

  // "None (no license)" reads as "None" in badges and tables.
  function licenseLabel(v) {
    const s = String(v == null ? "" : v).trim();
    return /^none\b/i.test(s) ? "None" : s;
  }

  // Footnotes for the comparison table, computed from the rows and registry.
  // The RH zero-declaration file count is not in the comparison data yet, so it
  // falls back to the figure from the review, gated on the RH file count.
  const RH_SLUG = "riemann-hypothesis";
  const RH_ZERO_DECL_FILES = { files: 175187, zero: 28904 };
  function cmpNotes(rows) {
    const out = { declsTitle: CMP_SRC_DECLS_TITLE, orphanStar: new Set(), footnote: "" };
    const reg = state.registry ? state.registry.projects : [];
    const kernelBits = [];
    for (const r of rows) {
      const p = reg.find((x) => x.slug === r.slug) || {};
      const rm = state.rootManifest && (state.rootManifest.slug === r.slug) ? state.rootManifest : null;
      const kd = Number((rm && rm.stats && (rm.stats.kernel_total_decls || rm.stats.total_decls)) || (p.has_kernel_export ? p.decls : 0)) || 0;
      if (kd && Number(r.decls) && kd > Number(r.decls)) kernelBits.push((r.slug === RH_SLUG ? "RH" : (r.title || r.slug)) + " has " + fmtInt(kd) + " kernel decls");
    }
    if (kernelBits.length) out.declsTitle += " (" + kernelBits.join("; ") + ").";
    else out.declsTitle += ".";
    const rh = rows.find((r) => r.slug === RH_SLUG);
    if (rh && rh.orphan_pct != null && Number(rh.orphan_pct) === 0 && Number(rh.files) > 0) {
      const files = Number(rh.files);
      const zero = Number(rh.zero_decl_files != null ? rh.zero_decl_files : (files === RH_ZERO_DECL_FILES.files ? RH_ZERO_DECL_FILES.zero : NaN));
      if (Number.isFinite(zero) && zero > 0) {
        out.orphanStar.add(RH_SLUG);
        out.footnote = "* All " + fmtInt(files) + " RH files are imported from Main, but " + fmtInt(zero) + " (" + (100 * zero / files).toFixed(1) + "%) emit zero kernel declarations.";
      }
    }
    return out;
  }

  async function renderComparisonTable(host) {
    let doc;
    try { doc = await fetchJson(state.registry.comparison, { root: true }); } catch (_) { return; }
    const rows = Array.isArray(doc && doc.projects) ? doc.projects : (Array.isArray(doc && doc.rows) ? doc.rows : []);
    if (!rows.length || !host.isConnected) return;
    const sort = tableSort("cmp", { key: "lines", dir: "desc" });
    const cur = state.manifest ? currentProjectSlug() : "";
    const notes = cmpNotes(rows);
    const cols = CMP_COLUMNS.map((c) => ({
      key: c.key, label: c.label, title: c.key === "decls" ? notes.declsTitle : c.title, num: !c.text, firstDir: c.text ? "asc" : "desc",
      get: (r) => {
        const v = c.get ? c.get(r) : r[c.key];
        if (c.key === "title") return r.title || r.slug || null;
        if (c.text) return v == null || v === "" ? null : String(v);
        const n = Number(v);
        return v == null || v === "" || !Number.isFinite(n) ? null : n;
      }
    }));
    clearEl(host);
    host.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "Side by side" }), trustBadge("tool")]));
    host.appendChild(el("p", { className: "section-lede", textContent: "The same measurements for every proof. Click a column to sort; missing values stay at the bottom." }));
    const tbody = el("tbody");
    const fill = () => {
      clearEl(tbody);
      sortRowsBy(rows, cols, sort).forEach((r) => {
        const p = projectList().find((x) => x.slug === r.slug);
        const isCur = !!cur && r.slug === cur;
        tbody.appendChild(el("tr", { className: isCur ? "selected cmp-current" : null, "aria-current": isCur ? "true" : null }, CMP_COLUMNS.map((c) => {
          if (c.key === "title") {
            const name = r.title || r.slug;
            return el("td", { className: "cmp-proof", title: name }, [
              p ? el("a", { href: isCur ? "#overview" : projectUrl(p, "#overview") }, [identWbr(name)]) : el("span", null, [identWbr(name)]),
              isCur ? el("span", { className: "pill cmp-cur-pill", textContent: "current" }) : null
            ]);
          }
          const v = c.get ? c.get(r) : r[c.key];
          if (c.key === "license") {
            const full = String(v || "").trim();
            const short = licenseLabel(full).replace(/-or-later\b/g, "+");
            // Dual licenses may break only at " OR ", never inside an SPDX id.
            const parts = short ? short.split(/\s+OR\s+/i) : ["—"];
            const kids = [];
            parts.forEach((pt, i) => { if (i) kids.push(" or "); kids.push(el("span", { className: "lic-part", textContent: pt })); });
            return el("td", { className: "cmp-license", title: full ? "License: " + licenseLabel(full) : null }, kids);
          }
          if (c.key === "orphan_pct" && notes.orphanStar.has(r.slug)) {
            return el("td", { className: "num", title: notes.footnote.replace(/^\*\s*/, "") }, [c.fmt(v), el("span", { className: "cmp-star", textContent: "*" })]);
          }
          return el("td", { className: c.text ? null : "num", textContent: c.fmt ? c.fmt(v) : (c.text ? String(v || "—") : (v == null ? "—" : fmtInt(v))) });
        })));
      });
    };
    host.appendChild(el("div", { className: "table-wrap" }, [el("table", { className: "data-table cmp-table" }, [sortableHead(cols, sort, fill), tbody])]));
    host.appendChild(el("p", { className: "cmp-legend", id: "cmpLegend" }, [
      el("b", { textContent: "Compress." }), " name compressibility (lower means more templated names) · ",
      el("b", { textContent: "Orphan" }), " share of modules not reached from the entry points · ",
      el("b", { textContent: "Clones" }), " " + ((CMP_COLUMNS.find((c) => c.label === "Clones") || {}).title || "repeated declarations").replace(/^Clones?:\s*/i, "").replace(/\.$/, "") + " · ",
      el("b", { textContent: "Challenge" }), " sorry placeholders in challenge statements that are meant to stay open"
    ]));
    if (notes.footnote) host.appendChild(el("p", { className: "cmp-footnote", textContent: notes.footnote }));
    fill();
  }

  // ==========================================================================
  // OUTLINE RAIL + BREADCRUMBS
  // ==========================================================================
  const TAB_LABEL = {
    overview: "Overview", circuit: "Diagrams", findings: "Findings", dossiers: "Dossiers", blueprints: "Blueprints",
    flirt: "Clusters", atlas: "Edge Map", xrefs: "Cross-refs", portability: "Islands", benchmarks: "Benchmarks", search: "Search",
    experiments: "Moved", item: "Declaration", projects: "Proofs"
  };

  function isMobileRail() {
    return window.matchMedia ? window.matchMedia("(max-width: 900px)").matches : false;
  }

  function initRailState() {
    try {
      const v = window.localStorage.getItem("leanre_site_rail");
      if (v === "closed") state.rail.open = false;
      const md = window.localStorage.getItem("leanre_site_rail_mode");
      if (md === "spine" || md === "topics" || md === "folders") state.rail.mode = md;
    } catch (_) { /* ignore */ }
  }

  function applyRailVisibility() {
    const rail = $("#outlineRail");
    const hasRail = Boolean(rail && !rail.hidden);
    const mobile = isMobileRail();
    document.body.classList.toggle("rail-on", hasRail && !mobile && state.rail.open);
    document.body.classList.toggle("rail-mobile-open", hasRail && mobile && state.rail.mobileOpen);
    const t = $("#railToggleBtn");
    if (t) {
      t.classList.toggle("hidden", !hasRail);
      t.setAttribute("aria-expanded", String(mobile ? state.rail.mobileOpen : state.rail.open));
    }
  }

  function toggleRail(force) {
    if (isMobileRail()) {
      state.rail.mobileOpen = force != null ? Boolean(force) : !state.rail.mobileOpen;
    } else {
      state.rail.open = force != null ? Boolean(force) : !state.rail.open;
      try { window.localStorage.setItem("leanre_site_rail", state.rail.open ? "open" : "closed"); } catch (_) { /* ignore */ }
    }
    applyRailVisibility();
    if (state.route.tab === "circuit") requestAnimationFrame(fitCircuitStage);
  }

  async function ensureOutline() {
    if (state.outline) return state.outline;
    const p = state.manifest && state.manifest.assets && state.manifest.assets.outline;
    if (!p) return null;
    try {
      const o = await fetchJson(p);
      state.outline = (o && typeof o === "object") ? o : null;
    } catch (_) {
      state.outline = null;
    }
    return state.outline;
  }

  function railModes() {
    const m = state.manifest || {};
    const a = m.assets || {};
    const o = state.outline || {};
    const modes = [];
    if ((o.spine && o.spine.length) || (m.overview_pillars && m.overview_pillars.length)) modes.push(["spine", "Proof Spine"]);
    if ((o.clusters && o.clusters.length) || a.outline || a.cluster_labels) modes.push(["topics", "Topics"]);
    if ((o.folders && o.folders.length) || a.outline || (m.top_modules && m.top_modules.length)) modes.push(["folders", "Folders"]);
    return modes;
  }

  function currentItemName() {
    const r = state.route || {};
    return r.tab === "item" ? [r.sub, r.arg].filter(Boolean).join("/") : "";
  }

  function railRow(o) {
    const attrs = {
      className: "rail-row" + (o.active ? " active" : "") + (o.cls ? " " + o.cls : ""),
      style: o.depth ? { paddingLeft: (10 + Math.min(4, o.depth) * 12) + "px" } : null,
      title: o.title || null,
      "aria-current": o.active ? "page" : null
    };
    const kids = [
      el("span", { className: "rail-lbl", textContent: o.label }),
      o.count != null && o.count !== "" ? el("span", { className: "rail-cnt", textContent: typeof o.count === "number" ? fmtCompact(o.count) : String(o.count) }) : null
    ];
    if (o.href) return el("a", Object.assign(attrs, { href: o.href, onclick: o.onclick || null }), kids);
    return el("button", Object.assign(attrs, { type: "button", onclick: o.onclick || null }), kids);
  }

  function renderRail() {
    const rail = $("#outlineRail");
    if (!rail) return;
    clearEl(rail);
    const modes = state.manifest ? railModes() : [];
    if (!modes.length) {
      rail.hidden = true;
      applyRailVisibility();
      return;
    }
    rail.hidden = false;
    if (!modes.some(([k]) => k === state.rail.mode)) state.rail.mode = modes[0][0];
    rail.appendChild(el("div", { className: "rail-hd" }, [
      el("div", { className: "rail-modes", role: "tablist", "aria-label": "Outline view" }, modes.map(([k, lbl]) => el("button", {
        type: "button", role: "tab", "aria-selected": k === state.rail.mode ? "true" : "false",
        className: k === state.rail.mode ? "active" : "", textContent: lbl,
        onclick: () => {
          state.rail.mode = k;
          try { window.localStorage.setItem("leanre_site_rail_mode", k); } catch (_) { /* ignore */ }
          renderRail();
        }
      }))),
      el("button", { type: "button", className: "rail-close", "aria-label": "Close outline", title: "Close outline", textContent: "×", onclick: () => toggleRail(false) })
    ]));
    const list = el("div", { className: "rail-list", id: "railList" });
    rail.appendChild(list);
    applyRailVisibility();
    fillRailList(list, state.rail.mode);
  }

  async function fillRailList(list, mode) {
    const m = state.manifest || {};
    const a = m.assets || {};
    if (mode !== "spine" && !state.outline && a.outline) {
      list.appendChild(el("div", { className: "rail-note", textContent: "Loading…" }));
      await ensureOutline();
      if (!list.isConnected) return;
      clearEl(list);
    }
    const o = state.outline || {};
    const cur = currentItemName();
    const closeOnMobile = () => { if (isMobileRail()) toggleRail(false); };

    if (mode === "spine") {
      const fromOutline = Boolean(o.spine && o.spine.length);
      const items = fromOutline ? o.spine : (m.overview_pillars || []).map((p) => ({
        name: p.decl || p.target || "", label: p.label || p.name, dom: p.subtree_size ?? p.count ?? p.dom, depth: p.depth,
        circuit_mode: p.circuit_mode, circuit_target: p.circuit_target, note: p.note || p.description
      }));
      list.appendChild(el("div", { className: "rail-note", textContent: !fromOutline && pillarsCountModules(m)
        ? "Ordered by exclusive subtree size (modules reached only through this one)."
        : "Ordered by exclusive subtree size (declarations reached only through this node)." }));
      for (const it of items) {
        const nm = it.name || "";
        const label = it.label || it.short || shortName(nm) || "—";
        const href = nm ? "#item/" + encodeURIComponent(nm)
          : (it.circuit_mode && it.circuit_target ? "#circuit/" + it.circuit_mode + "/" + encodeURIComponent(it.circuit_target) : null);
        list.appendChild(railRow({ label, count: Number(it.dom) || null, depth: Number(it.depth) || 0, href, active: Boolean(nm) && nm === cur, title: [nm, it.note].filter(Boolean).join(" — "), onclick: closeOnMobile }));
      }
      return;
    }

    if (mode === "topics") {
      let clusters = o.clusters;
      if ((!clusters || !clusters.length) && a.cluster_labels) {
        try {
          const doc = await fetchJson(a.cluster_labels);
          clusters = (doc.clusters || []).map((c) => ({
            id: c.cluster_id, label: (c.blinded_label && c.blinded_label.label) || c.pillar || c.cluster_id,
            count: c.counts && c.counts.live_decls, mismatch_status: c.mismatch_audit && c.mismatch_audit.status
          }));
        } catch (_) { clusters = []; }
        if (!list.isConnected) return;
      }
      list.appendChild(el("div", { className: "rail-note", textContent: "Groups of declarations with the same structural shape, labeled by topic." }));
      for (const c of (clusters || [])) {
        const label = String(c.label || c.id || "").replace(/^\[M\]\s*/, "");
        list.appendChild(railRow({
          label, count: Number(c.count) || null, title: (c.id || "") + (c.mismatch_status === "cross_domain_misplaced" ? " · in an unexpected folder" : ""),
          cls: c.mismatch_status === "cross_domain_misplaced" ? "flag" : "",
          href: "#flirt",
          onclick: () => { state.flirt.q = String(c.id || ""); state.flirt.status = "all"; state.flirt.page = 0; closeOnMobile(); if (state.route.tab === "flirt") handleRoute(); }
        }));
      }
      return;
    }

    // Folders
    let folders = o.folders;
    if ((!folders || !folders.length) && m.top_modules && m.top_modules.length) {
      const byDir = new Map();
      for (const t of m.top_modules) {
        const fp = String(t.file_path || String(t.module || "").replace(/\./g, "/") + ".lean");
        const dir = fp.includes("/") ? fp.slice(0, fp.lastIndexOf("/")) : "(top level)";
        if (!byDir.has(dir)) byDir.set(dir, { path: dir, files: 0, top_modules: [] });
        const d = byDir.get(dir);
        d.files++;
        d.top_modules.push({ module: t.module, file: fp, decls: t.decl_count });
      }
      folders = Array.from(byDir.values()).sort((x, y) => y.files - x.files);
    }
    const st = m.stats || {};
    if (Number(st.flirt_misfiles) >= 20 || a.cluster_labels) {
      list.appendChild(el("div", { className: "rail-note" }, [
        "Folder names often diverge from topic; ",
        el("a", { href: "#flirt", textContent: "see Clusters ›" })
      ]));
    }
    if (o.folder_stats && o.folder_stats.total_dirs > (folders || []).length) {
      list.appendChild(el("div", { className: "rail-note", textContent: "The " + fmtInt((folders || []).length) + " largest of " + plural(o.folder_stats.total_dirs, "folder") + "." }));
    }
    const flist = folders || [];
    const topCount = new Map();
    for (const f of flist) { const top = String(f.path || f.name || "").split("/")[0]; topCount.set(top, (topCount.get(top) || 0) + 1); }
    const groups = new Map();
    for (const f of flist) {
      const path = String(f.path || f.name || "");
      const segs = path.split("/");
      const key = (topCount.get(segs[0]) > 25 && segs.length > 1) ? segs.slice(0, 2).join("/") : segs[0];
      if (!groups.has(key)) groups.set(key, { key, files: 0, folders: [] });
      const g = groups.get(key);
      g.files += Number(f.files) || 0;
      g.folders.push(f);
    }
    const folderRow = (f, groupKey) => {
      const path = String(f.path || f.name || "");
      const rel = path === groupKey ? "(this folder)" : path.slice(groupKey.length).replace(/^\//, "");
      const kids = el("div", { className: "rail-kids", hidden: true });
      const row = railRow({
        label: rel, depth: 1, count: f.files != null ? Number(f.files) : null, cls: "folder", title: path + (f.decls ? " · " + plural(f.decls, "declaration") : ""),
        onclick: () => {
          kids.hidden = !kids.hidden;
          row.classList.toggle("open", !kids.hidden);
          if (!kids.hidden && !kids.childNodes.length) {
            for (const tm of (f.top_modules || []).slice(0, 12)) {
              const mod = String(tm.module || "");
              kids.appendChild(railRow({ label: shortName(mod), title: mod, count: tm.decls != null ? Number(tm.decls) : null, depth: 2, href: "#item/" + encodeURIComponent(mod), onclick: closeOnMobile }));
            }
            kids.appendChild(railRow({ label: "Search this folder ›", depth: 2, cls: "muted", href: "#search/" + encodeURIComponent(path.replace(/\//g, ".")), onclick: closeOnMobile }));
          }
        }
      });
      return [row, kids];
    };
    for (const g of Array.from(groups.values()).sort((x, y) => y.files - x.files)) {
      const kids = el("div", { className: "rail-kids", hidden: true });
      const row = railRow({
        label: g.key.replace(/\//g, "."), count: g.files || null, cls: "folder group", title: g.key + " · " + plural(g.folders.length, "folder"),
        onclick: () => {
          kids.hidden = !kids.hidden;
          row.classList.toggle("open", !kids.hidden);
          if (!kids.hidden && !kids.childNodes.length) {
            for (const f of g.folders) folderRow(f, g.key).forEach((n) => kids.appendChild(n));
          }
        }
      });
      list.appendChild(row);
      list.appendChild(kids);
    }
  }

  function crumbLeaf(r) {
    return plainTextFromTex(crumbLeafRaw(r));
  }

  function crumbLeafRaw(r) {
    const m = state.manifest || {};
    if (r.tab === "circuit") return r.arg ? shortName(r.arg) : (r.sub === "macro" ? "Repository map" : "");
    if (r.tab === "findings" && r.sub) { const f = (m.findings || []).find((x) => x.slug === r.sub); return f ? (f.title || f.slug) : r.sub; }
    if (r.tab === "dossiers" && r.sub) {
      if (r.sub === "research") { const d = (m.research || []).find((x) => x.slug === r.arg); return d ? (d.title || d.slug) : "Research"; }
      const d = (m.dossiers || []).find((x) => x.slug === r.sub); return d ? (d.title || d.slug) : r.sub;
    }
    if (r.tab === "blueprints" && r.sub) { const b = (m.blueprints || []).find((x) => x.id === r.sub); return b ? (b.title || b.id) : r.sub; }
    if (r.tab === "item") return shortName(currentItemName());
    if (r.tab === "xrefs" && r.sub) return shortName([r.sub, r.arg].filter(Boolean).join("/"));
    if (r.tab === "search" && r.sub) return "“" + r.sub + "”";
    return "";
  }

  function updateCrumbs(r) {
    const bar = $("#crumbBar");
    if (!bar) return;
    clearEl(bar);
    const parts = [];
    if (state.registry) parts.push(["Proofs", "#projects"]);
    if (r.tab !== "projects" && state.manifest) parts.push([state.manifest.repo_name || state.manifest.slug || "Project", "#overview"]);
    if (r.tab !== "overview" && r.tab !== "projects") parts.push([TAB_LABEL[r.tab] || r.tab, "#" + r.tab]);
    const leaf = crumbLeaf(r);
    if (leaf) parts.push([leaf, null]);
    if (parts.length < 2) { bar.classList.add("hidden"); return; }
    bar.classList.remove("hidden");
    parts.forEach(([lbl, href], i) => {
      const last = i === parts.length - 1;
      if (i) bar.appendChild(el("span", { className: "crumb-sep", "aria-hidden": "true", textContent: "›" }));
      bar.appendChild(last || !href
        ? el("span", { className: "crumb cur", "aria-current": last ? "page" : null, textContent: lbl })
        : el("a", { className: "crumb", href, textContent: lbl }));
    });
  }

  // ==========================================================================
  // 2D MAP (embedding_2d.json) + MODULE MATRIX (source-only projects)
  // ==========================================================================
  const MAP_PALETTE = ["#7cc4e4", "#e0a95a", "#6fcf9f", "#c7a6f5", "#e2777a", "#66c6b8", "#d7b46a", "#8fb3ea", "#f09fc7", "#a6d4a0", "#b8a07e", "#9aa4b2"];

  function cssVar(name, fallback) {
    try {
      const v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
      return v || fallback;
    } catch (_) { return fallback; }
  }

  // Column lookup that tolerates missing fields (layers differ by project).
  function layerFieldIndex(layer) {
    const F = {};
    (layer.fields || []).forEach((f, i) => { F[f] = i; });
    return F;
  }

  function map2dPoints(layer, proj) {
    const F = layerFieldIndex(layer);
    const T = layer.tables || {};
    const xk = proj === "pca" ? "px" : "ux";
    const yk = proj === "pca" ? "py" : "uy";
    const get = (p, k) => (F[k] != null ? p[F[k]] : undefined);
    const num = (p, k) => { const v = get(p, k); return v == null || v === "" ? null : Number(v); };
    return (layer.points || []).map((p, i) => {
      const name = String(get(p, "name") || get(p, "path") || "");
      const statusIdx = F.status_idx != null ? get(p, "status_idx") : get(p, "hygiene_flag");
      const statusTbl = F.status_idx != null ? (T.statuses || []) : (T.hygiene_flags || []);
      return {
        i, raw: p,
        x: Number(get(p, xk)) || 0,
        y: Number(get(p, yk)) || 0,
        name,
        short: String(get(p, "short") || shortName(name)),
        label: String(get(p, "label") || "").replace(/^\[M\]\s*/, ""),
        id: String(get(p, "id") || ""),
        dom: Number(get(p, "dom")) || 0,
        pillar: (T.pillars || [])[get(p, "pillar_idx")] || "",
        pillarIdx: Number(get(p, "pillar_idx")) || 0,
        dir: (T.dirs || [])[get(p, "dir_idx")] || "",
        dirIdx: Number(get(p, "dir_idx")) || 0,
        kind: (T.kinds || [])[get(p, "kind_idx")] || "",
        cluster: (T.clusters || [])[get(p, "cluster_idx")] || "",
        mod: String(F.mod != null ? (get(p, "mod") || "") : (F.mod_idx != null ? ((T.mods || [])[get(p, "mod_idx")] || "") : (F.loc != null || F.fan_in != null ? name : ""))),
        line: get(p, "line") != null ? Number(get(p, "line")) : null,
        terms: (get(p, "top_term_idxs") || []).map((t) => (T.vocab_terms || [])[t]).filter(Boolean),
        nn: (get(p, "nn_idx") || []).filter((j) => Number.isInteger(j)),
        drift: Number(get(p, "drift")) || 0,
        uniq: num(p, "uniq"),
        sim: num(p, "sim_nn1"),
        lib: num(p, "lib_sim"),
        dups: num(p, "dup_count") != null ? num(p, "dup_count") : num(p, "clone_count"),
        comments: num(p, "comment_pct"),
        sorry: num(p, "sorry_count"),
        loc: num(p, "loc"),
        fanIn: num(p, "fan_in"),
        status: statusIdx != null ? String(statusTbl[statusIdx] || "") : ""
      };
    });
  }

  // Color-by modes, offered only when the layer has the column.
  const STATUS_LABELS = { alias_vn1: "single-node alias", decide_kernel: "decide (kernel)", high_drift: "high drift", challenge_sorry: "challenge sorry", proof_sorry: "proof sorry" };
  function statusLabel(s) { return STATUS_LABELS[s] || String(s || "").replace(/_/g, " "); }
  const STATUS_COLORS = { clean: "#9aa4b2", challenge_sorry: "#e0a95a", proof_sorry: "#e2777a", axiom: "#c7a6f5", decide_kernel: "#7cc4e4", unreached: "#5b6472", alias_vn1: "#d7b46a", high_drift: "#8fb3ea" };
  const COLOR_MODES = [
    { key: "pillar", label: "Part / Branch", fields: ["pillar_idx"], type: "cat", table: "pillars" },
    { key: "folder", label: "Folder", fields: ["dir_idx"], type: "cat", table: "dirs", top: 12 },
    { key: "uniq", label: "Uniqueness", fields: ["uniq"], type: "num", lo: "duplicate", hi: "unique", stops: [[100, 116, 139], [96, 140, 210], [250, 190, 60]] },
    { key: "sim", label: "Code similarity", fields: ["sim_nn1"], type: "num", lo: "distinct", hi: "near-clone", stops: [[71, 85, 105], [45, 190, 175], [236, 92, 160]] },
    { key: "lib", label: "Library overlap", fields: ["lib_sim"], type: "num", lo: "project-native", hi: "library-backed", stops: [[170, 110, 70], [150, 155, 160], [60, 200, 140]] },
    { key: "drift", label: "Folder drift", fields: ["drift"], type: "num", lo: "same folder", hi: "elsewhere", stops: [[91, 127, 166], [224, 169, 90]] },
    { key: "size", label: "Subtree / Size", fields: ["dom", "loc", "fan_in"], type: "num", log: true, lo: "small", hi: "large", stops: [[60, 80, 110], [124, 196, 228], [250, 236, 170]] },
    { key: "dups", label: "Duplicates", fields: ["dup_count", "clone_count"], type: "num", log: true, min1: true, lo: "one of a kind", hi: "many copies", stops: [[90, 100, 115], [226, 119, 122]] },
    { key: "status", label: "Status / Sorry", fields: ["status_idx", "hygiene_flag"], type: "cat", tables: { status_idx: "statuses", hygiene_flag: "hygiene_flags" } },
    { key: "comments", label: "Comments %", fields: ["comment_pct"], type: "num", lo: "none", hi: "most lines", stops: [[71, 85, 105], [167, 139, 250]] },
    { key: "kind", label: "Kind", fields: ["kind_idx"], type: "cat", table: "kinds" }
  ];
  const FOCUS_FILTERS = [
    { key: "all", label: "All" },
    { key: "unique", label: "Unique only (≥ 0.65)", ok: (p) => p.uniq != null, test: (p) => p.uniq >= 0.65 },
    { key: "dups", label: "Duplicates / clones", ok: (p) => p.dups != null || p.sim != null, test: (p) => (p.dups || 0) > 1 || (p.sim != null && p.sim >= 0.95) },
    { key: "drift", label: "Drifted", ok: () => true, test: (p) => p.drift >= 0.7 },
    { key: "sorry", label: "Has sorry", ok: (p) => p.sorry != null || p.status !== "", test: (p) => (p.sorry || 0) > 0 || /sorry/.test(p.status) }
  ];

  function colorModesFor(layer) {
    const F = layerFieldIndex(layer);
    const T = layer.tables || {};
    const out = [];
    for (const m of COLOR_MODES) {
      const field = m.fields.find((f) => F[f] != null);
      if (!field) continue;
      if (m.key === "comments" && !(layer.points || []).some((p) => Number(p[F[field]]) > 0)) continue;
      if (m.type === "cat") {
        const tbl = T[m.table || (m.tables || {})[field]];
        if (!Array.isArray(tbl) || tbl.length < 2) continue;
      }
      out.push(Object.assign({}, m, { field }));
    }
    return out;
  }

  function colorScale(mode, layer) {
    const F = layerFieldIndex(layer);
    const T = layer.tables || {};
    const fi = F[mode.field];
    if (mode.type === "cat") {
      const tbl = T[mode.table || (mode.tables || {})[mode.field]] || [];
      const keyOf = (p) => Number(p.raw[fi]) || 0;
      const colorOf = (k) => (mode.key === "status" && STATUS_COLORS[tbl[k]]) ? STATUS_COLORS[tbl[k]] : MAP_PALETTE[k % MAP_PALETTE.length];
      return { cat: true, tbl, keyOf, color: (p) => colorOf(keyOf(p)), colorOf };
    }
    let lo = Infinity, hi = -Infinity;
    const tr = (v) => { let x = Number(v); if (mode.min1) x = Math.max(0, x - 1); return mode.log ? Math.log1p(Math.max(0, x)) : x; };
    for (const p of (layer.points || [])) {
      const v = p[fi];
      if (v == null || v === "" || !Number.isFinite(Number(v))) continue;
      const t = tr(v);
      lo = Math.min(lo, t); hi = Math.max(hi, t);
    }
    if (!Number.isFinite(lo)) { lo = 0; hi = 1; }
    if (hi - lo < 1e-9) hi = lo + 1;
    const stops = mode.stops;
    const ramp = (t) => {
      const u = Math.max(0, Math.min(1, t)) * (stops.length - 1);
      const k = Math.min(stops.length - 2, Math.floor(u));
      const c = mix(stops[k], stops[k + 1], u - k);
      return "rgb(" + c.join(",") + ")";
    };
    const untr = (t) => { let x = mode.log ? Math.expm1(t) : t; if (mode.min1) x += 1; return x; };
    return {
      cat: false, ramp, lo: untr(lo), hi: untr(hi),
      color: (p) => { const v = p.raw[fi]; return v == null || v === "" ? "rgb(110,116,126)" : ramp((tr(v) - lo) / (hi - lo)); }
    };
  }

  // Plain names for the proof's main parts (pillar codes used in the data).
  const PART_NAMES = {
    A: "Theta & local matching",
    B: "Galois & étale tower",
    C: "Windowed Ш¹",
    D: "Arakelov covolume",
    LIT: "Theta / toroidal core",
    DM: "Shared diamond",
    BR: "Zeta bridge"
  };
  function partName(code) {
    const c = String(code || "");
    if (PART_NAMES[c]) return PART_NAMES[c] + " (" + c + ")";
    return c.length > 3 ? c : (c ? "Part " + c : "");
  }

  // View window helpers (data coordinates, aspect-locked to the canvas size).
  const MAP_PAD = 22;
  function map2dAspect(win, dims) {
    const want = (dims.W - 2 * MAP_PAD) / (dims.H - 2 * MAP_PAD);
    let w = win.x1 - win.x0, h = win.y1 - win.y0;
    const cx = (win.x0 + win.x1) / 2, cy = (win.y0 + win.y1) / 2;
    if (w / h > want) h = w / want; else w = h * want;
    return { x0: cx - w / 2, x1: cx + w / 2, y0: cy - h / 2, y1: cy + h / 2 };
  }
  function map2dFitWindow(pts, dims, onlyIdx) {
    let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
    const use = onlyIdx ? onlyIdx.map((j) => pts[j]).filter(Boolean) : pts;
    for (const p of use) { x0 = Math.min(x0, p.x); x1 = Math.max(x1, p.x); y0 = Math.min(y0, p.y); y1 = Math.max(y1, p.y); }
    if (!Number.isFinite(x0)) { x0 = -1; x1 = 1; y0 = -1; y1 = 1; }
    const mx = Math.max(1e-6, x1 - x0) * (onlyIdx ? 0.35 : 0.02);
    const my = Math.max(1e-6, y1 - y0) * (onlyIdx ? 0.35 : 0.02);
    return map2dAspect({ x0: x0 - mx, x1: x1 + mx, y0: y0 - my, y1: y1 + my }, dims);
  }
  function map2dToScreen(win, dims, x, y) {
    return [
      MAP_PAD + ((x - win.x0) / (win.x1 - win.x0)) * (dims.W - 2 * MAP_PAD),
      dims.H - MAP_PAD - ((y - win.y0) / (win.y1 - win.y0)) * (dims.H - 2 * MAP_PAD)
    ];
  }
  function map2dToData(win, dims, sx, sy) {
    return [
      win.x0 + ((sx - MAP_PAD) / (dims.W - 2 * MAP_PAD)) * (win.x1 - win.x0),
      win.y0 + ((dims.H - MAP_PAD - sy) / (dims.H - 2 * MAP_PAD)) * (win.y1 - win.y0)
    ];
  }

  function map2dPointLabel(p, layerKey) {
    return layerKey === "clusters_141" ? (p.label || p.id) : (p.short || p.name);
  }

  const MAP_SPARSE_N = 60;
  function drawMap2d(canvas, pts, opts) {
    const dims = opts.dims || { W: 760, H: 560 };
    canvas.width = dims.W;
    canvas.height = dims.H;
    const ctx = canvas.getContext("2d");
    if (!ctx || !pts.length) return;
    const win = opts.win || map2dFitWindow(pts, dims);
    const zoom = opts.zoom || 1;
    const scale = opts.scale;
    ctx.fillStyle = cssVar("--bg-code", "#0c0f13");
    ctx.fillRect(0, 0, dims.W, dims.H);
    const hidden = opts.hidden || new Set();
    const focus = opts.focus || null;
    // Sparse layers (a handful of modules or folders) get larger dots.
    const rScale = Math.min(2.2, 1 + Math.log2(zoom) * 0.25) * (pts.length < MAP_SPARSE_N ? 2.2 : 1);
    for (const p of pts) {
      const [sx, sy] = map2dToScreen(win, dims, p.x, p.y);
      p.sx = sx; p.sy = sy;
      p.r = (1.8 + Math.min(4.2, Math.log10(1 + (p.dom || p.loc || 0)) * 0.75)) * rScale;
      p.vis = !(scale && scale.cat && hidden.has(scale.keyOf(p))) && sx > -10 && sx < dims.W + 10 && sy > -10 && sy < dims.H + 10;
      p.dim = Boolean(focus && !focus(p));
    }
    const colorOf = (p) => (scale ? scale.color(p) : MAP_PALETTE[p.pillarIdx % MAP_PALETTE.length]);
    const sel = opts.sel >= 0 ? pts[opts.sel] : null;
    const nnSet = new Set(sel ? sel.nn : []);
    // Dimmed (filtered-out) points first, then the rest on top.
    for (const pass of [true, false]) {
      ctx.globalAlpha = pass ? 0.1 : (sel ? 0.32 : 0.84);
      for (const p of pts) {
        if (!p.vis || p.dim !== pass || (sel && (p === sel || nnSet.has(p.i)))) continue;
        ctx.fillStyle = colorOf(p);
        ctx.beginPath();
        ctx.arc(p.sx, p.sy, p.r, 0, Math.PI * 2);
        ctx.fill();
      }
    }
    ctx.globalAlpha = 1;
    const hiColor = cssVar("--text-hi", "#eceff3");
    if (sel) {
      ctx.strokeStyle = cssVar("--text-muted", "#8c96a5");
      ctx.lineWidth = 1.2;
      ctx.setLineDash([4, 3]);
      for (const j of sel.nn) {
        const q = pts[j];
        if (!q) continue;
        ctx.beginPath(); ctx.moveTo(sel.sx, sel.sy); ctx.lineTo(q.sx, q.sy); ctx.stroke();
      }
      ctx.setLineDash([]);
      for (const j of sel.nn) {
        const q = pts[j];
        if (!q) continue;
        ctx.fillStyle = colorOf(q);
        ctx.beginPath(); ctx.arc(q.sx, q.sy, q.r + 1, 0, Math.PI * 2); ctx.fill();
        ctx.strokeStyle = hiColor; ctx.lineWidth = 1; ctx.stroke();
      }
      ctx.fillStyle = colorOf(sel);
      ctx.beginPath(); ctx.arc(sel.sx, sel.sy, sel.r + 2.5, 0, Math.PI * 2); ctx.fill();
      ctx.strokeStyle = hiColor; ctx.lineWidth = 2; ctx.stroke();
    }
    if (zoom >= 1.8 || (sel && opts.labelSel)) {
      ctx.font = "11px " + cssVar("--sans", "sans-serif");
      ctx.textBaseline = "middle";
      const placed = [];
      const fits = (b) => b.x >= 2 && b.y >= 2 && b.x + b.w <= dims.W - 2 && b.y + b.h <= dims.H - 2 &&
        !placed.some((o) => b.x < o.x + o.w && b.x + b.w > o.x && b.y < o.y + o.h && b.y + b.h > o.y);
      const cand = pts.filter((p) => p.vis && !p.dim).sort((a, b) => (b === sel) - (a === sel) || (b.dom || b.loc || 0) - (a.dom || a.loc || 0));
      const maxLabels = zoom >= 1.8 ? Math.round(18 * Math.max(1, (dims.W * dims.H) / (760 * 560)) ** 0.5) : 1;
      for (const p of cand) {
        if (placed.length >= maxLabels) break;
        const txt = String(map2dPointLabel(p, opts.layer)).slice(0, 30);
        const w = ctx.measureText(txt).width + 6;
        const box = { x: p.sx + p.r + 3, y: p.sy - 7, w, h: 14 };
        if (!fits(box)) { box.x = p.sx - p.r - 3 - w; if (!fits(box)) continue; }
        placed.push(box);
        ctx.fillStyle = cssVar("--bg-code", "#0c0f13");
        ctx.globalAlpha = 0.78;
        ctx.fillRect(box.x, box.y, box.w, box.h);
        ctx.globalAlpha = 1;
        ctx.fillStyle = hiColor;
        ctx.fillText(txt, box.x + 3, box.y + 7);
      }
    }
    if (opts.box) {
      const b = opts.box;
      ctx.strokeStyle = cssVar("--accent", "#7cc4e4");
      ctx.lineWidth = 1;
      ctx.setLineDash([3, 3]);
      ctx.strokeRect(Math.min(b.x0, b.x1) + 0.5, Math.min(b.y0, b.y1) + 0.5, Math.abs(b.x1 - b.x0), Math.abs(b.y1 - b.y0));
      ctx.setLineDash([]);
      ctx.fillStyle = cssVar("--accent-bg", "rgba(124,196,228,0.1)");
      ctx.fillRect(Math.min(b.x0, b.x1), Math.min(b.y0, b.y1), Math.abs(b.x1 - b.x0), Math.abs(b.y1 - b.y0));
    }
  }

  function map2dCanvasXY(canvas, ev) {
    const rect = canvas.getBoundingClientRect();
    return [((ev.clientX - rect.left) / rect.width) * canvas.width, ((ev.clientY - rect.top) / rect.height) * canvas.height];
  }

  function map2dHit(canvas, pts, ev) {
    const [cx, cy] = map2dCanvasXY(canvas, ev);
    // Sparse layers get a wider hit radius so their few dots are easy to pick.
    let best = -1, bd = pts.length < MAP_SPARSE_N ? 26 * 26 : 121;
    for (const p of pts) {
      if (!p.vis) continue;
      const d = (p.sx - cx) * (p.sx - cx) + (p.sy - cy) * (p.sy - cy);
      if (d < bd) { bd = d; best = p.i; }
    }
    return best;
  }

  function declActions(name, mod, line, opts) {
    const o = opts || {};
    const acts = el("div", { className: "cir-ins-acts" });
    if (name) acts.appendChild(el("a", { className: "btn sm" + (o.primary ? " primary" : ""), href: "#item/" + encodeURIComponent(name), textContent: "Inspect ›" }));
    const gh = mod ? buildGithubUrl(mod, line) : null;
    if (gh) {
      const peek = makeSrcButton(gh, name || mod, { className: "btn sm", text: "Source", links: o.links });
      if (peek) acts.appendChild(peek);
      if (!o.noGithub) acts.appendChild(el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "Proof file ↗" }));
    }
    return acts;
  }

  function pct(v) { return v == null ? "" : Math.round(Number(v) * (Number(v) <= 1 ? 100 : 1)) + "%"; }

  function renderMap2dDetail(box, pt, pts, layerKey, onPick) {
    clearEl(box);
    if (!pt) {
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Click a dot to see what it is, its vocabulary and its five nearest neighbors." }));
      return;
    }
    box.appendChild(el("div", { className: "cir-ins-title", textContent: map2dPointLabel(pt, layerKey) }));
    if (layerKey === "clusters_141") box.appendChild(el("div", { className: "cir-ins-note mono", textContent: pt.id + " · represented by " + pt.short }));
    else if (pt.name !== pt.short) box.appendChild(el("div", { className: "cir-ins-note mono", textContent: pt.name }));
    const kv = el("div", { className: "cir-ins-kv" });
    const add = (k, v) => { if (v == null || v === "") return; kv.appendChild(el("div", { className: "k", textContent: k })); kv.appendChild(el("div", { className: "v", textContent: String(v) })); };
    add("Kind", pt.kind);
    add("Status", pt.status ? statusLabel(pt.status) : "");
    add("Exclusive subtree", pt.dom ? fmtInt(pt.dom) : "");
    add("Lines", pt.loc != null ? fmtInt(pt.loc) : "");
    add("Imported by", pt.fanIn != null ? fmtInt(pt.fanIn) : "");
    add("Part", partName(pt.pillar));
    add("Folder", pt.dir);
    add("Module", pt.mod && pt.mod !== pt.name ? pt.mod + (pt.line ? ":" + pt.line : "") : "");
    add("Cluster", pt.cluster);
    add("Uniqueness", pt.uniq != null ? Number(pt.uniq).toFixed(2) + " (1 = unique)" : "");
    add("Similarity to nearest", pt.sim != null ? Number(pt.sim).toFixed(2) : "");
    add("Library overlap", pt.lib != null ? pct(pt.lib) : "");
    add("Same-signature copies", pt.dups != null ? fmtInt(pt.dups) : "");
    add("Comment lines", pt.comments != null ? Number(pt.comments).toFixed(1) + "%" : "");
    add("sorry", pt.sorry != null ? fmtInt(pt.sorry) : "");
    add("Neighbors elsewhere", Math.round(pt.drift * 10) + " of 10 nearest live in another folder");
    box.appendChild(kv);
    if (pt.terms.length) {
      box.appendChild(el("div", { className: "map-sub", textContent: "Vocabulary" }));
      box.appendChild(el("div", { className: "map-terms", textContent: pt.terms.slice(0, 6).join(" · ") }));
    }
    if (pt.nn.length) {
      box.appendChild(el("div", { className: "map-sub", textContent: "Nearest neighbors" }));
      box.appendChild(el("div", { className: "map-nn" }, pt.nn.slice(0, 5).map((j) => {
        const q = pts[j];
        return q ? el("button", { type: "button", className: "map-nn-btn", title: q.name, textContent: map2dPointLabel(q, layerKey), onclick: () => onPick(j) }) : null;
      })));
    }
    box.appendChild(declActions(pt.name, pt.mod, pt.line, { primary: true }));
  }

  // ---- Full screen for charts and diagrams (in-page overlay + native API) ----
  const fsState = { el: null, onChange: null, btn: null, themeStale: false };
  // Floating layers (hover tip, source drawer) must live inside a native
  // full-screen element to be painted above it.
  function placeFloatingLayers() {
    const tip = $("#circuitTip");
    const host = fsState.el && document.contains(fsState.el) ? fsState.el : document.body;
    if (tip && tip.parentNode !== host) host.appendChild(tip);
    if (srcView.root && !srcView.root.hidden) placeSourceDrawer();
  }
  function setFullscreen(target, on, onChange, btn) {
    if (on) {
      if (fsState.el && fsState.el !== target) setFullscreen(fsState.el, false, fsState.onChange, fsState.btn);
      if (onChange && onChange.before) onChange.before(true);
      Object.assign(fsState, { el: target, onChange, btn });
      target.classList.add("fs-on");
      document.body.classList.add("fs-lock");
      if (btn) { btn.textContent = "✕ Exit full screen"; btn.setAttribute("aria-pressed", "true"); }
      placeFloatingLayers();
      try {
        const allowNative = !navigator.userActivation || navigator.userActivation.isActive;
        if (allowNative && target.requestFullscreen && !document.fullscreenElement) {
          const pr = target.requestFullscreen();
          if (pr && pr.catch) pr.catch(() => {});
        }
      } catch (_) { /* overlay still works */ }
    } else {
      if (onChange && onChange.before) onChange.before(false);
      target.classList.remove("fs-on");
      document.body.classList.remove("fs-lock");
      if (btn) { btn.textContent = "⛶ Full screen"; btn.setAttribute("aria-pressed", "false"); }
      try {
        if (document.fullscreenElement && document.exitFullscreen) {
          const pr = document.exitFullscreen();
          if (pr && pr.catch) pr.catch(() => {});
        }
      } catch (_) { /* ignore */ }
      const stale = fsState.themeStale;
      if (fsState.el === target) Object.assign(fsState, { el: null, onChange: null, btn: null, themeStale: false });
      placeFloatingLayers();
      // The theme changed while in full screen: repaint the rest of the page now.
      if (stale && state.manifest && ["atlas", "overview", "item"].includes(state.route.tab)) {
        requestAnimationFrame(() => handleRoute({ keepScroll: true }));
        return;
      }
    }
    requestAnimationFrame(() => requestAnimationFrame(() => { if (onChange) onChange(on); }));
  }

  // Canvases remember their last draw call so a theme switch can repaint them
  // in place (inside full screen) with the new colors.
  const themeRedraws = new WeakMap();
  function themeAwareDraw(fn) {
    return function (canvas) {
      const args = Array.prototype.slice.call(arguments);
      if (canvas && typeof canvas === "object") themeRedraws.set(canvas, () => fn.apply(null, args));
      return fn.apply(null, args);
    };
  }
  function redrawFullscreenForTheme() {
    const root = fsState.el;
    if (!root) return;
    fsState.themeStale = true;
    $$("canvas", root).forEach((c) => { const f = themeRedraws.get(c); if (f) f(); });
    if (typeof fsState.onChange === "function") fsState.onChange(true);
    root.dispatchEvent(new CustomEvent("leanre-theme", { detail: { theme: state.theme } }));
  }
  function exitFullscreen() {
    if (fsState.el) setFullscreen(fsState.el, false, fsState.onChange, fsState.btn);
  }
  function fullscreenButton(target, onChange) {
    const btn = el("button", { type: "button", className: "btn sm fs-btn", "aria-pressed": "false", title: "Full screen (Esc to exit)", textContent: "⛶ Full screen" });
    btn.addEventListener("click", () => setFullscreen(target, !target.classList.contains("fs-on"), onChange, btn));
    return btn;
  }
  // Escape for full screen is part of the single ordered handler (handleGlobalEscape).
  document.addEventListener("fullscreenchange", () => {
    if (!document.fullscreenElement && fsState.el) exitFullscreen();
  });

  // Two-finger pinch + one-finger pan + tap/double-tap on any element.
  // handlers: { pan(dx, dy), pinch(factor, cx, cy), tap(ev), doubleTap(ev), start(ev), end() }
  function attachTouchGestures(target, handlers) {
    const pts = new Map();
    let pinchD = 0, pinchMid = null, startT = 0, moved = 0, lastTap = { t: 0, x: 0, y: 0 };
    target.style.touchAction = "none";
    target.addEventListener("pointerdown", (ev) => {
      if (ev.pointerType === "mouse") return;
      pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY });
      if (!handlers.noCapture) { try { target.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ } }
      if (pts.size === 1) { startT = Date.now(); moved = 0; if (handlers.start) handlers.start(ev); }
      if (pts.size === 2) {
        const [a, b] = Array.from(pts.values());
        pinchD = Math.hypot(a.x - b.x, a.y - b.y);
        pinchMid = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
        moved = 99;
      }
    });
    target.addEventListener("pointermove", (ev) => {
      if (ev.pointerType === "mouse" || !pts.has(ev.pointerId)) return;
      const prev = pts.get(ev.pointerId);
      pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY });
      if (pts.size === 2) {
        const [a, b] = Array.from(pts.values());
        const d = Math.hypot(a.x - b.x, a.y - b.y);
        const mid = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
        if (pinchD > 0 && handlers.pinch) handlers.pinch(d / pinchD, mid.x, mid.y);
        if (pinchMid && handlers.pan) handlers.pan(mid.x - pinchMid.x, mid.y - pinchMid.y);
        pinchD = d; pinchMid = mid;
      } else if (pts.size === 1) {
        const dx = ev.clientX - prev.x, dy = ev.clientY - prev.y;
        moved += Math.hypot(dx, dy);
        if (moved > 6 && handlers.pan) handlers.pan(dx, dy);
      }
    });
    const up = (ev) => {
      if (ev.pointerType === "mouse" || !pts.has(ev.pointerId)) return;
      pts.delete(ev.pointerId);
      if (pts.size < 2) { pinchD = 0; pinchMid = null; }
      if (pts.size === 0) {
        if (moved <= 6 && Date.now() - startT < 500 && ev.type === "pointerup") {
          const now = Date.now();
          if (now - lastTap.t < 320 && Math.hypot(ev.clientX - lastTap.x, ev.clientY - lastTap.y) < 24) {
            lastTap = { t: 0, x: 0, y: 0 };
            if (handlers.doubleTap) handlers.doubleTap(ev);
          } else {
            lastTap = { t: now, x: ev.clientX, y: ev.clientY };
            if (handlers.tap) handlers.tap(ev);
          }
        }
        if (handlers.end) handlers.end();
      }
    };
    target.addEventListener("pointerup", up);
    target.addEventListener("pointercancel", up);
    target.dataset.touchGestures = "1";
  }

  const LAYER_LABELS = { landmarks: "Landmarks", clusters_141: "Clusters", modules: "Modules", folders: "Folders" };
  const MAP_LAYER_UNITS = { landmarks: "declaration", clusters_141: "cluster", modules: "module", folders: "folder" };

  // Share of points whose nearest neighbor sits in another folder, for the map lede.
  // Kernel landmarks use the exported subtree-filtered figure; other layers are
  // counted over every point so the sentence holds for all of them.
  function map2dDriftSentence(layerKey, layer) {
    const drift = ((layer && layer.metrics) || {}).drift || {};
    const fmt1 = (v) => Number(v).toFixed(1) + "%";
    if (layerKey === "landmarks") {
      return drift.dom1k_nn1_diff_folder_pct != null && drift.dom1k_count
        ? fmt1(drift.dom1k_nn1_diff_folder_pct) + " of declarations with 1,000 or more declarations in their exclusive subtree have their nearest neighbor in a different folder."
        : "";
    }
    const F = layerFieldIndex(layer);
    const pts = layer.points || [];
    let n = 0, diff = 0;
    if (F.nn_idx != null && F.dir_idx != null) {
      for (const p of pts) {
        const j = (p[F.nn_idx] || [])[0];
        if (!Number.isInteger(j) || !pts[j]) continue;
        n += 1;
        if (p[F.dir_idx] !== pts[j][F.dir_idx]) diff += 1;
      }
    }
    const pctVal = n ? (100 * diff) / n : (drift.dom1k_nn1_diff_folder_pct != null && drift.dom1k_count === pts.length ? Number(drift.dom1k_nn1_diff_folder_pct) : null);
    if (pctVal == null) return "";
    const unitMany = { clusters_141: "clusters", modules: "modules", folders: "folders" }[layerKey] || "points";
    return fmt1(pctVal) + " of " + unitMany + " have their nearest neighbor in a different folder.";
  }

  // Mounts the interactive 2D map into `host`. Used on #atlas and the overview lens.
  async function mountMap2d(host, opts) {
    const o = opts || {};
    const path = state.manifest && state.manifest.assets && state.manifest.assets.embedding_2d;
    if (!path || !host) return false;
    host.classList.add("map-host");
    // Re-mounts (projection, layer or color change) reuse the parsed file and
    // rebuild synchronously: no spinner flash, and focus returns to the same control.
    const prevAe = document.activeElement;
    const refocus = prevAe && prevAe !== host && host.contains(prevAe)
      ? { tag: prevAe.tagName, cls: String(prevAe.className || ""), txt: /^(INPUT|SELECT)$/.test(prevAe.tagName) ? "" : prevAe.textContent }
      : null;
    let doc = host._mapDocPath === path ? host._mapDoc : null;
    if (!doc) {
      clearEl(host);
      host.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })]));
      try { doc = await fetchJson(path); } catch (err) {
        clearEl(host);
        host.appendChild(el("div", { className: "empty-card" }, [el("h3", { textContent: "Could not load the 2D map" }), el("p", { textContent: String(err.message || err) })]));
        return false;
      }
      if (!host.isConnected) return false;
      host._mapDoc = doc;
      host._mapDocPath = path;
    }
    const layers = doc.layers || {};
    const LAYER_ORDER = ["landmarks", "modules", "clusters_141", "folders"];
    const layerKeys = Object.keys(layers).filter((k) => layers[k] && Array.isArray(layers[k].points) && layers[k].points.length)
      .sort((a, b) => ((LAYER_ORDER.indexOf(a) + 1) || 99) - ((LAYER_ORDER.indexOf(b) + 1) || 99));
    const st = state.map2d;
    if (!layers[st.layer] || !layerKeys.includes(st.layer)) {
      st.layer = ["landmarks", "modules", "clusters_141", "folders"].find((k) => layerKeys.includes(k)) || layerKeys[0];
    }
    const layer = layers[st.layer];
    if (!layer) { clearEl(host); return false; }
    clearEl(host);
    const viewKey = st.layer + "|" + st.proj;
    if (st.viewKey !== viewKey) { st.viewKey = viewKey; st.win = null; st.zoom = 1; st.hidden = new Set(); st.sel = -1; }
    if (!(st.hidden instanceof Set)) st.hidden = new Set();
    if (!st.tool) st.tool = "pan";
    if (!st.focusKey) st.focusKey = "all";
    const modes = colorModesFor(layer);
    if (!modes.some((m) => m.key === st.color)) st.color = (modes[0] || {}).key || "pillar";
    const mode = modes.find((m) => m.key === st.color);
    const scale = mode ? colorScale(mode, layer) : null;

    const metrics = layer.metrics || {};
    const drift = metrics.drift || {};
    const mk = metrics[st.proj === "pca" ? "pca2" : "knn2"] || {};
    const unit = MAP_LAYER_UNITS[st.layer] || "declaration";
    if (!o.compact) {
      const driftNote = map2dDriftSentence(st.layer, layer);
      host.appendChild(el("p", { className: "section-lede", textContent: "Each dot is a " + unit + ", placed by the vocabulary it uses (Mathlib names, imports and identifiers), so nearby dots draw on similar mathematics." + (driftNote ? " " + driftNote : "") }));
    }
    const seg = (items, key) => el("div", { className: "seg" }, items.map(([k, lbl]) => el("button", {
      type: "button", className: st[key] === k ? "active" : "", textContent: lbl,
      onclick: () => { st[key] = k; if (key === "layer") st.sel = -1; mountMap2d(host, o); }
    })));
    const colorSel = el("select", {
      className: "select map-color", "aria-label": "Color by",
      onchange: (ev) => { st.color = ev.target.value; st.hidden = new Set(); mountMap2d(host, o); }
    }, modes.map((m) => el("option", { value: m.key, selected: m.key === st.color, textContent: m.label })));
    host.appendChild(el("div", { className: "toolbar-row" }, [
      seg([["knn", "Nonlinear (k-NN)"], ["pca", "Linear (PCA)"]], "proj"),
      layerKeys.length > 1 ? seg(layerKeys.map((k) => [k, (LAYER_LABELS[k] || k) + " (" + fmtInt(layers[k].count || layers[k].points.length) + ")"]), "layer") : null,
      modes.length > 1 ? el("label", { className: "map-color-lbl" }, ["Color by ", colorSel]) : null,
      !o.compact && mk.knn_preservation != null ? el("span", { className: "toolbar-count", title: "How well the flat layout keeps each point's true nearest neighbors", textContent: "Neighbor preservation " + Number(mk.knn_preservation).toFixed(2) + " · trustworthiness " + Number(mk.trustworthiness).toFixed(2) }) : null
    ]));

    const pts = map2dPoints(layer, st.proj);
    if (st.sel >= pts.length) st.sel = -1;
    const dims = { W: 760, H: 560 };
    let fullWin = map2dFitWindow(pts, dims);
    if (!st.win) st.win = fullWin;
    const zoomOf = (win) => Math.max(1, (fullWin.x1 - fullWin.x0) / (win.x1 - win.x0));

    const canvas = el("canvas", { className: "map2d-canvas", tabindex: "0", "aria-label": "2D map. Ctrl or ⌘ + scroll, pinch, or double-click to zoom; drag to pan; Esc clears the selection." });
    const tip = el("div", { className: "map-tip", hidden: true, role: "tooltip" });
    const detail = el("aside", { className: "map2d-detail" });
    const legend = el("div", { className: "map-legend" });
    const zoomOut = el("span", { className: "map-zoom", textContent: "1.0×" });
    const findStatus = el("span", { className: "map-find-status", "aria-live": "polite" });
    const fitNbBtn = el("button", { type: "button", className: "btn sm", textContent: "Fit neighbors", disabled: st.sel < 0 });
    const toolSeg = el("div", { className: "seg" }, [["pan", "Pan"], ["box", "Box zoom"]].map(([k, lbl]) => el("button", {
      type: "button", className: st.tool === k ? "active" : "", textContent: lbl, title: k === "box" ? "Drag a rectangle to zoom (or hold Shift while dragging)" : "Drag to move the map",
      onclick: (ev) => { st.tool = k; $$("button", toolSeg).forEach((b) => b.classList.toggle("active", b === ev.currentTarget)); canvas.style.cursor = k === "box" ? "crosshair" : "grab"; }
    })));
    const findInput = el("input", { type: "search", className: "input map-find", placeholder: "Find " + unit + "…", "aria-label": "Find on the map", value: st.findQ || "" });
    findInput.addEventListener("input", () => { st.findQ = findInput.value; });
    const zoomHint = el("div", { className: "map-zoom-hint", "aria-hidden": "true", textContent: "Ctrl/⌘ + scroll or double-click to zoom" });
    let zoomHintT = null;
    const flashZoomHint = () => {
      zoomHint.classList.add("on");
      clearTimeout(zoomHintT);
      zoomHintT = setTimeout(() => zoomHint.classList.remove("on"), 1400);
    };
    const wrap = el("div", { className: "atlas-canvas-wrap map2d-wrap" }, [canvas, tip, zoomHint]);

    const focusFilters = FOCUS_FILTERS.filter((f) => f.key === "all" || (pts.some(f.ok) && pts.some((p) => f.ok(p) && f.test(p))));
    if (!focusFilters.some((f) => f.key === st.focusKey)) st.focusKey = "all";
    const focusFn = () => { const f = FOCUS_FILTERS.find((x) => x.key === st.focusKey); return f && f.test ? f.test : null; };

    let box = null;
    const redraw = () => {
      st.zoom = zoomOf(st.win);
      zoomOut.textContent = st.zoom.toFixed(1) + "×";
      fitNbBtn.disabled = st.sel < 0;
      drawMap2d(canvas, pts, { dims, win: st.win, zoom: st.zoom, sel: st.sel, scale, hidden: st.hidden, focus: focusFn(), box, layer: st.layer, labelSel: true });
    };
    const setWin = (win) => {
      let w = map2dAspect(win, dims);
      const fw = fullWin.x1 - fullWin.x0;
      const minW = fw / 40;
      if (w.x1 - w.x0 < minW) {
        const cx = (w.x0 + w.x1) / 2, cy = (w.y0 + w.y1) / 2, k = minW / (w.x1 - w.x0);
        w = map2dAspect({ x0: cx - (cx - w.x0) * k, x1: cx + (w.x1 - cx) * k, y0: cy - (cy - w.y0) * k, y1: cy + (w.y1 - cy) * k }, dims);
      }
      if (w.x1 - w.x0 >= fw) w = fullWin;
      st.win = w;
      redraw();
    };
    const zoomAt = (sx, sy, factor) => {
      const [dx, dy] = map2dToData(st.win, dims, sx, sy);
      const w = st.win;
      setWin({ x0: dx - (dx - w.x0) / factor, x1: dx + (w.x1 - dx) / factor, y0: dy - (dy - w.y0) / factor, y1: dy + (w.y1 - dy) / factor });
    };
    const panBy = (dxPx, dyPx) => {
      const kx = (st.win.x1 - st.win.x0) / (dims.W - 2 * MAP_PAD);
      const ky = (st.win.y1 - st.win.y0) / (dims.H - 2 * MAP_PAD);
      st.win = { x0: st.win.x0 - dxPx * kx, x1: st.win.x1 - dxPx * kx, y0: st.win.y0 + dyPx * ky, y1: st.win.y1 + dyPx * ky };
      redraw();
    };
    const zoomTo = (j, level) => {
      const p = pts[j];
      if (!p) return;
      const w = (fullWin.x1 - fullWin.x0) / level, h = (fullWin.y1 - fullWin.y0) / level;
      setWin({ x0: p.x - w / 2, x1: p.x + w / 2, y0: p.y - h / 2, y1: p.y + h / 2 });
    };
    const pick = (j) => {
      st.sel = j;
      redraw();
      renderMap2dDetail(detail, j >= 0 ? pts[j] : null, pts, st.layer, pick);
    };
    const resetView = () => { box = null; setWin(fullWin); };
    const resize = () => {
      const on = host.classList.contains("fs-on");
      const center = [(st.win.x0 + st.win.x1) / 2, (st.win.y0 + st.win.y1) / 2];
      const zoom = st.zoom || 1;
      dims.W = on ? Math.max(320, Math.floor(wrap.clientWidth)) : 760;
      dims.H = on ? Math.max(240, Math.floor(wrap.clientHeight)) : 560;
      fullWin = map2dFitWindow(pts, dims);
      const w = (fullWin.x1 - fullWin.x0) / zoom, h = (fullWin.y1 - fullWin.y0) / zoom;
      st.win = map2dAspect({ x0: center[0] - w / 2, x1: center[0] + w / 2, y0: center[1] - h / 2, y1: center[1] + h / 2 }, dims);
      setWin(st.win);
    };
    fitNbBtn.addEventListener("click", () => {
      if (st.sel < 0) return;
      setWin(map2dFitWindow(pts, dims, [st.sel].concat(pts[st.sel].nn)));
    });
    const runFind = () => {
      const q = findInput.value.trim().toLowerCase();
      if (!q) { findStatus.textContent = ""; return; }
      const nameOf = (p) => String(map2dPointLabel(p, st.layer) + " " + p.id + " " + p.short).toLowerCase();
      const hit = pts.find((p) => p.name.toLowerCase() === q)
        || pts.filter((p) => p.short.toLowerCase() === q).sort((a, b) => (b.dom || 0) - (a.dom || 0))[0]
        || pts.find((p) => nameOf(p).startsWith(q))
        || pts.find((p) => nameOf(p).includes(q) || p.name.toLowerCase().includes(q));
      if (!hit) { findStatus.textContent = "No match on this map"; return; }
      findStatus.textContent = "";
      if (scale && scale.cat && st.hidden.has(scale.keyOf(hit))) { st.hidden.delete(scale.keyOf(hit)); buildLegend(); }
      st.sel = hit.i;
      zoomTo(hit.i, Math.max(6, st.zoom));
      renderMap2dDetail(detail, hit, pts, st.layer, pick);
    };
    findInput.addEventListener("keydown", (ev) => { if (ev.key === "Enter") { ev.preventDefault(); runFind(); } });
    findInput.addEventListener("change", runFind);

    const buildLegend = () => {
      clearEl(legend);
      if (!scale) return;
      if (!scale.cat) {
        const bar = el("span", { className: "map-colorbar", "aria-hidden": "true" });
        bar.style.background = "linear-gradient(to right, " + [0, 0.25, 0.5, 0.75, 1].map((t) => scale.ramp(t)).join(", ") + ")";
        const fmt = (v) => (Math.abs(v) <= 1 && !mode.log ? Number(v).toFixed(2) : fmtCompact(Math.round(v)));
        legend.appendChild(el("span", { className: "map-colorbar-wrap" }, [
          el("span", { className: "map-legend-note", textContent: fmt(scale.lo) + " " + mode.lo }),
          bar,
          el("span", { className: "map-legend-note", textContent: fmt(scale.hi) + " " + mode.hi })
        ]));
        return;
      }
      const counts = new Map();
      for (const p of pts) { const k = scale.keyOf(p); counts.set(k, (counts.get(k) || 0) + 1); }
      let keys = Array.from(counts.keys());
      if (mode.top) keys = keys.sort((a, b) => counts.get(b) - counts.get(a)).slice(0, mode.top);
      else keys.sort((a, b) => a - b);
      for (const k of keys) {
        const raw = scale.tbl[k];
        const label = mode.key === "pillar" ? partName(raw) : (mode.key === "folder" ? String(raw || "folder " + k).split(/[./]/).slice(-1)[0] : (mode.key === "status" ? statusLabel(raw || k) : String(raw || k).replace(/_/g, " ")));
        const off = st.hidden.has(k);
        const pill = el("button", {
          type: "button", className: "map-pill" + (off ? " off" : ""), "aria-pressed": off ? "false" : "true",
          title: "Click to show or hide · double-click to show only this", textContent: label + " · " + fmtInt(counts.get(k))
        });
        pill.prepend(el("i", { className: "atlas-swatch", style: { background: scale.colorOf(k) } }));
        pill.addEventListener("click", () => {
          if (st.hidden.has(k)) st.hidden.delete(k); else st.hidden.add(k);
          buildLegend(); redraw();
          const again = Array.from(legend.querySelectorAll(".map-pill")).find((b) => b.textContent === pill.textContent);
          if (again) again.focus({ preventScroll: true });
        });
        pill.addEventListener("dblclick", () => {
          const all = Array.from(counts.keys());
          const solo = all.every((kk) => kk === k || st.hidden.has(kk)) && !st.hidden.has(k);
          st.hidden = new Set(solo ? [] : all.filter((kk) => kk !== k));
          buildLegend(); redraw();
        });
        legend.appendChild(pill);
      }
      if (mode.top && counts.size > keys.length) legend.appendChild(el("span", { className: "map-legend-note", textContent: "Top " + keys.length + " of " + plural(counts.size, "folder") }));
    };

    const showTip = (j, cx, cy) => {
      if (j < 0) { tip.hidden = true; return; }
      const p = pts[j];
      clearEl(tip);
      tip.appendChild(el("div", { className: "map-tip-name", textContent: map2dPointLabel(p, st.layer) }));
      const lines = [
        p.pillar ? partName(p.pillar) : null,
        p.dir ? "Folder: " + p.dir : null,
        p.dom ? fmtInt(p.dom) + " in exclusive subtree" : (p.loc != null ? fmtInt(p.loc) + " lines" : null),
        p.uniq != null ? "Uniqueness " + Number(p.uniq).toFixed(2) : null,
        p.sim != null ? "Similarity to nearest " + Number(p.sim).toFixed(2) : null,
        p.lib != null ? "Library overlap " + pct(p.lib) : null,
        p.dups != null && p.dups > 1 ? plural(p.dups, "same-signature copy", "same-signature copies") : null,
        p.sorry ? fmtInt(p.sorry) + " sorry" : null,
        Math.round(p.drift * 10) + " of 10 nearest neighbors in other folders"
      ].filter(Boolean);
      for (const t of lines) tip.appendChild(el("div", { textContent: t }));
      tip.hidden = false;
      const wr = wrap.getBoundingClientRect();
      const cr = canvas.getBoundingClientRect();
      const px = (cx / canvas.width) * cr.width + (cr.left - wr.left);
      const py = (cy / canvas.height) * cr.height + (cr.top - wr.top);
      tip.style.left = Math.max(4, Math.min(wr.width - 250, px + 14)) + "px";
      tip.style.top = Math.max(4, Math.min(wr.height - 120, py + 14)) + "px";
    };

    // Mouse: drag to pan, Box zoom (or Shift+drag), click to select, wheel zoom.
    let drag = null;
    canvas.style.cursor = st.tool === "box" ? "crosshair" : "grab";
    canvas.addEventListener("pointerdown", (ev) => {
      if (ev.pointerType !== "mouse" && ev.pointerType !== "pen" && ev.pointerType !== "") return;
      if (ev.button !== 0) return;
      const [cx, cy] = map2dCanvasXY(canvas, ev);
      drag = { cx, cy, lx: cx, ly: cy, moved: 0, box: st.tool === "box" || ev.shiftKey };
      try { canvas.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
      if (!drag.box) canvas.style.cursor = "grabbing";
    });
    canvas.addEventListener("pointermove", (ev) => {
      if (ev.pointerType === "touch") return;
      const [cx, cy] = map2dCanvasXY(canvas, ev);
      if (drag) {
        drag.moved = Math.max(drag.moved, Math.hypot(cx - drag.cx, cy - drag.cy));
        if (drag.box) {
          box = { x0: drag.cx, y0: drag.cy, x1: cx, y1: cy };
          redraw();
        } else if (drag.moved > 2) {
          panBy(cx - drag.lx, cy - drag.ly);
        }
        drag.lx = cx; drag.ly = cy;
        tip.hidden = true;
        return;
      }
      const j = map2dHit(canvas, pts, ev);
      canvas.style.cursor = j >= 0 ? "pointer" : (st.tool === "box" ? "crosshair" : "grab");
      showTip(j, cx, cy);
    });
    const endDrag = (ev) => {
      if (!drag) return;
      const d = drag;
      drag = null;
      canvas.style.cursor = st.tool === "box" ? "crosshair" : "grab";
      if (d.box && box && Math.abs(box.x1 - box.x0) > 6 && Math.abs(box.y1 - box.y0) > 6) {
        const [ax, ay] = map2dToData(st.win, dims, Math.min(box.x0, box.x1), Math.max(box.y0, box.y1));
        const [bx, by] = map2dToData(st.win, dims, Math.max(box.x0, box.x1), Math.min(box.y0, box.y1));
        box = null;
        setWin({ x0: ax, x1: bx, y0: ay, y1: by });
        return;
      }
      box = null;
      if (d.moved <= 3 && ev && ev.type === "pointerup") {
        const j = map2dHit(canvas, pts, ev);
        if (j >= 0) { pick(j); return; }
        if (st.sel >= 0) { pick(-1); return; }
      }
      redraw();
    };
    canvas.addEventListener("pointerup", endDrag);
    canvas.addEventListener("pointercancel", endDrag);
    canvas.addEventListener("pointerleave", () => { tip.hidden = true; });
    // Plain wheel scrolls the page while the map is unzoomed and inline;
    // Ctrl/⌘ + wheel (or trackpad pinch), a zoomed map, or full screen zooms.
    canvas.addEventListener("wheel", (ev) => {
      if (!(ev.ctrlKey || ev.metaKey) && st.zoom <= 1.01 && !host.classList.contains("fs-on")) { flashZoomHint(); return; }
      ev.preventDefault();
      const [cx, cy] = map2dCanvasXY(canvas, ev);
      zoomAt(cx, cy, Math.exp(-ev.deltaY * 0.0016));
    }, { passive: false });
    const zoomOrReset = (cx, cy) => { if (st.zoom <= 1.01) zoomAt(cx, cy, 2.5); else resetView(); };
    canvas.addEventListener("dblclick", (ev) => { ev.preventDefault(); const [cx, cy] = map2dCanvasXY(canvas, ev); zoomOrReset(cx, cy); });
    canvas.addEventListener("keydown", (ev) => {
      if (ev.key === "+" || ev.key === "=") { ev.preventDefault(); zoomAt(dims.W / 2, dims.H / 2, 1.5); }
      else if (ev.key === "-") { ev.preventDefault(); zoomAt(dims.W / 2, dims.H / 2, 1 / 1.5); }
      else if (ev.key === "0") { ev.preventDefault(); resetView(); }
      else if (ev.key === "Escape" && st.sel >= 0) { ev.preventDefault(); ev.stopPropagation(); pick(-1); }
    });
    // Touch: pinch to zoom at the fingers, drag to pan, tap to select, double-tap to reset.
    const toCanvas = (x, y) => { const r = canvas.getBoundingClientRect(); return [((x - r.left) / r.width) * canvas.width, ((y - r.top) / r.height) * canvas.height]; };
    const pxScale = () => canvas.width / Math.max(1, canvas.getBoundingClientRect().width);
    attachTouchGestures(canvas, {
      pan: (dx, dy) => panBy(dx * pxScale(), dy * pxScale()),
      pinch: (f, x, y) => { const [cx, cy] = toCanvas(x, y); zoomAt(cx, cy, f); },
      tap: (ev) => { const j = map2dHit(canvas, pts, ev); if (j >= 0) { pick(j); const [cx, cy] = map2dCanvasXY(canvas, ev); showTip(j, cx, cy); } else { tip.hidden = true; if (st.sel >= 0) pick(-1); } },
      doubleTap: (ev) => { if (ev && ev.clientX != null) { const [cx, cy] = toCanvas(ev.clientX, ev.clientY); zoomOrReset(cx, cy); } else resetView(); }
    });

    const focusRow = focusFilters.length > 1 ? el("div", { className: "map-focus", role: "group", "aria-label": "Focus" }, focusFilters.map((f) => el("button", {
      type: "button", className: "map-chip" + (st.focusKey === f.key ? " active" : ""), "aria-pressed": st.focusKey === f.key ? "true" : "false", textContent: f.label,
      onclick: (ev) => {
        st.focusKey = f.key;
        $$(".map-chip", focusRow).forEach((b) => { const on = b === ev.currentTarget; b.classList.toggle("active", on); b.setAttribute("aria-pressed", on ? "true" : "false"); });
        redraw();
      }
    }))) : null;

    const section = el("div", { className: "map2d-grid" + (o.compact ? " compact" : "") });
    const fsBtn = fullscreenButton(host, () => resize());
    const detailsToggle = el("button", { type: "button", className: "btn sm map-details-toggle", textContent: "Details", onclick: () => host.classList.toggle("details-collapsed") });
    const mapTools = el("div", { className: "map-tools" }, [
      toolSeg,
      el("button", { type: "button", className: "btn sm", title: "Zoom in", "aria-label": "Zoom in", textContent: "+", onclick: () => zoomAt(dims.W / 2, dims.H / 2, 1.6) }),
      el("button", { type: "button", className: "btn sm", title: "Zoom out", "aria-label": "Zoom out", textContent: "−", onclick: () => zoomAt(dims.W / 2, dims.H / 2, 1 / 1.6) }),
      el("button", { type: "button", className: "btn sm", title: "Show the whole map (or double-click it)", textContent: "Reset", onclick: resetView }),
      zoomOut,
      fitNbBtn,
      el("div", { className: "spacer" }),
      findInput,
      findStatus,
      detailsToggle,
      fsBtn
    ]);
    section.appendChild(el("div", { className: "map2d-main" }, [mapTools, focusRow, wrap, legend]));
    section.appendChild(detail);
    host.appendChild(section);
    buildLegend();
    redraw();
    renderMap2dDetail(detail, st.sel >= 0 ? pts[st.sel] : null, pts, st.layer, pick);
    if (refocus) {
      const again = Array.from(host.querySelectorAll(refocus.tag.toLowerCase())).find((n) => String(n.className || "") === refocus.cls && (!refocus.txt || n.textContent === refocus.txt));
      if (again) again.focus({ preventScroll: true });
    }
    host._map2d = { pts, pick, zoomTo, resetView, runFind: (q) => { findInput.value = q; runFind(); }, state: st, modes, dims, fsBtn, canvas };
    return true;
  }

  function drawModuleMatrix(canvas, mm, sel) {
    const grid = Array.isArray(mm.grid) ? mm.grid : [];
    const G = Number(mm.grid_size) || grid.length || 1;
    const scale = Math.max(4, Math.floor(512 / G));
    const pad = 10;
    const size = G * scale;
    const ctx = atlasSizeCanvas(canvas, size + 2 * pad, size + 2 * pad);
    if (!ctx) return { scale, pad, G };
    ctx.fillStyle = canvasBg();
    ctx.fillRect(0, 0, size + 2 * pad, size + 2 * pad);
    let mx = 1;
    for (const row of grid) for (const v of (row || [])) mx = Math.max(mx, Number(v) || 0);
    const lmx = Math.log1p(mx);
    for (let r = 0; r < G; r++) {
      const row = grid[r] || [];
      for (let c = 0; c < G; c++) {
        const v = Number(row[c]) || 0;
        if (v <= 0) continue;
        const t = Math.pow(Math.log1p(v) / lmx, 0.8);
        let R, Gc, B;
        if (isLightTheme()) {
          [R, Gc, B] = t < 0.6 ? mix([214, 228, 238], [40, 128, 170], t / 0.6) : mix([40, 128, 170], [180, 83, 9], (t - 0.6) / 0.4);
        } else {
          R = Math.round(30 + t * (t > 0.6 ? 200 : 70));
          Gc = Math.round(70 + t * 140);
          B = Math.round(110 + t * (t > 0.6 ? 20 : 130));
        }
        ctx.fillStyle = "rgb(" + R + "," + Gc + "," + B + ")";
        ctx.fillRect(pad + c * scale, pad + r * scale, scale, scale);
      }
    }
    ctx.strokeStyle = canvasInk(0.14);
    ctx.lineWidth = 1;
    let prevTop = null;
    for (const rg of (mm.regions || [])) {
      const b0 = Number(rg.bin_start || 0);
      const top = String(rg.key || "").split(".")[0];
      const changed = prevTop !== null && top !== prevTop;
      prevTop = top;
      if (b0 <= 0 || !changed) continue;
      const p = pad + b0 * scale + 0.5;
      ctx.beginPath(); ctx.moveTo(p, pad); ctx.lineTo(p, pad + size); ctx.moveTo(pad, p); ctx.lineTo(pad + size, p); ctx.stroke();
    }
    ctx.strokeStyle = canvasInk(0.4);
    ctx.strokeRect(pad + 0.5, pad + 0.5, size - 1, size - 1);
    if (sel) {
      ctx.strokeStyle = "#7cc4e4";
      ctx.lineWidth = 2;
      ctx.strokeRect(pad + sel.c * scale - 1, pad + sel.r * scale - 1, scale + 2, scale + 2);
    }
    return { scale, pad, G };
  }

  const EDGE_ROLE = { type: "in the statement", value: "in the proof", both: "statement and proof" };

  function trayHeader(title, sub, onClose) {
    return el("div", { className: "tray-hd" }, [
      el("div", null, [el("strong", { textContent: title }), sub ? el("span", { className: "tray-sub", textContent: sub }) : null]),
      el("button", { type: "button", className: "icon-btn", "aria-label": "Close", title: "Close", textContent: "×", onclick: onClose })
    ]);
  }

  function declTrayRow(d) {
    return el("div", { className: "tray-row" }, [
      el("div", { className: "tray-main" }, [
        el("span", { className: "tray-name", title: d.name, textContent: d.short || shortName(d.name) }),
        el("span", { className: "tray-meta", textContent: [d.kind, d.dom ? fmtInt(d.dom) + " in subtree" : null, d.mod ? shortName(d.mod) + (d.line ? ":" + d.line : "") : null].filter(Boolean).join(" · ") })
      ]),
      declActions(d.name, d.mod, d.line, { noGithub: true })
    ]);
  }

  // e = [src_name, dst_name, edge_role, src_mod, src_line, dst_mod, dst_line]
  function edgeTrayRow(e) {
    const [sName, dName, role, sMod, sLine, dMod, dLine] = e;
    const sUrl = sMod ? buildGithubUrl(sMod, sLine) : null;
    const dUrl = dMod ? buildGithubUrl(dMod, dLine) : null;
    const canCompare = isLeanBlob(sUrl) || isLeanBlob(dUrl);
    return el("div", { className: "tray-row" }, [
      el("div", { className: "tray-main" }, [
        el("span", { className: "tray-name", title: sName + " → " + dName }, [
          el("a", { href: "#item/" + encodeURIComponent(sName), textContent: shortName(sName) }),
          el("span", { className: "tray-arrow", textContent: " → " }),
          el("a", { href: "#item/" + encodeURIComponent(dName), textContent: shortName(dName) })
        ]),
        el("span", { className: "tray-meta", textContent: (EDGE_ROLE[role] || role || "") + (sMod ? " · " + shortName(sMod) : "") })
      ]),
      el("div", { className: "cir-ins-acts" }, [
        el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(sName), textContent: "Inspect ›" }),
        sUrl ? makeSrcButton(sUrl, sName, { className: "btn sm", text: "Source" }) : null,
        canCompare ? el("button", { type: "button", className: "btn sm", textContent: "Compare A ↔ B", onclick: () => openSourceCompare(
          { url: sUrl || "", title: sName, line: sLine, label: "A" },
          { url: dUrl || "", title: dName, line: dLine, label: "B" }
        ) }) : null
      ])
    ]);
  }

  function moduleTrayRow(t) {
    const url = safeHref(t.url) || buildGithubUrl(t.name || t.module, 1);
    const name = t.name || t.module || "";
    return el("div", { className: "tray-row" }, [
      el("div", { className: "tray-main" }, [
        el("span", { className: "tray-name", title: name, textContent: name }),
        el("span", { className: "tray-meta", textContent: [t.decl_count != null ? plural(t.decl_count, "declaration") : null, t.fan_in != null ? "imported by " + fmtInt(t.fan_in) : null].filter(Boolean).join(" · ") })
      ]),
      el("div", { className: "cir-ins-acts" }, [
        el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(name), textContent: "Inspect ›" }),
        url ? makeSrcButton(url, name, { className: "btn sm", text: "Source" }) : null
      ])
    ]);
  }

  function renderModuleMatrixBody(mm) {
    const main = $("#appMain");
    clearEl(main);
    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Module matrix" }),
      trustBadge("tool"),
      el("p", { className: "page-lede", textContent: "Imports between the " + fmtInt(mm.n_modules || 0) + " modules, ordered so that each folder sits in one block. " + (mm.diagonal_near_pct != null ? mm.diagonal_near_pct + "% of the " + fmtInt(mm.n_edges || 0) + " imports stay near the diagonal, inside or next to their own folder." : "") })
    ]));
    const canvas = el("canvas", { className: "atlas-canvas", id: "moduleMatrixCanvas", "aria-label": "Module import matrix" });
    const readout = el("div", { className: "atlas-readout", textContent: "Hover a cell to see which folders it connects; click it to list the modules and imports inside." });
    const tray = el("div", { className: "cell-tray", hidden: true });
    const mmCard = el("section", { className: "atlas-card", id: "moduleMatrixCard" });
    let mmSel = null;
    main.appendChild(mmCard);
    [
      el("div", { className: "atlas-card-hd" }, [el("h3", { textContent: "Imports by folder" }), el("span", { className: "mm-fs" })]),
      el("p", { className: "atlas-explain", textContent: "Each cell counts imports from the modules in its row to the modules in its column. Brighter cells hold more imports." }),
      el("div", { className: "atlas-canvas-wrap" }, [canvas]),
      el("p", { className: "atlas-axis", textContent: "Rows import columns. Lines mark where the top-level folder changes." }),
      readout,
      tray
    ].forEach((n) => mmCard.appendChild(n));
    let geo = drawModuleMatrix(canvas, mm, null);
    mmCard.querySelector(".mm-fs").replaceWith(fullscreenButton(mmCard, atlasFsFit(mmCard, canvas, () => { geo = drawModuleMatrix(canvas, mm, mmSel); })));
    const cellAt = (ev) => {
      const [cx, cy] = atlasCanvasXY(canvas, ev);
      const c = Math.floor((cx - geo.pad) / geo.scale);
      const r = Math.floor((cy - geo.pad) / geo.scale);
      return (r < 0 || c < 0 || r >= geo.G || c >= geo.G) ? null : { r, c };
    };
    const binLabel = (i) => ((mm.bins || [])[i] || {}).label || "block " + i;
    const cellText = (cell) => binLabel(cell.r) + " → " + binLabel(cell.c) + " · " + plural(Number(((mm.grid || [])[cell.r] || [])[cell.c]) || 0, "import");
    const closeMm = () => {
      mmSel = null;
      tray.hidden = true;
      readout.classList.remove("locked");
      geo = drawModuleMatrix(canvas, mm, null);
    };
    canvas.addEventListener("mousemove", (ev) => {
      const cell = cellAt(ev);
      if (!cell) return;
      const v = Number(((mm.grid || [])[cell.r] || [])[cell.c]) || 0;
      canvas.style.cursor = v > 0 ? "pointer" : "crosshair";
      if (mmSel) return; // keep the selected cell's readout while its tray is open
      readout.textContent = cellText(cell);
    });
    canvas.addEventListener("click", (ev) => {
      const cell = cellAt(ev);
      if (!cell) return;
      if (mmSel && mmSel.r === cell.r && mmSel.c === cell.c) { closeMm(); return; }
      mmSel = cell;
      readout.textContent = "Selected: " + cellText(cell) + ". Click the cell again or × to close.";
      readout.classList.add("locked");
      geo = drawModuleMatrix(canvas, mm, cell);
      const samples = (mm.cell_samples || {})[cell.r + "," + cell.c] || [];
      const rowB = (mm.bins || [])[cell.r] || {};
      const colB = (mm.bins || [])[cell.c] || {};
      clearEl(tray);
      tray.hidden = false;
      tray.appendChild(trayHeader(binLabel(cell.r) + " → " + binLabel(cell.c), plural(Number(((mm.grid || [])[cell.r] || [])[cell.c]) || 0, "import"), closeMm));
      tray.appendChild(el("div", { className: "tray-cols" }, [
        el("div", null, [el("h4", { textContent: "Row: largest modules" }), ...((rowB.top_modules || []).slice(0, 4).map(moduleTrayRow))]),
        el("div", null, [el("h4", { textContent: "Column: largest modules" }), ...((colB.top_modules || []).slice(0, 4).map(moduleTrayRow))])
      ]));
      if (samples.length) {
        tray.appendChild(el("h4", { textContent: "Sample imports in this cell" }));
        for (const sm of samples.slice(0, 6)) {
          tray.appendChild(edgeTrayRow([sm.src, sm.dst, "", sm.src, 1, sm.dst, 1]));
        }
      }
    });
    const mapHost = el("section", { className: "map2d-section", id: "map2dSection" });
    if (state.manifest.assets && state.manifest.assets.embedding_2d) {
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "2D map" })]));
      main.appendChild(mapHost);
      mountMap2d(mapHost);
    }
  }

  // ==========================================================================
  // DECLARATION INSPECTOR (#item/<name>)
  // ==========================================================================
  async function findSearchEntry(name) {
    const sMeta = state.manifest && state.manifest.search;
    if (!sMeta || !name) return null;
    const packs = await Promise.all(searchShardPrefixesForQuery(name).map((p) => loadSearchShard(p)));
    let loose = null;
    for (const pk of packs) {
      for (const raw of (pk.rows || [])) {
        const e = normalizeSearchEntry(raw, pk.modPrefixes);
        if (e.name === name) return e;
        if (!loose && !name.includes(".") && shortName(e.name) === name) loose = e;
      }
    }
    return loose;
  }

  function cachedAsset(key) {
    const p = state.manifest && state.manifest.assets && state.manifest.assets[key];
    return p ? (state.cacheJson.get(projectRelPath(p)) || null) : null;
  }

  function moduleFromOutline(name) {
    const m = state.manifest || {};
    const tm = (m.top_modules || []).find((t) => t.module === name);
    if (tm) return { module: name, file: tm.file_path, decls: tm.decl_count };
    for (const f of ((state.outline && state.outline.folders) || [])) {
      const hit = (f.top_modules || []).find((t) => t.module === name);
      if (hit) return { module: name, file: hit.file, decls: hit.decls, folder: f.path };
    }
    return null;
  }

  async function gatherItemInfo(name) {
    await ensureOutline();
    const info = { name, short: shortName(name), kind: "", mod: "", line: null, dom: null, live: null, circuit: null, bpId: null, isModule: false, spine: null, found: false };
    const e = await findSearchEntry(name);
    if (e) {
      Object.assign(info, { name: e.name, short: shortName(e.name), kind: e.kind, mod: e.mod, line: e.line, dom: e.dom || null, live: e.live, bpId: e.bpId, found: true });
      info.circuit = findAnyCircuitForSymbol(e.name, e.circuitPath);
    }
    const sp = ((state.outline && state.outline.spine) || []).find((s) => s.name === info.name);
    if (sp) {
      info.spine = sp;
      info.found = true;
      info.kind = info.kind || sp.kind || "";
      info.mod = info.mod || sp.mod || "";
      info.line = info.line || sp.line || null;
      info.dom = info.dom || sp.dom || null;
    }
    if (!info.circuit) info.circuit = findAnyCircuitForSymbol(info.name);
    const atlas = cachedAsset("atlas");
    if (atlas && !info.line) {
      for (const bin of ((atlas.hic_matrix && atlas.hic_matrix.bin_catalog) || [])) {
        const d = (bin || []).find((x) => x.name === info.name);
        if (d) { info.line = d.line; info.mod = info.mod || d.mod; info.kind = info.kind || d.kind; break; }
      }
    }
    if (!info.found) {
      const mod = moduleFromOutline(name);
      const looksModule = /^[A-Z][A-Za-z0-9_']*(\.[A-Z][A-Za-z0-9_']*)+$/.test(name);
      if (mod || (e && e.kind === "module")) { Object.assign(info, { isModule: true, kind: "module", mod: name, found: true, decls: mod && mod.decls }); }
      else if (looksModule && state.manifest.source_only) { Object.assign(info, { isModule: true, kind: "module", mod: name }); }
    }
    if (info.kind === "module") info.isModule = true;
    info.neighbors = (state.outline && state.outline.neighbors && state.outline.neighbors[info.name]) || null;
    if (!info.neighbors && info.circuit && info.circuit.path) {
      try {
        const data = await fetchJson(info.circuit.path);
        const nodes = (data.payload && data.payload.nodes) || [];
        const pick = (kind) => nodes.filter((n) => n.kind === kind && n.full_name && !/\s/.test(n.full_name)).map((n) => ({ name: n.full_name, rel: "" }));
        const dep = pick("callee"), use = pick("caller");
        if (dep.length || use.length) info.neighbors = { used_by: use, depends_on: dep, fromDiagram: true };
      } catch (_) { /* optional */ }
    }
    return info;
  }

  // Map of identifier -> declaration name, built only from names we know are
  // related to this item (neighbors, diagram nodes, twins). No fuzzy matching.
  function buildKnownLinks(info, extraNames) {
    const full = new Set();
    const add = (n) => { if (n && typeof n === "string" && n !== info.name) full.add(n); };
    if (info.neighbors) {
      for (const x of (info.neighbors.used_by || [])) add(x.name);
      for (const x of (info.neighbors.depends_on || [])) add(x.name);
    }
    for (const n of (extraNames || [])) add(n);
    const links = new Map();
    const shortCount = new Map();
    for (const n of full) { const s = shortName(n); shortCount.set(s, (shortCount.get(s) || 0) + 1); }
    for (const n of full) {
      links.set(n, n);
      const s = shortName(n);
      if (shortCount.get(s) === 1 && s.length > 2) links.set(s, n);
    }
    return links;
  }

  function neighborList(title, arrow, items) {
    return el("div", { className: "nb-col" }, [
      el("div", { className: "nb-hd", textContent: title + " " + arrow }),
      items && items.length
        ? el("ul", { className: "nb-list" }, items.slice(0, 8).map((x) => el("li", null, [
          el("a", { href: "#item/" + encodeURIComponent(x.name), title: x.name, textContent: shortName(x.name) }),
          x.rel ? el("span", { className: "nb-rel", textContent: EDGE_ROLE[x.rel === "type" ? "type" : (x.rel === "value" ? "value" : "both")] || x.rel }) : null
        ])).concat(items.length > 8 ? [el("li", { className: "nb-more", textContent: "and " + fmtInt(items.length - 8) + " more" })] : []))
        : el("p", { className: "nb-empty", textContent: "Not recorded for this declaration." })
    ]);
  }

  async function renderItemView(rawName) {
    const main = $("#appMain");
    clearEl(main);
    const name = String(rawName || "").trim();
    if (!name) { navigate("#search", true); return; }
    if (state.item.name !== name) { state.item.name = name; state.item.view = "summary"; }
    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Looking up " + shortName(name) + "…" })]));
    const info = await gatherItemInfo(name);
    if (state.route.tab !== "item" || currentItemName() !== name) return;
    clearEl(main);
    updateCrumbs(state.route);

    const gh = info.mod ? buildGithubUrl(info.mod, info.isModule ? null : info.line) : null;
    const meta = [
      info.kind || null,
      !info.isModule && info.mod ? info.mod + (info.line ? ":" + info.line : "") : null,
      info.dom ? fmtInt(info.dom) + " declarations in exclusive subtree" : null,
      info.live === 0 ? "unreachable" : null
    ].filter(Boolean).join(" · ");
    main.appendChild(el("header", { className: "item-head" }, [
      el("h1", { className: "item-title", textContent: info.short || name }),
      info.name !== info.short ? el("div", { className: "item-full", textContent: info.name }) : null,
      meta ? el("p", { className: "item-meta", textContent: meta }) : null,
      !info.found ? el("p", { className: "quiet-note", textContent: (xrefsBaseUrl() && !info.isModule
        ? "Not in the curated summary list; live cross-reference details load below."
        : "This name is not in the declaration index for this proof.") + (gh ? " The source link is inferred from its name." : "") }) : null,
      (!state.manifest.source_only && !state.manifest.demo_mode && info.found && !info.isModule && info.live !== 0)
        ? el("p", { className: "item-axioms", textContent: "Axioms: at most propext, Classical.choice and Quot.sound, with no sorryAx, inherited from the kernel check of the main theorems." })
        : null
    ]));

    if (!info.isModule) {
      const nb = info.neighbors || {};
      const strip = el("section", { className: "nb-strip", "aria-label": "Connections" }, [
        neighborList("Used by", "↑", nb.used_by),
        el("div", { className: "nb-col nb-self" }, [
          el("div", { className: "nb-hd", textContent: "This declaration" }),
          el("div", { className: "nb-self-name", textContent: info.short }),
          info.spine && info.spine.note ? el("p", { className: "nb-empty", textContent: info.spine.note }) : null
        ]),
        neighborList("Depends on", "↓", nb.depends_on)
      ]);
      main.appendChild(strip);
      const xBase = xrefsBaseUrl();
      if (xBase && window.LeanreXrefs) {
        window.LeanreXrefs.hydrateItemConnections(strip, {
          baseUrl: xBase,
          name: info.name,
          onNavigateXref: (n) => navigate("#xrefs/" + encodeURIComponent(n)),
          onNavigateItem: (n) => navigate("#item/" + encodeURIComponent(n))
        }).catch(() => {});
      }
    }

    const views = [["summary", "Summary"]];
    if (info.circuit) views.push(["diagram", "Diagram"]);
    if (gh) views.push(["source", "Lean Source"]);
    if (!info.isModule && ((state.manifest.assets || {}).embedding_2d || (state.manifest.assets || {}).atlas)) views.push(["twins", "Compare / Twins"]);
    views.push(["docs", "Dossiers"]);
    if (!views.some(([k]) => k === state.item.view)) state.item.view = "summary";
    const body = el("div", { className: "item-body", id: "itemBody" });
    main.appendChild(el("div", { className: "toolbar-row item-tabs" }, [
      el("div", { className: "seg", role: "tablist" }, views.map(([k, lbl]) => el("button", {
        type: "button", role: "tab", "aria-selected": state.item.view === k ? "true" : "false", className: state.item.view === k ? "active" : "", textContent: lbl,
        onclick: () => { state.item.view = k; renderItemView(name); }
      }))),
      el("div", { className: "spacer" }),
      gh && state.item.view !== "source" ? el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }) : null
    ]));
    main.appendChild(body);
    await renderItemBody(body, info, gh);
  }

  async function renderItemBody(body, info, gh) {
    const m = state.manifest || {};
    const view = state.item.view;
    if (view === "summary") {
      const kv = el("div", { className: "cir-ins-kv item-kv" });
      const add = (k, v) => { if (v == null || v === "") return; kv.appendChild(el("div", { className: "k", textContent: k })); kv.appendChild(el("div", { className: "v", textContent: String(v) })); };
      add("Full name", info.name);
      add("Kind", info.kind);
      add(info.isModule ? "File" : "Module", info.isModule ? String(info.mod).replace(/\./g, "/") + ".lean" : info.mod);
      add("Line", info.line);
      add("Exclusive subtree", info.dom ? fmtInt(info.dom) : "");
      if (info.spine) {
        add("Role", info.spine.role);
        add("Reached through", info.spine.idom);
      }
      add("Declarations", info.decls != null ? fmtInt(info.decls) : "");
      body.appendChild(kv);
      const acts = el("div", { className: "cir-ins-acts" });
      if (info.circuit) acts.appendChild(el("a", { className: "btn sm primary", href: "#circuit/" + info.circuit.mode + "/" + encodeURIComponent(info.circuit.short || info.circuit.name), textContent: "Open full diagram ›" }));
      if (info.bpId) acts.appendChild(el("a", { className: "btn sm", href: "#blueprints/" + encodeURIComponent(info.bpId), textContent: "Blueprint ›" }));
      acts.appendChild(el("a", { className: "btn sm", href: "#search/" + encodeURIComponent(info.short), textContent: "Search similar names ›" }));
      body.appendChild(acts);
      const docs = docsMentioning(info.short, false, info.name);
      if (docs.length) {
        body.appendChild(el("div", { className: "map-sub", textContent: "Mentioned in" }));
        body.appendChild(el("ul", { className: "item-docs" }, docs.slice(0, 8).map((d) => el("li", null, [el("a", { href: d.route, textContent: d.title + " ›" })]))));
      }
      return;
    }

    if (view === "diagram" && info.circuit) {
      const box = el("div", { className: "lens-box item-diagram" }, [el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading diagram…" })])]);
      body.appendChild(box);
      body.appendChild(el("div", { className: "cir-ins-acts" }, [el("a", { className: "btn sm primary", href: "#circuit/" + info.circuit.mode + "/" + encodeURIComponent(info.circuit.short || info.circuit.name), textContent: "Open full diagram ›" })]));
      try {
        const data = await fetchJson(info.circuit.path);
        const svgText = state.theme === "light" ? (data.svg_light || data.svg || data.svg_dark) : (data.svg_dark || data.svg || data.svg_light);
        mountSafeSvg(box, svgText || "");
      } catch (err) {
        clearEl(box);
        box.appendChild(el("p", { className: "cir-ins-note", textContent: "Could not load the diagram: " + String(err.message || err) }));
      }
      return;
    }

    if (view === "source" && gh) {
      let extra = [];
      if (info.circuit) {
        try {
          const data = await fetchJson(info.circuit.path);
          const p = data.payload || {};
          extra = (p.nodes || []).concat(p.binders || []).map((n) => n.full_name).filter(Boolean);
        } catch (_) { /* optional */ }
      }
      const host = el("div", { className: "item-source" });
      body.appendChild(host);
      await renderDockedSource(host, { url: gh, title: info.name, line: info.isModule ? null : info.line, links: buildKnownLinks(info, extra) });
      return;
    }

    if (view === "twins") {
      const host = el("div", { className: "item-twins" }, [el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Looking for relatives…" })])]);
      body.appendChild(host);
      const a = m.assets || {};
      const [emb, atlas] = await Promise.all([
        a.embedding_2d ? fetchJson(a.embedding_2d).catch(() => null) : null,
        a.atlas ? fetchJson(a.atlas).catch(() => null) : null
      ]);
      clearEl(host);
      const mySpec = { url: gh || "", title: info.name, line: info.line, label: "A" };
      let any = false;
      if (emb && emb.layers && emb.layers.landmarks) {
        const pts = map2dPoints(emb.layers.landmarks, "knn");
        const me = pts.find((p) => p.name === info.name);
        if (me && me.nn.length) {
          any = true;
          host.appendChild(el("div", { className: "map-sub", textContent: "Closest in vocabulary (2D map neighbors)" }));
          if (me.terms.length) host.appendChild(el("p", { className: "map-terms", textContent: "Its statement draws on: " + me.terms.slice(0, 6).join(" · ") }));
          host.appendChild(el("div", { className: "tray-list" }, me.nn.slice(0, 5).map((j) => {
            const q = pts[j];
            if (!q) return null;
            const qUrl = q.mod ? buildGithubUrl(q.mod, q.line) : "";
            return el("div", { className: "tray-row" }, [
              el("div", { className: "tray-main" }, [
                el("a", { className: "tray-name", href: "#item/" + encodeURIComponent(q.name), title: q.name, textContent: q.short }),
                el("span", { className: "tray-meta", textContent: [q.kind, q.dir, q.dom ? fmtInt(q.dom) + " in subtree" : null].filter(Boolean).join(" · ") })
              ]),
              el("div", { className: "cir-ins-acts" }, [
                el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(q.name), textContent: "Inspect ›" }),
                (isLeanBlob(gh) || isLeanBlob(qUrl)) ? el("button", { type: "button", className: "btn sm", textContent: "Compare side-by-side", onclick: () => openSourceCompare(mySpec, { url: qUrl || "", title: q.name, line: q.line, label: "B" }) }) : null
              ])
            ]);
          })));
        }
      }
      const al = atlas && atlas.alien_twins;
      if (al) {
        // Every sampled pool (low, partial and high overlap), deduplicated.
        const seen = new Set();
        const mine = [];
        for (const k of TWIN_POOL_KEYS) {
          for (const p of (Array.isArray(al[k]) ? al[k] : [])) {
            if (!p || !p.thm_a || !p.thm_b) continue;
            const key = [String(p.thm_a.name), String(p.thm_b.name)].sort().join("|");
            if (seen.has(key)) continue;
            seen.add(key);
            if (p.thm_a.name === info.name || p.thm_b.name === info.name) mine.push(p);
          }
        }
        mine.sort((x, y) => Number(x.jaccard || 0) - Number(y.jaccard || 0));
        if (mine.length) {
          any = true;
          host.appendChild(el("div", { className: "map-sub", textContent: "Paired proofs of the same statement" }));
          for (const p of mine) {
            // This declaration is always A; swap the pair when it is thm_b.
            const swap = p.thm_a.name !== info.name;
            const other = swap ? p.thm_a : p.thm_b;
            const os = atlasTwinSourceSpec(other, "B");
            const band = TWIN_BAND_SHORT[p.band] || "";
            const diffOpts = (extra) => Object.assign({ swap, specs: [mySpec, os] }, extra || {});
            host.appendChild(el("div", { className: "tray-row" }, [
              el("div", { className: "tray-main" }, [
                el("a", { className: "tray-name", href: "#item/" + encodeURIComponent(other.name), title: other.name, textContent: shortName(other.name) }),
                el("span", { className: "tray-meta", textContent: "overlap J = " + Number(p.jaccard || 0).toFixed(3) + (band ? " · " + band.toLowerCase() : "") + " · " + (other.origin === "project" ? "this project" : other.origin) }),
                p.proof_diff ? buildProofDiffBar(p.proof_diff, swap, { compact: true, onPick: (k) => openProofDiff(p, diffOpts({ filter: k })) }) : null
              ]),
              el("div", { className: "cir-ins-acts" }, [
                p.proof_diff ? el("button", { type: "button", className: "btn sm pdiff-open", textContent: "View diff", onclick: () => openProofDiff(p, diffOpts()) }) : null,
                el("button", { type: "button", className: "btn sm", textContent: "Compare side-by-side", onclick: () => openSourceCompare(mySpec, os, { pair: p, swap }) })
              ])
            ]));
          }
        }
      }
      if (!any) host.appendChild(el("p", { className: "cir-ins-note", textContent: "No close relatives were found for this declaration in the precomputed data." }));
      return;
    }

    if (view === "docs") {
      const host = el("div", { className: "item-docs-view" });
      body.appendChild(host);
      const quick = docsMentioning(info.short, false, info.name);
      host.appendChild(el("p", { className: "cir-ins-note", textContent: quick.length ? "Titles and summaries that mention " + info.short + ":" : "No title or summary mentions " + info.short + "." }));
      if (quick.length) host.appendChild(el("ul", { className: "item-docs" }, quick.map((d) => el("li", null, [el("a", { href: d.route, textContent: d.title + " ›" })]))));
      const all = docsMentioning("", true);
      if (all.length) {
        const out = el("div", { className: "item-docs-full" });
        const btn = el("button", {
          type: "button", className: "btn sm", textContent: "Search the full text of " + fmtInt(all.length) + " documents",
          onclick: async () => {
            btn.disabled = true;
            clearEl(out);
            const status = el("p", { className: "cir-ins-note", textContent: "Searching…" });
            out.appendChild(status);
            const rx = new RegExp("(^|[^A-Za-z0-9_'.])" + info.short.replace(/[.*+?^${}()|[\]\\]/g, "\\$&") + "(?![A-Za-z0-9_'])");
            const hits = [];
            let done = 0;
            for (const d of all) {
              try {
                const txt = await fetchText(d.path);
                const n = (txt.match(new RegExp(rx.source, "g")) || []).length;
                if (n) hits.push(Object.assign({ n }, d));
              } catch (_) { /* skip */ }
              done++;
              status.textContent = "Searched " + done + " of " + all.length + "…";
            }
            hits.sort((x, y) => y.n - x.n);
            status.textContent = hits.length ? "Found in " + hits.length + " documents:" : "Not mentioned in any document.";
            if (hits.length) out.appendChild(el("ul", { className: "item-docs" }, hits.map((d) => el("li", null, [el("a", { href: d.route, textContent: d.title + " ›" }), el("span", { className: "nb-rel", textContent: d.n + (d.n === 1 ? " mention" : " mentions") })]))));
          }
        });
        host.appendChild(btn);
        host.appendChild(out);
      }
    }
  }

  // Documents whose title or summary names `word` as a whole Lean token.
  // Short words (under five characters) match only as a full qualified name,
  // so "NoSuch.decl" does not match the English word "decl".
  function docsMentioning(word, all, fullName) {
    const m = state.manifest || {};
    const out = [];
    const esc = (s) => String(s).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    const tokRx = (s) => new RegExp("(^|[^\\p{L}\\p{N}_.'])" + esc(s) + "(?=$|[^\\p{L}\\p{N}_'])", "iu");
    const w = String(word || "");
    const full = String(fullName || "");
    const rxs = [];
    if (full && full !== w && full.includes(".")) rxs.push(tokRx(full));
    if (w.length >= 5) rxs.push(tokRx(w));
    const take = (d, route) => {
      const hay = (d.title || "") + " " + (d.summary || "");
      if (all || (rxs.length && rxs.some((rx) => rx.test(hay)))) out.push({ title: plainTextFromTex(d.title || d.slug), route, path: d.path });
    };
    for (const f of (m.findings || [])) take(f, "#findings/" + encodeURIComponent(f.slug));
    for (const d of (m.dossiers || [])) take(d, "#dossiers/" + encodeURIComponent(d.slug));
    for (const d of (m.research || [])) take(d, "#dossiers/research/" + encodeURIComponent(d.slug));
    return out;
  }

  function renderExperimentsView() {
    const main = $("#appMain");
    clearEl(main);
    main.appendChild(el("div", { className: "empty-card" }, [
      el("h3", { textContent: "This page has moved" }),
      el("p", { textContent: "The dependency views now live under Edge Map, and other formalizations are listed under Proofs." }),
      el("div", { className: "cir-ins-acts" }, [
        el("a", { className: "btn sm", href: "#atlas", textContent: "Edge Map ›" }),
        state.registry ? el("a", { className: "btn sm", href: "#projects", textContent: "Proofs ›" }) : null
      ])
    ]));
  }

  // ==========================================================================
  // CLUSTERS for source-only projects (flirt_tier1.json)
  // ==========================================================================
  function renderTier1Body(doc) {
    const main = $("#appMain");
    clearEl(main);
    const ms = doc.misfile_scoring || {};
    const mi = doc.mathlib_import_stats || {};
    const bp = doc.boilerplate_stats || {};
    const dup = Number((bp.alpha_body_clone || {}).redundant_modules || 0) + Number((bp.sigset_clone || {}).redundant_modules || 0);
    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Clusters" }),
      trustBadge("tool"),
      el("p", { className: "page-lede", textContent: "Files whose namespace, imports or vocabulary suggest they belong in a different folder, and modules that repeat each other. This is a source-only scan, so the signals come from names and imports rather than proofs." })
    ]));
    main.appendChild(el("section", { className: "kpi-strip" }, [
      { val: fmtInt(doc.file_count), label: "Files", sub: doc.total_lines_wc ? plural(doc.total_lines_wc, "line") : "" },
      { val: fmtInt(ms.alertable_misfiles_total || 0), label: "Possibly misfiled", sub: ms.alertable_pct_of_corpus != null ? ms.alertable_pct_of_corpus + "% of files" : "" },
      { val: fmtInt(mi.modules_importing_whole_mathlib || 0), label: "Import all of Mathlib", sub: "rather than specific modules" },
      { val: fmtInt(dup), label: "Near-duplicate modules", sub: "identical bodies or statement sets" }
    ].map((k) => el("div", { className: "kpi-card" }, [el("div", { className: "kpi-val", textContent: k.val }), el("div", { className: "kpi-label", textContent: k.label }), k.sub ? el("div", { className: "kpi-sub", textContent: k.sub }) : null]))));
    const allRows = doc.top_misfiles || [];
    const topicOf = (r) => (clusterToken(r.domain_observed) || "—") + " vs " + (clusterToken(r.domain_expected) || "—");
    if (allRows.length) {
      const LIMIT = 60;
      let showAll = false;
      const cols = [
        { key: "file", label: "File", get: (r) => r.module || r.file_path || null },
        { key: "ns", label: "Namespace vs folder", get: (r) => r.declared_ns || null },
        { key: "topic", label: "Topic: observed vs expected", get: (r) => (r.domain_observed || r.domain_expected ? topicOf(r) : null) },
        { key: "signal", label: "Signal", get: (r) => clusterToken(r.band) || null }
      ];
      const sort = tableSort("tier1-misfiles", { key: "", dir: "asc" });
      const tbody = el("tbody");
      const subEl = el("span", { className: "sub" });
      const moreBtn = allRows.length > LIMIT ? el("button", { type: "button", className: "btn sm", onclick: () => { showAll = !showAll; fill(); } }) : null;
      const fill = () => {
        clearEl(tbody);
        const sorted = sortRowsBy(allRows, cols, sort);
        (showAll ? sorted : sorted.slice(0, LIMIT)).forEach((r) => tbody.appendChild(el("tr", null, [
          el("td", null, [el("code", null, [identWbr(r.module || r.file_path || "—")]), r.file_path ? el("div", { className: "bp-anchor" }, [makeSourceLink(r.file_path, null, r.file_path, r.module)]) : null]),
          el("td", null, [el("code", null, [identWbr(r.declared_ns || "—")]), el("div", { className: "cir-ins-note mono" }, [identWbr(r.folder_ns || "")])]),
          el("td", { textContent: topicOf(r), title: [r.domain_observed, r.domain_expected].filter(Boolean).join(" vs ") || null }),
          el("td", { textContent: clusterToken(r.band) || "—", title: r.band || null })
        ])));
        subEl.textContent = allRows.length > LIMIT && !showAll ? "First " + LIMIT + " of " + fmtInt(allRows.length) : plural(allRows.length, "file");
        if (moreBtn) moreBtn.textContent = showAll ? "Show fewer" : "Show all " + fmtInt(allRows.length);
      };
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "Possibly misfiled" }), subEl, moreBtn]));
      main.appendChild(el("div", { className: "table-wrap" }, [el("table", { className: "data-table", id: "tier1MisfileTable" }, [
        sortableHead(cols, sort, () => fill()), tbody
      ])]));
      fill();
    }
    const BP_LABEL = { alpha_body_clone: "Identical proof bodies", sigset_clone: "Identical statement sets", import_shim: "Import-only shims", statement_wrapper: "Statement wrappers" };
    const bpRows = Object.keys(BP_LABEL).filter((k) => bp[k]);
    if (bpRows.length) {
      const n = (v) => { const x = Number(v); return v != null && Number.isFinite(x) ? x : null; };
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "Repetition" })]));
      main.appendChild(el("div", { className: "table-wrap" }, [simpleSortableTable("tier1-repetition", [
        { key: "pattern", label: "Pattern", get: (k) => BP_LABEL[k] },
        { key: "clusters", label: "Groups", num: true, get: (k) => n(bp[k].clusters) },
        { key: "modules", label: "Modules", num: true, get: (k) => n(bp[k].modules) },
        { key: "redundant", label: "Redundant", num: true, get: (k) => n(bp[k].redundant_modules) },
        { key: "largest", label: "Largest group", num: true, get: (k) => n(bp[k].largest_cluster) }
      ], bpRows, { key: "", dir: "desc" }, (k) => el("tr", null, [
        el("td", { textContent: BP_LABEL[k] }), el("td", { className: "num", textContent: fmtInt(bp[k].clusters) }), el("td", { className: "num", textContent: fmtInt(bp[k].modules) }),
        el("td", { className: "num", textContent: fmtInt(bp[k].redundant_modules) }), el("td", { className: "num", textContent: fmtInt(bp[k].largest_cluster) })
      ]))]));
    }
  }

  // ==========================================================================
  // VIEW 1: OVERVIEW
  // ==========================================================================
  // Trust boundary: tool output vs separately authored review notes.
  function trustBadge(kind, label) {
    if (kind === "notes") {
      return el("span", { className: "trust-badge notes", title: (state.manifest && state.manifest.source_only) ? "Loaded from the project's separate notes directory — independent commentary, not generated by the source scanner." : "Loaded from the project's separate notes directory — independent commentary, not generated by the kernel extractor or scanner.", textContent: "Review note · authored separately" });
    }
    return el("span", { className: "trust-badge tool", title: (state.manifest && state.manifest.source_only) ? "Computed by leanre's deterministic tools from the source scan." : "Computed by leanre's deterministic tools from the kernel export and the source scan.", textContent: label || "Generated by leanre" });
  }
  function docProvenance(d) {
    if (d && d.provenance) return d.provenance === "notes_layer" ? "notes" : "tool";
    const m = state.manifest || {};
    const nl = m.provenance && m.provenance.notes_layer;
    if (nl && typeof nl.enabled === "boolean") return nl.enabled ? "notes" : "tool";
    return m.source_only ? "tool" : "notes";
  }

  // Split text so that names of structures/theorems with their own diagram
  // become links to those diagrams (e.g. "OpenLiteratureStatements").
  function linkCircuitNames(text) {
    const circuits = (state.manifest && state.manifest.circuits) || {};
    const names = [];
    for (const b of (circuits.bundles || [])) if ((b.short || "").length > 6) names.push(["bundle", b.short]);
    for (const t of (circuits.theorems || [])) if ((t.short || "").length > 6) names.push(["theorem", t.short]);
    if (!names.length) return [String(text)];
    const byName = new Map(names.map(([mode, nm]) => [nm, mode]));
    const rx = new RegExp("\\b(" + names.map(([, nm]) => nm.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).sort((a, b) => b.length - a.length).join("|") + ")\\b", "g");
    const out = [];
    let last = 0;
    let mm;
    const src = String(text);
    while ((mm = rx.exec(src))) {
      if (mm.index > last) out.push(src.slice(last, mm.index));
      const nm = mm[1];
      out.push(el("a", { className: "inline-diagram", href: "#circuit/" + byName.get(nm) + "/" + encodeURIComponent(nm), title: "Open the diagram for " + nm, textContent: nm, onclick: (ev) => ev.stopPropagation() }));
      last = rx.lastIndex;
    }
    if (last < src.length) out.push(src.slice(last));
    return out;
  }

  function overviewLenses() {
    const m = state.manifest || {};
    const a = m.assets || {};
    const out = [["spine", "Spine"]];
    if (m.circuits && m.circuits.macro) out.push(["diagram", "Diagram"]);
    if (a.atlas || a.module_matrix) out.push(["edges", "Edge Map"]);
    if (a.embedding_2d) out.push(["map", "2D Map"]);
    return out;
  }

  async function renderOverviewLens(host, domTree) {
    const m = state.manifest || {};
    const a = m.assets || {};
    const lens = state.overviewLens;
    clearEl(host);
    if (lens === "spine") {
      host.appendChild(el("p", { className: "section-lede", textContent: m.source_only
        ? "Each bar counts the modules that can only be reached through that one (its dominator subtree in the import graph). Click a row to inspect it."
        : (pillarsCountModules(m)
          ? "Each bar counts the modules that can only be reached through that module (its dominator subtree in the import graph). Click a row to open the module import diagram."
          : "Each bar counts the declarations that can only be reached through that part (its dominator subtree). Click a row to inspect it.") }));
      host.appendChild(domTree);
      return;
    }
    const lede = el("p", { className: "section-lede" });
    const box = el("div", { className: "lens-box" }, [el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })])]);
    const more = el("div", { className: "cir-ins-acts" });
    host.appendChild(lede);
    host.appendChild(box);
    host.appendChild(more);
    try {
      if (lens === "diagram") {
        lede.textContent = "The repository map: the main theorems at the top and the parts they rest on below.";
        const data = await fetchJson(m.circuits.macro);
        if (state.overviewLens !== lens || !box.isConnected) return;
        const svgText = state.theme === "light" ? (data.svg_light || data.svg || data.svg_dark) : (data.svg_dark || data.svg || data.svg_light);
        mountSafeSvg(box, svgText || "");
        more.appendChild(el("a", { className: "btn sm", href: "#circuit/macro", textContent: "Open the full diagram ›" }));
      } else if (lens === "edges") {
        const canvas = el("canvas", { className: "atlas-canvas lens-canvas", "aria-label": "Edge map" });
        if (a.atlas) {
          lede.textContent = "Every dependency edge, ordered by the dominator tree. Brighter cells hold more edges; cyan cells are mostly statement edges and amber cells mostly proof edges.";
          const doc = await fetchJson(a.atlas);
          if (state.overviewLens !== lens || !box.isConnected) return;
          clearEl(box);
          box.appendChild(canvas);
          atlasDrawHicCanvas(canvas, doc.hic_matrix || {}, "ratio");
        } else {
          lede.textContent = "Imports between modules, ordered so that each folder sits in one block.";
          const mm = await fetchJson(a.module_matrix);
          if (state.overviewLens !== lens || !box.isConnected) return;
          clearEl(box);
          box.appendChild(canvas);
          drawModuleMatrix(canvas, mm, null);
        }
        more.appendChild(el("a", { className: "btn sm", href: "#atlas", textContent: "Open the Edge Map ›" }));
      } else if (lens === "map") {
        lede.textContent = "Declarations placed by the Mathlib vocabulary their statements use. Click a dot to see its neighbors.";
        clearEl(box);
        box.classList.add("lens-map");
        await mountMap2d(box, { compact: true });
        more.appendChild(el("a", { className: "btn sm", href: "#atlas/map", textContent: "Open the 2D Map ›" }));
      }
    } catch (err) {
      clearEl(box);
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Could not load this view: " + String(err.message || err) }));
    }
  }

  // Overview pillars count modules (import dominators) on source-only scans and
  // on projects whose pillars come from the module graph (no declaration names).
  function pillarsCountModules(m) {
    if (!m) return false;
    if (m.source_only) return true;
    const ps = Array.isArray(m.overview_pillars) ? m.overview_pillars : [];
    return ps.length > 0 && ps.every((p) => !p.decl && /\bmodules?\b/i.test(String(p.note || p.description || "")));
  }

  // Human title from the manifest (or registry) title on source-only scans:
  // "How the Fermat's Last Theorem (FLT) formalization fits together".
  function overviewTitle(m) {
    const reg = state.registry ? state.registry.projects.find((p) => p.slug === m.slug) : null;
    const label = [m.title, reg && reg.title].find((x) => x && !/leanre/i.test(String(x)));
    if (m.demo_mode) return "How the " + (label ? String(label).trim() : "Tiny Demo") + " formalization fits together";
    if (m.source_only && label) return "How the " + String(label).trim().replace(/^the\s+/i, "") + " formalization fits together";
    if (label && m.slug === "riemann-hypothesis") return "How the " + String(label).replace(/\s*\([^)]*\)\s*$/, "").trim() + " proof fits together";
    const repo = m.repo_name || "this repository";
    return "How the " + repo + " proof fits together";
  }

  // Review notes are present only when the notes layer is on; tool-generated
  // summaries alone do not count.
  function hasReviewNotes(m) {
    const nl = m && m.provenance && m.provenance.notes_layer;
    if (nl && typeof nl.enabled === "boolean") return nl.enabled;
    return Boolean((m.findings || []).length || (m.dossiers || []).length);
  }

  function renderOverview() {
    const main = $("#appMain");
    clearEl(main);
    const m = state.manifest || {};
    const st = m.stats || {};

    // Hero: one title, a two-sentence description computed from the manifest,
    // a quiet scope note, and three actions.
    const repo = m.repo_name || "this repository";
    const nFind = (m.findings || []).length;
    const nDos = (m.dossiers || []).length;
    const nBp = (m.blueprints || []).length;
    const docParts = [];
    if (nFind) docParts.push(plural(nFind, "finding"));
    if (nDos) docParts.push(plural(nDos, "dossier"));
    if (nBp) docParts.push(plural(nBp, "blueprint"));
    const joinList = (xs) => xs.length <= 1 ? (xs[0] || "") : xs.slice(0, -1).join(", ") + " and " + xs[xs.length - 1];
    const liveTxt = st.live_decls ? fmtInt(st.live_decls) + " reachable declarations" : "declarations";
    // Source-only scans map modules and imports, not declaration dependencies.
    const sentence1 = m.source_only
      ? "Maps how " + plural(st.total_files, "module") + " (" + plural(st.total_decls, "source declaration") + ") connect across " + plural(st.edges, "module import") + ", tracking axioms and sorrys."
      : "This site maps how the " + liveTxt + " in " + repo + " depend on one another, which parts carry the weight of the proof, and which hypotheses are actually used.";
    const sentence2 = docParts.length
      ? "It collects " + joinList(docParts) + ", and every diagram and table links to the exact line of Lean source at a pinned commit."
      : "Every diagram and table links to the exact line of Lean source at a pinned commit.";

    const heroActions = el("div", { className: "hero-actions" }, [
      (m.circuits && m.circuits.macro) ? el("a", { className: "btn primary", href: "#circuit", textContent: "Explore diagrams ›" }) : null,
      nFind ? el("a", { className: "btn", href: "#findings", textContent: "Read findings ›" }) : null,
      el("a", { className: "btn", href: "#search", textContent: "Search declarations ›" }),
      state.registry && projectList().length > 1 ? el("a", { className: "btn quiet", href: "#projects", textContent: "All " + projectList().length + " proofs ›" }) : null
    ]);

    const scopeNote = m.scope_note || (m.repo_name === "riemann-hypothesis"
      ? "Scope: the 5 headline theorems concern ζ(s) and Dirichlet L-functions over ℚ only, not Dedekind or Hecke L-functions; the author folder named DedekindLFunctions is a misnomer."
      : "");
    main.appendChild(el("section", { className: "hero" }, [
      el("h1", { textContent: overviewTitle(m) }),
      el("p", { className: "hero-sub", textContent: sentence1 + " " + sentence2 }),
      scopeNote ? el("p", { className: "hero-scope", textContent: plainTextFromTex(scopeNote) }) : null,
      m.source_only
        ? el("p", { className: "hero-note", role: "note", textContent: "Note: this is a source-only scan. Nothing here was checked by Lean's kernel, and none of it is independent mathematical peer review." })
        : el("p", { className: "hero-note", role: "note" }, [
          "Note: passing Lean's kernel confirms the logic under the standard axioms (",
          el("code", { textContent: "propext" }), ", ",
          el("code", { textContent: "Classical.choice" }), ", ",
          el("code", { textContent: "Quot.sound" }),
          "); it is not independent mathematical peer review."
        ]),
      el("p", { className: "trust-line" }, [trustBadge("tool"), hasReviewNotes(m)
        ? el("span", { textContent: " Numbers, diagrams and maps here are computed by leanre. Findings and dossiers are review notes, written separately." })
        : el("span", { textContent: " Numbers, diagrams and maps here are computed by leanre." })]),
      heroActions
    ]));

    // Key numbers
    const cir = m.circuits || {};
    const nB = (cir.bundles || []).length, nT = (cir.theorems || []).length;
    const nCir = nB + nT + (cir.macro ? 1 : 0);
    const kTotal = Number(st.kernel_total_decls) || 0;
    const reachSub = kTotal && st.total_decls && kTotal !== Number(st.total_decls)
      ? "of " + plural(kTotal, "kernel declaration") + " (" + fmtInt(st.total_decls) + " in source)"
      : (st.total_decls ? "of " + fmtInt(st.total_decls) + " in total" : "");
    const kpis = [
      { label: "Reachable declarations", val: fmtInt(st.live_decls), sub: reachSub },
      { label: "Unreachable", val: fmtInt(st.dead_decls), sub: m.source_only ? "in modules not imported from the entry module" : "not reached from the main theorems" },
      { label: m.source_only ? "Module import edges" : "Dependency edges", val: fmtInt(st.edges), sub: plural(st.total_files, "file") + " · " + plural(st.total_lines, "line") },
      { label: nCir === 1 ? "Diagram" : "Diagrams", val: fmtInt(nCir), sub: (nB || nT) ? plural(nB, "structure") + " · " + plural(nT, "theorem") : (cir.macro ? "Module map" : "") }
    ];
    main.appendChild(el("section", { className: "kpi-strip", "aria-label": "Key numbers" }, kpis.map((k) =>
      el("div", { className: "kpi-card" }, [
        el("div", { className: "kpi-val", textContent: k.val }),
        el("div", { className: "kpi-label", textContent: k.label }),
        k.sub ? el("div", { className: "kpi-sub", textContent: k.sub }) : null
      ])
    )));

    // Two-column Overview: Dominator Hierarchy + Showcase Proof Circuits
    const pillars = Array.isArray(m.overview_pillars) ? m.overview_pillars : [];
    const barBase = pillarsCountModules(m) ? Number(st.total_files) || 0 : Number(st.live_decls) || 0;
    const maxCount = Math.max(1, barBase, ...pillars.map((p) => Number(p.count || p.dom || p.subtree_size || 0)));

    const domTree = el("div", { className: "dom-tree" });
    if (pillars.length) {
      pillars.forEach((p, idx) => {
        const cnt = Number(p.count ?? p.dom ?? p.subtree_size ?? 0);
        const pct = Math.max(1.5, Math.min(100, (cnt / maxCount) * 100));
        const depth = Number(p.depth || 0);
        const target = p.circuit_target || p.target || p.decl || p.name || "";
        const declName = p.decl || "";
        const circuitHit = (p.circuit_mode && target)
          ? (findCircuitEntry(p.circuit_mode, target) || findAnyCircuitForSymbol(target))
          : (target ? findAnyCircuitForSymbol(target) : null);
        const rowHref = declName ? "#item/" + encodeURIComponent(declName)
          : (circuitHit ? "#circuit/" + circuitHit.mode + "/" + encodeURIComponent(circuitHit.short || circuitHit.name) : "");
        const desc = (p.note || p.description || "") + (p.role === "diamond" ? " · exclusive subtree only; the shared core in Diagrams is larger because it counts every declaration used by two or more pillars" : "");
        const fillCls = idx === 0 ? "emerald" : (String(p.role || p.label || p.name || "").toLowerCase().includes("diamond") ? "amber" : (depth >= 2 ? "teal" : ""));
        const row = el("div", {
          className: "dom-row" + (rowHref ? " clickable" : ""),
          role: rowHref ? "link" : null,
          tabindex: rowHref ? "0" : null,
          title: rowHref ? (declName ? "Inspect " + declName : (circuitHit.mode === "macro" ? (pillarsCountModules(m) ? "Open the module import diagram" : "Open the repository diagram") : "Open the diagram for " + circuitHit.name)) : (desc || p.label || p.name || ""),
          onclick: rowHref ? () => navigate(rowHref) : null,
          onkeydown: rowHref ? (ev) => { if (ev.key === "Enter") navigate(rowHref); } : null
        }, [
          el("div", { className: "dom-name" }, [
            depth > 0 ? el("span", { className: "indent", textContent: "  ".repeat(Math.min(depth, 4)) + "└─" }) : null,
            el("div", { style: { minWidth: "0" } }, [
              el("div", { className: "lbl" }, [identWbr(p.label || p.name || target || "node")]),
              desc ? el("div", { className: "sub-note" }, linkCircuitNames(desc)) : null
            ])
          ]),
          el("div", { className: "dom-bar-track" }, [
            el("div", { className: "dom-bar-fill " + fillCls, style: { width: pct.toFixed(1) + "%" } })
          ]),
          el("div", { className: "dom-count", textContent: fmtInt(cnt) + (p.pct_live != null ? " (" + Number(p.pct_live).toFixed(0) + "%)" : "") }),
          el("span", { className: "nav-glyph", "aria-hidden": "true", textContent: rowHref ? "›" : "" })
        ]);
        domTree.appendChild(row);
      });
    } else {
      domTree.appendChild(el("div", { className: "empty-card" }, [
        el("p", { textContent: "No breakdown of the main parts is available. The repository map in Diagrams shows the roots and their clusters." })
      ]));
    }

    // Showcase Proof Circuits Launchpad
    const showcaseGrid = el("div", { className: "showcase-chips" });
    const addedKeys = new Set();
    const pushShowcase = (mode, target, label, desc, tag, colorCls) => {
      const k = mode + ":" + target;
      if (addedKeys.has(k)) return;
      addedKeys.add(k);
      showcaseGrid.appendChild(el("button", {
        type: "button",
        className: "showcase-btn",
        onclick: () => {
          if (mode === "macro") navigate("#circuit/macro");
          else navigate("#circuit/" + mode + "/" + encodeURIComponent(target));
        }
      }, [
        el("div", { className: "sc-top" }, [
          el("span", { className: "sc-title", textContent: label }),
          el("span", { className: "sc-tag", textContent: tag + " ›" })
        ]),
        el("div", { className: "sc-sub", textContent: desc })
      ]));
    };

    for (const sc of SHOWCASE_ORDER) {
      const hit = findCircuitEntry(sc.mode, sc.target);
      if (hit) {
        pushShowcase(sc.mode, hit.short || hit.name || "", sc.label, sc.desc, sc.tag);
      }
    }
    // Fill up with available structures/theorems on generic/demo repos
    if (addedKeys.size < 6 && m.circuits) {
      for (const b of (m.circuits.bundles || []).slice(0, 4)) {
        pushShowcase("bundle", b.short || b.name, b.short || shortName(b.name), plural(b.fields || 0, "field") + " · used by " + fmtInt(b.consumers || 0), "Structure");
      }
      for (const t of (m.circuits.theorems || []).slice(0, 4)) {
        pushShowcase("theorem", t.short || t.name, t.short || shortName(t.name), plural(t.steps || 0, "proof step"), "Theorem");
      }
    }

    const lenses = overviewLenses();
    if (!lenses.some(([k]) => k === state.overviewLens)) state.overviewLens = "spine";
    const lensBody = el("div", { className: "lens-body", id: "lensBody" });
    const lensSeg = el("div", { className: "seg", role: "tablist", "aria-label": "View" }, lenses.map(([k, lbl]) => el("button", {
      type: "button", role: "tab", "aria-selected": state.overviewLens === k ? "true" : "false", className: state.overviewLens === k ? "active" : "", textContent: lbl,
      onclick: () => {
        state.overviewLens = k;
        $$("button", lensSeg).forEach((b) => { const on = b.textContent === lbl; b.classList.toggle("active", on); b.setAttribute("aria-selected", on ? "true" : "false"); });
        renderOverviewLens(lensBody, domTree);
      }
    })));
    main.appendChild(el("section", { className: "overview-grid" }, [
      el("div", { className: "panel lens-panel" }, [
        el("div", { className: "section-hdr lens-hd", style: { marginTop: "0" } }, [
          el("h2", { textContent: "At a glance" }),
          lenses.length > 1 ? lensSeg : null
        ]),
        lensBody
      ]),
      el("div", { className: "panel" }, [
        el("div", { className: "section-hdr", style: { marginTop: "0" } }, [
          el("h2", { textContent: "Places to start" })
        ]),
        el("p", { className: "section-lede", textContent: "Selected diagrams. Drag to pan and scroll to zoom once inside." }),
        showcaseGrid
      ])
    ]));
    renderOverviewLens(lensBody, domTree);

    // Findings
    const findings = Array.isArray(m.findings) ? m.findings : [];
    if (findings.length) {
      main.appendChild(el("div", { className: "section-hdr" }, [
        el("h2", { textContent: "Findings" }),
        el("a", { className: "sub", href: "#findings", textContent: "All findings ›" })
      ]));
      main.appendChild(el("section", { className: "findings-cards" }, findings.map((f) =>
        el("button", {
          type: "button",
          className: "finding-card",
          onclick: () => navigate("#findings/" + encodeURIComponent(f.slug))
        }, [
          el("div", { className: "fc-title" }, [renderTextWithTex(f.title || f.slug), el("span", { className: "nav-glyph", "aria-hidden": "true", textContent: " ›" })]),
          f.summary ? el("div", { className: "fc-sum", textContent: plainTextFromTex(f.summary) }) : null
        ])
      )));
    }
  }

  // ==========================================================================
  // VIEW 2: INTERACTIVE 3-LEVEL PROOF CIRCUIT VIEWER
  // ==========================================================================
  function applyCircuitTransform() {
    const stg = $("#cirStage");
    if (!stg) return;
    state.circuit.userMoved = true;
    stg.style.transform = "translate(" + state.circuit.tx.toFixed(1) + "px," + state.circuit.ty.toFixed(1) + "px) scale(" + state.circuit.scale.toFixed(3) + ")";
  }

  // Full screen keeps the region the reader zoomed into (centered), instead of refitting.
  function rememberCircuitViewport() {
    const wrap = $("#cirStageWrap");
    if (wrap) state.circuit.vp = { w: wrap.clientWidth, h: wrap.clientHeight };
  }
  function keepCircuitViewport() {
    const wrap = $("#cirStageWrap");
    const vp = state.circuit.vp;
    if (!wrap || !vp || !state.circuit.userMoved) { fitCircuitStage(); return; }
    state.circuit.tx += (wrap.clientWidth - vp.w) / 2;
    state.circuit.ty += (wrap.clientHeight - vp.h) / 2;
    applyCircuitTransform();
  }

  function zoomCircuitAt(factor, mx, my) {
    const ns = Math.max(0.16, Math.min(4.0, state.circuit.scale * factor));
    state.circuit.tx = mx - (mx - state.circuit.tx) * (ns / state.circuit.scale);
    state.circuit.ty = my - (my - state.circuit.ty) * (ns / state.circuit.scale);
    state.circuit.scale = ns;
    applyCircuitTransform();
  }

  function showCircuitZoomHint(wrap) {
    let hint = wrap.querySelector(".cir-zoom-hint");
    if (!hint) {
      hint = el("div", { className: "cir-zoom-hint", "aria-hidden": "true", textContent: "Ctrl/⌘ + scroll or double-click to zoom" });
      wrap.appendChild(hint);
    }
    hint.classList.add("show");
    clearTimeout(hint._t);
    hint._t = setTimeout(() => hint.classList.remove("show"), 1400);
  }

  function clearCircuitSelection() {
    const had = Boolean(state.circuit.selectedItem);
    $$("#cirStage .circuit-node.selected, #cirStage .circuit-pin.selected").forEach((x) => x.classList.remove("selected"));
    state.circuit.selectedItem = null;
    if (had) renderCircuitInspector(null, false);
    return had;
  }

  function circuitHref(entry) {
    if (!entry) return "#circuit/macro";
    return entry.mode === "macro" ? "#circuit/macro" : "#circuit/" + entry.mode + "/" + encodeURIComponent(entry.short || entry.name);
  }

  function fitCircuitStage() {
    const wrap = $("#cirStageWrap");
    const stg = $("#cirStage");
    if (!wrap || !stg) return;
    const svg = stg.querySelector("svg");
    if (!svg) return;
    const vb = svg.viewBox && svg.viewBox.baseVal;
    const sw = (vb && vb.width) || Number(svg.getAttribute("width")) || 1200;
    const sh = (vb && vb.height) || Number(svg.getAttribute("height")) || 760;
    const cw = wrap.clientWidth || 1000;
    const ch = wrap.clientHeight || 560;
    const sc = Math.max(0.18, Math.min(1.25, Math.min((cw - 18) / sw, (ch - 18) / sh)));
    state.circuit.scale = sc;
    state.circuit.tx = Math.max(8, (cw - sw * sc) / 2);
    state.circuit.ty = Math.max(8, (ch - sh * sc) / 2);
    applyCircuitTransform();
    state.circuit.userMoved = false;
  }

  function applyCircuitNodeHighlight() {
    const stg = $("#cirStage");
    if (!stg) return;
    const q = (state.circuit.filter || "").trim().toLowerCase();
    const payload = (state.circuit.data && state.circuit.data.payload) || {};
    const byId = new Map();
    for (const n of (payload.nodes || [])) byId.set(n.id, n);
    for (const b of (payload.binders || [])) byId.set(b.id, b);

    $$(".circuit-node", stg).forEach((g) => {
      const nid = g.getAttribute("data-node-id") || "";
      const obj = byId.get(nid) || {};
      const hay = ((obj.label || "") + " " + (obj.full_name || "") + " " + (obj.tooltip || "") + " " + (obj.badge || "") + " " + (obj.type || "")).toLowerCase();
      const hit = q ? hay.includes(q) : false;
      g.classList.toggle("dim", Boolean(q && !hit));
      g.classList.toggle("hl", hit);
    });
    $$(".circuit-pin", stg).forEach((g) => {
      const pn = g.getAttribute("data-pin") || "";
      const hit = q ? pn.toLowerCase().includes(q) : false;
      g.classList.toggle("dim", Boolean(q && !hit));
      g.classList.toggle("hl", hit);
    });
  }

  function renderCircuitInspector(item, isHover) {
    const box = $("#cirInspector");
    if (!box) return;
    clearEl(box);

    const cdata = state.circuit.data;
    const payload = (cdata && cdata.payload) || null;
    if (!payload) {
      box.appendChild(el("div", { className: "cir-ins-hd" }, [el("span", { textContent: "Details" })]));
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Click a node or a field to see its details and source." }));
      return;
    }

    const meta = payload.meta || {};
    const stats = payload.stats || {};
    const targetInfo = meta.target_info || {};
    const modeKey = String(payload.mode || state.circuit.mode);

    box.appendChild(el("div", { className: "cir-ins-hd" }, [
      el("span", { textContent: isHover ? "Preview" : (item ? "Selected" : "Summary") }),
      el("span", { className: "cir-ins-mode", textContent: MODE_LABEL[modeKey] || modeKey }),
      item && !isHover ? el("button", { type: "button", className: "icon-btn cir-ins-clear", "aria-label": "Clear selection", title: "Clear selection (Esc)", textContent: "×", onclick: clearCircuitSelection }) : null
    ]));

    if (!item) {
      box.appendChild(el("div", { className: "cir-ins-title", textContent: payload.target || payload.title || "Repository map" }));
      const topAnchor = (payload.pins && payload.pins.anchor) || meta.anchor || targetInfo.anchor || "";
      if (topAnchor) {
        box.appendChild(el("div", { className: "cir-ins-note" }, ["Source: ", makeSourceLink(topAnchor, null, null, payload.target || payload.title)]));
      }

      const kv = el("div", { className: "cir-ins-kv" });
      const addKv = (k, v) => {
        if (v == null || v === "") return;
        kv.appendChild(el("div", { className: "k", textContent: k }));
        kv.appendChild(el("div", { className: "v", textContent: String(v) }));
      };
      addKv("Nodes / links", fmtInt(stats.node_count) + " / " + fmtInt(stats.wire_count));
      if (payload.mode === "macro") {
        addKv("Reachable", fmtInt(stats.live_decls) + " (" + fmtInt(stats.dead_decls) + " unreachable)");
        if (stats.shared_diamond_decls != null) {
          addKv("Shared core", fmtInt(stats.shared_diamond_decls) + ((state.manifest || {}).source_only ? " modules" : " declarations"));
          const dm = ((state.manifest || {}).overview_pillars || []).find((p) => p.role === "diamond");
          if (dm && Number(dm.subtree_size)) addKv("Not the same as", "the Overview's shared diamond (" + fmtInt(dm.subtree_size) + "), which counts only declarations reached exclusively below the main waist; the shared core counts every declaration used by two or more of the four pillars");
        }
        if (stats.motif_clusters_count != null) addKv("Repeated shapes", fmtInt(stats.motif_clusters_count));
        if (stats.excluded_trivial_shells) addKv("Hidden", fmtInt(stats.excluded_prop_shells) + " Prop · " + fmtInt(stats.excluded_trivial_shells) + " trivial wrappers");
      } else if (payload.mode === "bundle") {
        addKv("Fields", fmtInt(stats.total_fields) + " (" + fmtInt(stats.projected_fields) + " used, " + fmtInt(stats.unread_fields) + " unused)");
        addKv("Conditional", fmtInt(stats.conditional_prop_fields) + " · trivially True: " + fmtInt(stats.literal_true_fields));
        addKv("Built by", fmtInt(stats.producers_total));
        addKv("Used by", fmtInt(stats.consumers_total) + " (" + fmtInt(stats.consumers_dropped_input) + " ignore it)");
      } else if (payload.mode === "theorem") {
        addKv("Kind", stats.decl_kind || "—");
        addKv("Hypotheses", fmtInt(stats.binders_used) + " used · " + fmtInt(stats.binders_dropped) + " unused");
        addKv("Proof steps", fmtInt(stats.steps_count));
        addKv("Used by / uses", fmtInt(stats.fan_in) + " / " + fmtInt(stats.fan_out));
        if (meta.sighash) addKv("Signature hash", meta.sighash);
      }
      box.appendChild(kv);
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Click a node to see its details and source; double-click it to open its own diagram where there is one. Drag to pan; Ctrl/⌘ + scroll or double-click the background to zoom." }));
      return;
    }

    // Specific Node or Pin Inspector
    const title = circuitPlainLabel(item.full_name || item.name || item.label || item.id || "");
    box.appendChild(el("div", { className: "cir-ins-title", textContent: title }));

    const pillRow = el("div", { className: "cir-ins-acts" });
    if (item.kind) pillRow.appendChild(el("span", { className: "pill", textContent: circuitPlainLabel(item.kind) }));
    if (item.status) {
      const sCls = ["dropped", "dangling", "literal_true", "true_slot"].includes(item.status)
        ? "crimson"
        : (["conditional_prop", "default_zero", "le_refl"].includes(item.status) ? "amber" : (item.status === "unread" || item.status === "trivial_shell" ? "slate" : "emerald"));
      pillRow.appendChild(el("span", { className: "pill " + sCls, textContent: String(item.status).replace(/_/g, " ") }));
    }
    if (item.badge && circuitPlainLabel(item.badge) !== circuitPlainLabel(item.kind)) pillRow.appendChild(el("span", { className: "pill", textContent: circuitPlainLabel(item.badge) }));
    box.appendChild(pillRow);

    const anchor = item.anchor || (item._isPin ? (targetInfo.anchor || "") : (item.line_no && meta.anchor ? meta.anchor.replace(/:\d+$/, ":" + item.line_no) : ""));
    if (anchor) {
      box.appendChild(el("div", { className: "cir-ins-note" }, ["Source: ", makeGithubAnchor(anchor)]));
    }

    // Diagrams available for this node
    const zt = item.zoom_target || null;
    const pivot = (zt && zt.target) || item.full_name || item.name || "";
    const acts = el("div", { className: "cir-ins-acts" });
    const drill = (state.circuit.drillMap && state.circuit.drillMap.get(item)) || null;
    const bundleHit = pivot ? findCircuitEntry("bundle", pivot) : null;
    const thmHit = pivot ? findCircuitEntry("theorem", pivot) : null;
    const sameEntry = (a, b) => a && b && a.mode === b.mode && (a.name || a.short) === (b.name || b.short);
    const DRILL_LABEL = { bundle: "Open structure diagram ›", theorem: "Open theorem diagram ›", macro: "Open repository diagram ›" };
    if (drill) {
      acts.appendChild(el("a", { className: "btn sm primary cir-drill", href: circuitHref(drill), title: "Or double-click the node", textContent: DRILL_LABEL[drill.mode] || "Open diagram ›" }));
    }
    if (bundleHit && !sameEntry(bundleHit, drill)) {
      acts.appendChild(el("a", { className: "btn sm" + (drill ? "" : " primary"), href: circuitHref(bundleHit), textContent: DRILL_LABEL.bundle }));
    }
    if (thmHit && !sameEntry(thmHit, drill)) {
      acts.appendChild(el("a", { className: "btn sm" + (drill || bundleHit ? "" : " primary"), href: circuitHref(thmHit), textContent: DRILL_LABEL.theorem }));
    }
    if (!item._isPin && (item.full_name || item.name)) {
      acts.appendChild(el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(item.full_name || item.name), textContent: "Inspect ›" }));
    }
    if (anchor) {
      const gh = buildGithubUrl(anchor);
      if (gh) {
        const known = new Map();
        for (const n of ((cdata && cdata.payload && cdata.payload.nodes) || [])) if (n.full_name) { known.set(n.full_name, n.full_name); known.set(shortName(n.full_name), n.full_name); }
        const peek = makeSrcButton(gh, title, { className: "btn sm", text: "Show source inline", links: known });
        if (peek) acts.appendChild(peek);
        acts.appendChild(el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }));
      }
    }
    if (acts.childNodes.length) box.appendChild(acts);
    else if (pivot && !item._isPin) {
      box.appendChild(el("div", { className: "cir-ins-note", textContent: "There is no separate diagram for this declaration." }));
    }

    const kv = el("div", { className: "cir-ins-kv" });
    const addKv = (k, v) => {
      if (v == null || v === "") return;
      kv.appendChild(el("div", { className: "k", textContent: k }));
      kv.appendChild(el("div", { className: "v", textContent: String(v) }));
    };
    const m = item.metrics || {};
    if (item._isPin) {
      addKv("Status", String(item.status || "").replace(/_/g, " "));
      addKv("Used", item.projected ? "yes" : "no (never read)");
      if (item.fan_in != null) addKv("Read by", fmtInt(item.fan_in));
      if (item.is_conditional_prop) addKv("Form", "conditional, P → Q");
      if (item.is_literal_true) addKv("Form", "trivially True");
      if (item.type) addKv("Type", item.type);
    } else {
      if (item.type) addKv("Type", item.type);
      if (item.line_no != null) addKv("Line", "L" + item.line_no);
      if (m.subtree_size != null) addKv("Exclusive subtree", fmtInt(m.subtree_size) + (m.pct_live != null ? " (" + m.pct_live + "%)" : ""));
      if (m.dom_subtree_size != null && m.subtree_size == null) addKv("Exclusive subtree", fmtInt(m.dom_subtree_size));
      if (m.fan_in != null) addKv("Used by", fmtInt(m.fan_in));
      if (m.fan_out != null) addKv("Uses", fmtInt(m.fan_out));
      if (m.is_trivial_shell) addKv("Wrapper", (m.shell_label || "Prop") + " (hidden)");
      else if (item.k1n_count != null || m.k1n_count != null) addKv("Same-shape copies", "×" + fmtInt(item.k1n_count ?? m.k1n_count));
      if (m.total_fields != null) addKv("Fields", fmtInt(m.projected) + " used · " + fmtInt(m.unread) + " unused");
      if (item.drops_target) addKv("Note", "its input is never used");
      if (item.producer_role) addKv("Role", item.producer_role);
      if (item.tooltip) addKv("Summary", item.tooltip);
    }
    box.appendChild(kv);
  }

  function wireCircuitStageEvents() {
    const wrap = $("#cirStageWrap");
    if (!wrap || wrap.dataset.wired === "1") return;
    wrap.dataset.wired = "1";
    let dragging = false, sx = 0, sy = 0, otx = 0, oty = 0;

    wrap.addEventListener("pointerdown", (ev) => {
      if (ev.pointerType === "touch") return;
      if (ev.button !== 0) return;
      dragging = true;
      sx = ev.clientX;
      sy = ev.clientY;
      otx = state.circuit.tx;
      oty = state.circuit.ty;
      state.circuit.dragMoved = 0;
      wrap.classList.add("dragging");
    });
    window.addEventListener("pointermove", (ev) => {
      if (!dragging) return;
      const dx = ev.clientX - sx;
      const dy = ev.clientY - sy;
      state.circuit.dragMoved = Math.max(state.circuit.dragMoved, Math.hypot(dx, dy));
      state.circuit.tx = otx + dx;
      state.circuit.ty = oty + dy;
      applyCircuitTransform();
    });
    window.addEventListener("pointerup", () => {
      if (!dragging) return;
      dragging = false;
      wrap.classList.remove("dragging");
    });
    attachTouchGestures(wrap, {
      noCapture: true,
      start: () => { state.circuit.dragMoved = 0; },
      pan: (dx, dy) => { state.circuit.dragMoved += Math.hypot(dx, dy); state.circuit.tx += dx; state.circuit.ty += dy; applyCircuitTransform(); },
      pinch: (f, x, y) => {
        const rect = wrap.getBoundingClientRect();
        const mx = x - rect.left, my = y - rect.top;
        const ns = Math.max(0.16, Math.min(40, state.circuit.scale * f));
        state.circuit.tx = mx - (mx - state.circuit.tx) * (ns / state.circuit.scale);
        state.circuit.ty = my - (my - state.circuit.ty) * (ns / state.circuit.scale);
        state.circuit.scale = ns;
        state.circuit.dragMoved = 99;
        applyCircuitTransform();
      },
      doubleTap: () => fitCircuitStage()
    });
    // Plain wheel scrolls the page; Ctrl/⌘ + wheel (and trackpad pinch) zooms.
    // In full screen there is no page to scroll, so the wheel zooms.
    wrap.addEventListener("wheel", (ev) => {
      if (!wrap.closest(".fs-on") && !(ev.ctrlKey || ev.metaKey)) { showCircuitZoomHint(wrap); return; }
      ev.preventDefault();
      const rect = wrap.getBoundingClientRect();
      zoomCircuitAt(ev.deltaY < 0 ? 1.12 : 0.89, ev.clientX - rect.left, ev.clientY - rect.top);
    }, { passive: false });
    wrap.addEventListener("dblclick", (ev) => {
      if (ev.target.closest && ev.target.closest(".circuit-node[data-drill='1']")) return;
      ev.preventDefault();
      const rect = wrap.getBoundingClientRect();
      zoomCircuitAt(ev.shiftKey ? 1 / 1.6 : 1.6, ev.clientX - rect.left, ev.clientY - rect.top);
    });
    wrap.addEventListener("click", (ev) => {
      if (state.circuit.dragMoved > 4) return;
      if (ev.target.closest && ev.target.closest(".circuit-node, .circuit-pin, .cir-zoom-hint")) return;
      clearCircuitSelection();
    });
  }

  function mountActiveCircuitSvg() {
    const stg = $("#cirStage");
    const cdata = state.circuit.data;
    if (!stg || !cdata) return;
    const svgText = state.theme === "light"
      ? (cdata.svg_light || cdata.svg || cdata.svg_dark || "")
      : (cdata.svg_dark || cdata.svg || cdata.svg_light || "");

    const svgEl = mountSafeSvg(stg, svgText);
    if (!svgEl) return;

    const payload = cdata.payload || {};
    const nodeById = new Map();
    for (const n of (payload.nodes || [])) nodeById.set(n.id, n);
    for (const b of (payload.binders || [])) nodeById.set(b.id, b);
    const pinByName = new Map();
    const chip = (payload.nodes || []).find((n) => n.kind === "chip");
    if (chip && Array.isArray(chip.pins)) {
      for (const p of chip.pins) pinByName.set(p.name, Object.assign({ _isPin: true }, p));
    }

    const tip = $("#circuitTip");
    const showTip = (txt, ev) => {
      if (!tip) return;
      tip.textContent = txt;
      tip.style.display = "block";
      tip.style.left = Math.min(window.innerWidth - 440, ev.clientX + 14) + "px";
      tip.style.top = Math.min(window.innerHeight - 100, ev.clientY + 14) + "px";
    };
    const hideTip = () => { if (tip) tip.style.display = "none"; };

    const drillMap = new Map();
    state.circuit.drillMap = drillMap;
    const drillTarget = (g, obj) => {
      let zmode = g.getAttribute("data-zoom-mode") || (obj.zoom_target && obj.zoom_target.mode) || "";
      const ztgt = g.getAttribute("data-zoom-target") || (obj.zoom_target && obj.zoom_target.target) || obj.full_name || "";
      if (!zmode || !ztgt) return null;
      if (state.circuit.mode === "macro" && obj.metrics && obj.metrics.sample_kind === "inductive") zmode = "bundle";
      const pre = findCircuitEntry(zmode, ztgt) || findAnyCircuitForSymbol(ztgt);
      if (!pre || (pre.mode === state.circuit.mode && (pre.name === state.circuit.target || pre.short === state.circuit.target))) return null;
      return pre;
    };

    $$(".circuit-node", svgEl).forEach((g) => {
      const nid = g.getAttribute("data-node-id") || "";
      const obj = nodeById.get(nid) || { id: nid, label: nid };
      const pre = drillTarget(g, obj);
      if (pre) { drillMap.set(obj, pre); g.setAttribute("data-drill", "1"); }
      g.addEventListener("mouseenter", (ev) => {
        state.circuit.hoveredItem = obj;
        // A clicked (locked) selection stays in the inspector while hovering others.
        if (!state.circuit.selectedItem) renderCircuitInspector(obj, true);
        showTip(obj.tooltip || obj.full_name || obj.label || nid, ev);
      });
      g.addEventListener("mousemove", (ev) => {
        if (tip && tip.style.display === "block") {
          tip.style.left = Math.min(window.innerWidth - 440, ev.clientX + 14) + "px";
          tip.style.top = Math.min(window.innerHeight - 100, ev.clientY + 14) + "px";
        }
      });
      g.addEventListener("mouseleave", () => {
        state.circuit.hoveredItem = null;
        hideTip();
        if (!state.circuit.selectedItem) renderCircuitInspector(null, false);
      });
      // Single click selects and locks; double-click (or the inspector button) opens the sub-diagram.
      g.addEventListener("click", (ev) => {
        if (state.circuit.dragMoved > 4) return;
        ev.stopPropagation();
        hideTip();
        $$(".circuit-node.selected, .circuit-pin.selected", svgEl).forEach((x) => x.classList.remove("selected"));
        g.classList.add("selected");
        state.circuit.selectedItem = obj;
        renderCircuitInspector(obj, false);
      });
      g.addEventListener("dblclick", (ev) => {
        if (!pre) return;
        ev.preventDefault();
        ev.stopPropagation();
        navigate(circuitHref(pre));
      });
    });

    $$(".circuit-pin", svgEl).forEach((g) => {
      const pname = g.getAttribute("data-pin") || "";
      const pObj = pinByName.get(pname) || { _isPin: true, name: pname, status: "projected" };
      g.addEventListener("mouseenter", (ev) => {
        state.circuit.hoveredItem = pObj;
        if (!state.circuit.selectedItem) renderCircuitInspector(pObj, true);
        showTip(pname + " [" + (pObj.status || "") + "]" + (pObj.type ? " : " + pObj.type : ""), ev);
      });
      g.addEventListener("mouseleave", () => {
        state.circuit.hoveredItem = null;
        hideTip();
        if (!state.circuit.selectedItem) renderCircuitInspector(null, false);
      });
      g.addEventListener("click", (ev) => {
        if (state.circuit.dragMoved > 4) return;
        ev.stopPropagation();
        $$(".circuit-node.selected, .circuit-pin.selected", svgEl).forEach((x) => x.classList.remove("selected"));
        g.classList.add("selected");
        state.circuit.selectedItem = pObj;
        renderCircuitInspector(pObj, false);
      });
    });

    fitCircuitStage();
    requestAnimationFrame(fitCircuitStage);
    applyCircuitNodeHighlight();
  }

  function renderCircuitChips(mode) {
    const wrap = $("#cirChipsWrap");
    if (!wrap) return;
    clearEl(wrap);
    const circuits = (state.manifest && state.manifest.circuits) || {};
    const list = mode === "bundle" ? (circuits.bundles || []) : (mode === "theorem" ? (circuits.theorems || []) : []);
    const q = (state.circuit.selectorFilter || "").trim().toLowerCase();

    if (mode === "macro") {
      const nB = (circuits.bundles || []).length, nT = (circuits.theorems || []).length;
      const what = nB && nT ? "Structures or Theorems" : (nB ? "Structures" : "Theorems");
      wrap.appendChild(el("span", { className: "cir-ins-note", textContent: (nB || nT)
        ? "Choose " + what + " above, or double-click a highlighted node, to open a more detailed diagram."
        : (state.manifest && state.manifest.source_only ? "Source-only scan: module import map only." : "Only the repository map is available for this project.") }));
      return;
    }

    const filtered = list.filter((it) => {
      if (!q) return true;
      return ((it.name || "") + " " + (it.short || "") + " " + (it.badge || "")).toLowerCase().includes(q);
    });
    if (!filtered.length) {
      wrap.appendChild(el("span", { className: "cir-ins-note", textContent: "No diagrams match \"" + q + "\"." }));
      return;
    }
    filtered.forEach((it) => {
      const isAct = state.circuit.mode === mode && (state.circuit.target === it.name || state.circuit.target === it.short);
      wrap.appendChild(el("a", {
        className: "cir-chip" + (isAct ? " active" : ""),
        href: circuitHref({ mode, name: it.name, short: it.short }),
        title: it.name,
        "aria-current": isAct ? "page" : null
      }, [
        el("span", { textContent: it.short || shortName(it.name) }),
        it.badge ? el("span", { className: "chip-tag", textContent: it.badge }) : null
      ]));
    });
    // Keep the open diagram's chip visible inside the short scrolling picker
    // (without scrolling the page).
    const act = wrap.querySelector(".cir-chip.active");
    if (act) {
      requestAnimationFrame(() => {
        const wr = wrap.getBoundingClientRect();
        const cr = act.getBoundingClientRect();
        if (cr.top < wr.top || cr.bottom > wr.bottom) wrap.scrollTop += cr.top - wr.top - 4;
      });
    }
  }

  async function renderCircuitView(subMode, argTarget) {
    const main = $("#appMain");
    const circuits = (state.manifest && state.manifest.circuits) || {};
    const mode = (subMode === "bundle" || subMode === "theorem" || subMode === "macro") ? subMode : "macro";
    const entry = findCircuitEntry(mode, argTarget) || (circuits.macro ? { mode: "macro", name: "Macro", short: "Macro", path: circuits.macro } : null);

    if (!entry) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No diagrams" }),
        el("p", { textContent: "This build does not include any diagrams." })
      ]));
      return;
    }

    state.circuit.mode = entry.mode;
    state.circuit.target = entry.mode === "macro" ? "" : (entry.name || entry.short || "");
    state.circuit.selectedItem = null;
    state.circuit.hoveredItem = null;

    // Push breadcrumb history
    const last = state.circuit.history[state.circuit.history.length - 1];
    if (!last || last.mode !== state.circuit.mode || last.target !== state.circuit.target) {
      state.circuit.history.push({ mode: state.circuit.mode, target: state.circuit.target, short: entry.short || shortName(entry.name) });
      if (state.circuit.history.length > 20) state.circuit.history.shift();
    }

    clearEl(main);
    const shell = el("div", { className: "circuit-shell" });

    // Toolbar
    // Hide empty Structures / Theorems tabs (source-only scans have neither).
    const modeSeg = el("div", { className: "seg", role: "tablist" }, [
      ["macro", "Repository"],
      (circuits.bundles || []).length ? ["bundle", "Structures (" + fmtInt((circuits.bundles || []).length) + ")"] : null,
      (circuits.theorems || []).length ? ["theorem", "Theorems (" + fmtInt((circuits.theorems || []).length) + ")"] : null
    ].filter(Boolean).map(([mKey, lbl]) => el("button", {
      type: "button",
      className: state.circuit.mode === mKey ? "active" : "",
      textContent: lbl,
      onclick: () => {
        // A tab switch starts a fresh trail rather than extending the old one.
        state.circuit.history = [];
        if (mKey === "macro") navigate("#circuit/macro");
        else {
          const list = mKey === "bundle" ? (circuits.bundles || []) : (circuits.theorems || []);
          const first = list[0];
          if (first) navigate("#circuit/" + mKey + "/" + encodeURIComponent(first.short || first.name));
        }
      }
    })));

    const crumbs = el("div", { className: "cir-crumbs", id: "cirCrumbs" });
    if (state.circuit.history.length > 1) {
      crumbs.appendChild(el("button", {
        type: "button", className: "btn sm", textContent: "← Back",
        onclick: () => {
          state.circuit.history.pop();
          const prev = state.circuit.history[state.circuit.history.length - 1];
          if (!prev || prev.mode === "macro") navigate("#circuit/macro");
          else navigate("#circuit/" + prev.mode + "/" + encodeURIComponent(prev.short || prev.target));
        }
      }));
    }
    // A one-step trail would only repeat the active tab.
    if (state.circuit.history.length > 1) state.circuit.history.slice(-5).forEach((h, idx, arr) => {
      if (idx > 0) crumbs.appendChild(el("span", { className: "cir-crumb-sep", textContent: "›" }));
      const cur = idx === arr.length - 1;
      const lbl = h.mode === "macro" ? "Repository" : (h.short || shortName(h.target));
      crumbs.appendChild(cur
        ? el("span", { className: "cir-crumb cur", "aria-current": "page", textContent: lbl })
        : el("a", { className: "cir-crumb", href: circuitHref({ mode: h.mode, name: h.target, short: h.short }), textContent: lbl }));
    });

    const nodeHighlightInput = el("input", {
      type: "search", className: "input", id: "cirNodeFilter",
      placeholder: "Highlight nodes…", value: state.circuit.filter,
      style: { width: "175px", padding: "4px 8px", fontSize: "12px" },
      oninput: (ev) => { state.circuit.filter = ev.target.value; applyCircuitNodeHighlight(); }
    });

    const toolbar = el("div", { className: "cir-toolbar" }, [
      modeSeg,
      crumbs,
      el("div", { className: "spacer" }),
      nodeHighlightInput,
      el("button", { type: "button", className: "btn sm", textContent: "+", title: "Zoom in", onclick: () => { state.circuit.scale = Math.min(4, state.circuit.scale * 1.2); applyCircuitTransform(); } }),
      el("button", { type: "button", className: "btn sm", textContent: "−", title: "Zoom out", onclick: () => { state.circuit.scale = Math.max(0.16, state.circuit.scale / 1.2); applyCircuitTransform(); } }),
      el("button", { type: "button", className: "btn sm", textContent: "Fit", title: "Fit diagram", onclick: fitCircuitStage }),
      el("button", { type: "button", className: "btn sm", textContent: "1:1", title: "Reset scale", onclick: () => { state.circuit.scale = 1; state.circuit.tx = 16; state.circuit.ty = 16; applyCircuitTransform(); } }),
      el("button", {
        type: "button", className: "btn sm", textContent: "Download SVG",
        onclick: () => {
          const sh = state.circuit.data;
          if (!sh) return;
          const txt = state.theme === "light" ? (sh.svg_light || sh.svg || sh.svg_dark) : (sh.svg_dark || sh.svg || sh.svg_light);
          if (!txt) return;
          const blob = new Blob([txt], { type: "image/svg+xml;charset=utf-8" });
          const u = URL.createObjectURL(blob);
          const a = el("a", { href: u, download: "leanre_diagram_" + state.circuit.mode + ".svg" });
          document.body.appendChild(a);
          a.click();
          a.remove();
          URL.revokeObjectURL(u);
        }
      })
    ]);

    // Diagram picker
    const selBar = el("div", { className: "cir-selector-bar" });
    if (state.circuit.mode !== "macro") {
      selBar.appendChild(el("div", { className: "cir-selector-row" }, [
        el("input", {
          type: "search", className: "input", id: "cirChipFilter",
          placeholder: state.circuit.mode === "bundle" ? "Filter structures…" : "Filter theorems…",
          value: state.circuit.selectorFilter,
          style: { width: "220px", padding: "4px 8px", fontSize: "12px" },
          oninput: (ev) => { state.circuit.selectorFilter = ev.target.value; renderCircuitChips(state.circuit.mode); }
        })
      ]));
    }
    selBar.appendChild(el("div", { className: "cir-chips-wrap", id: "cirChipsWrap" }));

    // Legend bar
    const legBar = el("div", { className: "cir-legend-bar" }, [
      ["used", "emerald"], ["unused", "slate"], ["conditional", "amber"], ["trivial or ignored", "crimson"], ["has its own diagram", "cyan"]
    ].map(([lbl, cls]) => el("span", { className: "cir-leg-pill " + cls }, [el("i"), el("span", { textContent: lbl })])).concat([el("span", { className: "spacer" }), trustBadge("tool")]));

    // Stage + Inspector
    const body = el("div", { className: "cir-body" }, [
      el("div", { className: "cir-stage-wrap", id: "cirStageWrap" }, [
        el("div", { className: "cir-stage", id: "cirStage" }, [
          el("div", { className: "loading-card", style: { margin: "24px" } }, [
            el("div", { className: "spinner" }),
            el("div", { textContent: "Loading diagram…" })
          ])
        ])
      ]),
      el("aside", { className: "cir-inspector", id: "cirInspector", "aria-label": "Diagram details" })
    ]);

    const fsChange = () => keepCircuitViewport();
    fsChange.before = rememberCircuitViewport;
    toolbar.appendChild(fullscreenButton(shell, fsChange));
    shell.appendChild(toolbar);
    shell.appendChild(selBar);
    shell.appendChild(legBar);
    shell.appendChild(body);
    main.appendChild(shell);

    renderCircuitChips(state.circuit.mode);
    wireCircuitStageEvents();

    try {
      const data = await fetchJson(entry.path);
      state.circuit.data = data;
      mountActiveCircuitSvg();
      renderCircuitInspector(null, false);
    } catch (err) {
      const stg = $("#cirStage");
      if (stg) {
        clearEl(stg);
        stg.appendChild(el("div", { className: "empty-card", style: { margin: "24px" } }, [
          el("h3", { textContent: "Could not load this diagram" }),
          el("p", { textContent: String(err.message || err) })
        ]));
      }
    }
  }

  // ==========================================================================
  // VIEW 3: FINDINGS (`findings/*.md`)
  // ==========================================================================
  async function renderFindingsView(slugArg) {
    const main = $("#appMain");
    const keeper = docListScrollKeeper("findings");
    clearEl(main);
    const items = (state.manifest && state.manifest.findings) || [];
    if (!items.length) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No findings" }),
        el("p", { textContent: "This build has no findings chapters." })
      ]));
      return;
    }

    const active = items.find((f) => f.slug === slugArg) || items.find((f) => f.slug === state.findingSlug) || items[0];
    state.findingSlug = active.slug;
    if (state.findingQ == null) state.findingQ = "";
    const hrefOf = (f) => "#findings/" + encodeURIComponent(f.slug);
    const titleOf = (f) => usSpelling(plainTextFromTex(f.title || f.slug));

    const listEl = el("div", { className: "doc-list", id: "findingListEl" });
    const countEl = el("span", { className: "doc-filter-count" });
    const clearBtn = filterClearButton(() => { state.findingQ = ""; inp.value = ""; fillList(); inp.focus(); });
    const metaRow = el("div", { className: "doc-filter-meta" }, [countEl, clearBtn]);
    const inp = el("input", {
      type: "search", className: "input", id: "findingSearchInput", placeholder: "Filter findings…",
      "aria-label": "Filter findings", value: state.findingQ,
      oninput: (ev) => { state.findingQ = ev.target.value; fillList(); }
    });
    function fillList() {
      clearEl(listEl);
      const q = state.findingQ.trim().toLowerCase();
      const shown = items.filter((f) => !q || (titleOf(f) + " " + f.slug).toLowerCase().includes(q));
      for (const f of shown) {
        listEl.appendChild(el("button", {
          type: "button",
          className: "doc-item" + (f.slug === active.slug ? " active" : ""),
          "aria-current": f.slug === active.slug ? "page" : null,
          onclick: () => navigate(hrefOf(f))
        }, [el("div", { className: "di-title", textContent: titleOf(f) })]));
      }
      if (!shown.length) listEl.appendChild(el("div", { className: "cir-ins-note doc-list-empty", textContent: "No matching findings." }));
      countEl.textContent = showingCount(shown.length, items.length, "findings", !!q);
      metaRow.hidden = !q;
      clearBtn.hidden = !q;
    }

    const sidebar = el("aside", { className: "doc-sidebar", "aria-label": "Findings" }, [
      el("div", { className: "doc-sidebar-top" }, [
        el("strong", { className: "doc-sidebar-title", textContent: "Findings" }),
        items.length > 6 ? inp : null,
        items.length > 6 ? metaRow : null
      ]),
      listEl
    ]);

    const articleWrap = el("article", { className: "doc-article-wrap" }, [
      el("div", { className: "doc-article-meta" }, [trustBadge(docProvenance(active))]),
      el("div", { className: "md-body", id: "findingMdBody" }, [
        el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })])
      ]),
      docPrevNext(items, active.slug, hrefOf, titleOf)
    ]);

    main.appendChild(el("div", { className: "doc-layout" }, [sidebar, articleWrap]));
    fillList();
    keeper.restore(listEl);
    revealArticleOnMobile(articleWrap, keeper);

    try {
      const md = await fetchText(active.path);
      const body = $("#findingMdBody");
      if (body) {
        body.innerHTML = renderMarkdownBlockSafe(md, "findings", "findings/" + active.slug + ".md");
        polishDocText(body);
        decorateLeanLinks(body);
        wireDocAnchors(body, hrefOf(active));
      }
    } catch (err) {
      const body = $("#findingMdBody");
      if (body) {
        clearEl(body);
        body.appendChild(el("div", { className: "empty-card" }, [
          el("h3", { textContent: "Could not load this finding" }),
          el("p", { textContent: String(err.message || err) })
        ]));
      }
    }
  }

  // ==========================================================================
  // VIEW 4: DOSSIERS (`analysis/*.md` + `research/*.md`)
  // ==========================================================================
  // Display names for dossier groups whose stored name is shorthand.
  const DOSSIER_CAT_DISPLAY = { "dom >= 1,000 closures": "Subtrees ≥ 1,000 declarations" };
  function inferDossierCategory(d) {
    const c = inferDossierCategoryRaw(d);
    return DOSSIER_CAT_DISPLAY[c] || c.replace(/\s>=\s/g, " ≥ ").replace(/\s!=\s/g, " ≠ ");
  }
  function inferDossierCategoryRaw(d) {
    if (d.category) return String(d.category);
    const s = String(d.slug || "").toLowerCase();
    if (s.startsWith("audit_")) return "Math audits";
    if (s.startsWith("adversarial_")) return "Semantic rechecks";
    if (s.startsWith("dom1000_") || s.startsWith("dom1500_")) return "dom >= 1,000 closures";
    if (s.startsWith("pillar_") || s.startsWith("theta_") || s.startsWith("vwin_") || s.startsWith("allrows_")) return "Pillars";
    if (s.includes("hironaka") || s.includes("kato") || s.includes("siegel") || s.includes("classical") || s.includes("famous") || s.includes("harish")) return "Classical theorems";
    if (s.includes("benchmark") || s.includes("sweep") || s.includes("generic_corpus") || s.includes("portability") || s.includes("cluster_atlas") || s.includes("compute_and")) return "Benchmarks & sweeps";
    return "Core";
  }

  async function renderDossiersView(sub, arg) {
    const main = $("#appMain");
    const keeper = docListScrollKeeper("dossiers");
    clearEl(main);
    const dossiers = (state.manifest && state.manifest.dossiers) || [];
    const research = (state.manifest && state.manifest.research) || [];

    if (!dossiers.length && !research.length) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No dossiers" }),
        el("p", { textContent: "This build has no dossiers or research notes." })
      ]));
      return;
    }

    const prevMode = state.dossierMode;
    if (sub === "research" && research.length) {
      state.dossierMode = "research";
      if (arg) state.dossierSlug = arg;
    } else if (sub) {
      state.dossierMode = "analysis";
      state.dossierSlug = sub;
    }
    // A filter typed for one list should not silently hide the other.
    if (prevMode !== state.dossierMode) { state.dossierQ = ""; state.dossierCat = "all"; }

    const isResearch = state.dossierMode === "research";
    const activePool = isResearch ? research : dossiers;
    const active = activePool.find((x) => x.slug === state.dossierSlug) || activePool[0] || null;
    if (active) state.dossierSlug = active.slug;
    const hrefOf = (d) => (isResearch ? "#dossiers/research/" : "#dossiers/") + encodeURIComponent(d.slug);
    const titleOf = (d) => usSpelling(plainTextFromTex(d.title || d.slug));

    const categories = ["all"];
    if (!isResearch) {
      dossiers.forEach((d) => {
        const c = inferDossierCategory(d);
        if (!categories.includes(c)) categories.push(c);
      });
    }
    // Reading order follows the sidebar: grouped by category for dossiers.
    const ordered = isResearch ? activePool.slice() : categories.slice(1).flatMap((c) => dossiers.filter((d) => inferDossierCategory(d) === c));

    const countEl = el("span", { className: "doc-filter-count" });
    const isFiltered = () => !!state.dossierQ.trim() || (!isResearch && state.dossierCat !== "all");
    const inp = el("input", {
      type: "search", className: "input", id: "dossierSearchInput",
      placeholder: isResearch ? "Filter research notes…" : "Filter dossiers…",
      "aria-label": isResearch ? "Filter research notes" : "Filter dossiers",
      value: state.dossierQ,
      oninput: (ev) => { state.dossierQ = ev.target.value; populateDossierList(); }
    });
    const catSel = (!isResearch && categories.length > 2) ? el("select", {
      className: "select", id: "dossierCatSel", "aria-label": "Category",
      onchange: (ev) => { state.dossierCat = ev.target.value; populateDossierList(); }
    }, categories.map((c) => el("option", { value: c, selected: state.dossierCat === c, textContent: c === "all" ? "All categories" : c }))) : null;
    const clearBtn = filterClearButton(() => {
      state.dossierQ = ""; state.dossierCat = "all"; inp.value = "";
      if (catSel) catSel.value = "all";
      populateDossierList(); inp.focus();
    });
    const metaRow = el("div", { className: "doc-filter-meta" }, [countEl, clearBtn]);

    const sidebarTop = el("div", { className: "doc-sidebar-top" }, [
      research.length ? el("div", { className: "seg" }, [
        el("button", {
          type: "button", className: !isResearch ? "active" : "",
          textContent: "Dossiers (" + dossiers.length + ")",
          onclick: () => { state.dossierMode = "analysis"; state.dossierSlug = ""; state.dossierQ = ""; state.dossierCat = "all"; navigate("#dossiers"); }
        }),
        el("button", {
          type: "button", className: isResearch ? "active" : "",
          textContent: "Research (" + research.length + ")",
          onclick: () => { state.dossierMode = "research"; state.dossierSlug = ""; state.dossierQ = ""; state.dossierCat = "all"; navigate("#dossiers/research"); }
        })
      ]) : el("strong", { className: "doc-sidebar-title", textContent: "Dossiers" }),
      inp,
      catSel,
      metaRow
    ]);

    const listEl = el("div", { className: "doc-list", id: "dossierListEl" });
    const docButton = (d) => el("button", {
      type: "button",
      className: "doc-item" + (active && d.slug === active.slug ? " active" : ""),
      "aria-current": active && d.slug === active.slug ? "page" : null,
      onclick: () => navigate(hrefOf(d))
    }, [el("div", { className: "di-title", textContent: titleOf(d) })]);
    function populateDossierList() {
      clearEl(listEl);
      const q = state.dossierQ.trim().toLowerCase();
      const filtered = ordered.filter((d) => {
        if (!isResearch && state.dossierCat !== "all" && inferDossierCategory(d) !== state.dossierCat) return false;
        if (!q) return true;
        return ((d.title || "") + " " + (d.slug || "") + " " + inferDossierCategory(d)).toLowerCase().includes(q);
      });
      const f = isFiltered();
      countEl.textContent = showingCount(filtered.length, activePool.length, isResearch ? "notes" : "dossiers", f);
      metaRow.hidden = !f;
      clearBtn.hidden = !f;
      if (!filtered.length) {
        listEl.appendChild(el("div", { className: "cir-ins-note doc-list-empty", textContent: isResearch ? "No matching research notes." : "No matching dossiers." }));
        return;
      }
      if (!isResearch) {
        let lastCat = null;
        for (const d of filtered) {
          const cat = inferDossierCategory(d);
          if (cat !== lastCat) { listEl.appendChild(el("div", { className: "doc-cat-hdr", textContent: cat })); lastCat = cat; }
          listEl.appendChild(docButton(d));
        }
      } else {
        filtered.forEach((d) => listEl.appendChild(docButton(d)));
      }
    }

    const articleWrap = el("article", { className: "doc-article-wrap" });
    if (active) {
      articleWrap.appendChild(el("div", { className: "doc-article-meta" }, [
        !isResearch && !(docProvenance(active) === "notes" && /^review notes?$/i.test(inferDossierCategory(active))) ? el("span", { textContent: inferDossierCategory(active) }) : null,
        trustBadge(docProvenance(active))
      ]));
      articleWrap.appendChild(el("div", { className: "md-body", id: "dossierMdBody" }, [
        el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })])
      ]));
      const pn = docPrevNext(ordered, active.slug, hrefOf, titleOf);
      if (pn) articleWrap.appendChild(pn);
    } else {
      articleWrap.appendChild(el("div", { className: "empty-card" }, [el("p", { textContent: "Choose a dossier from the list." })]));
    }

    main.appendChild(el("div", { className: "doc-layout" }, [
      el("aside", { className: "doc-sidebar", "aria-label": "Dossiers" }, [sidebarTop, listEl]),
      articleWrap
    ]));
    populateDossierList();
    keeper.restore(listEl);
    revealArticleOnMobile(articleWrap, keeper);

    if (active) {
      try {
        const md = await fetchText(active.path);
        const body = $("#dossierMdBody");
        if (body) {
          body.innerHTML = renderMarkdownBlockSafe(md, isResearch ? "research" : "analysis", (isResearch ? "research/" : "analysis/") + active.slug + ".md");
          polishDocText(body);
          decorateLeanLinks(body);
          wireDocAnchors(body, hrefOf(active));
        }
      } catch (err) {
        const body = $("#dossierMdBody");
        if (body) {
          clearEl(body);
          body.appendChild(el("div", { className: "empty-card" }, [
            el("h3", { textContent: "Could not load this dossier" }),
            el("p", { textContent: String(err.message || err) })
          ]));
        }
      }
    }
  }

  // ==========================================================================
  // VIEW 5: DECOMPILATION BLUEPRINTS (`outputs/decomp/*.json`)
  // ==========================================================================
  function normalizeBlueprintNodes(doc) {
    const raw = doc && doc.nodes;
    if (Array.isArray(raw)) {
      return raw.filter((n) => n && (n.id || n.fqn)).map((n) => Object.assign({}, n, {
        id: String(n.id || n.fqn),
        dom_sub: n.dom && n.dom.subtree != null ? Number(n.dom.subtree) : (n.dom_subtree != null ? Number(n.dom_subtree) : -1)
      }));
    }
    if (raw && typeof raw === "object") {
      return Object.entries(raw).map(([k, v]) => Object.assign({}, v, {
        id: String((v && (v.id || v.fqn)) || k),
        dom_sub: v && v.dom && v.dom.subtree != null ? Number(v.dom.subtree) : -1
      }));
    }
    return [];
  }

  function statusPillClass(st) {
    const u = String(st || "").toUpperCase();
    if (u === "READ" || u === "REAL" || u === "STANDALONE-READY" || u === "ALIGNED" || u === "PASS") return "emerald";
    if (u === "PARTIAL" || u === "WRAPPER" || u === "PROXY" || u === "SCOPED" || u === "PARTIAL_DRIFT" || u === "MODERATE") return "amber";
    if (u === "OPAQUE" || u === "DEGENERATE" || u === "VACUOUS" || u === "CROSS_DOMAIN_MISPLACED" || u === "HIGH" || u === "FAIL") return "crimson";
    return "slate";
  }

  // ---------- Shared sortable tables, filter Clear buttons, document readers ----------
  // Sort state per table, kept for the session: { key, dir: "asc" | "desc" }.
  // An empty key keeps the data's own order.
  function tableSort(id, dflt) {
    state.tableSorts = state.tableSorts || {};
    if (!state.tableSorts[id]) state.tableSorts[id] = Object.assign({}, dflt);
    return state.tableSorts[id];
  }

  const isBlankSortValue = (v) => v == null || v === "" || v === "—" || (typeof v === "number" && !Number.isFinite(v));

  // Stable sort; blank values ("—", null) always go last in either direction.
  function sortRowsBy(rows, cols, sort) {
    const c = cols.find((x) => x.key === sort.key && x.sortable !== false);
    if (!c) return rows.slice();
    const get = c.get || ((r) => r[c.key]);
    const mul = sort.dir === "asc" ? 1 : -1;
    return rows.map((r, i) => ({ r, i, v: get(r) })).sort((a, b) => {
      const na = isBlankSortValue(a.v), nb = isBlankSortValue(b.v);
      if (na || nb) return na && nb ? a.i - b.i : (na ? 1 : -1);
      const d = (typeof a.v === "number" && typeof b.v === "number")
        ? a.v - b.v
        : String(a.v).localeCompare(String(b.v), undefined, { numeric: true, sensitivity: "base" });
      return (d * mul) || (a.i - b.i);
    }).map((x) => x.r);
  }

  // <thead> whose sortable headers toggle ▲/▼ with a click, Enter or Space.
  // The header row stays mounted, so keyboard focus survives a re-sort.
  // cols: [{ key, label, num, title, sortable, firstDir, get }]
  function sortableHead(cols, sort, onSort) {
    const ths = cols.map((c) => {
      if (c.sortable === false) return el("th", { className: c.num ? "num" : null, title: c.title || null, textContent: c.label });
      const ind = el("span", { className: "sort-ind", "aria-hidden": "true" });
      const th = el("th", { className: "sortable" + (c.num ? " num" : ""), tabindex: "0", title: c.title || null, "data-sort-key": c.key }, [
        el("span", { className: "sort-label", textContent: c.label }), ind
      ]);
      const act = () => {
        if (sort.key === c.key) sort.dir = sort.dir === "asc" ? "desc" : "asc";
        else { sort.key = c.key; sort.dir = c.firstDir || (c.num ? "desc" : "asc"); }
        paint();
        onSort(sort);
      };
      th.addEventListener("click", act);
      th.addEventListener("keydown", (ev) => {
        if (ev.key === "Enter" || ev.key === " " || ev.key === "Spacebar") { ev.preventDefault(); act(); }
      });
      th._ind = ind;
      th._key = c.key;
      return th;
    });
    function paint() {
      ths.forEach((th) => {
        if (!th._ind) return;
        const on = th._key === sort.key;
        if (on) th.setAttribute("aria-sort", sort.dir === "asc" ? "ascending" : "descending");
        else th.removeAttribute("aria-sort");
        th.classList.toggle("sorted", on);
        th._ind.textContent = on ? (sort.dir === "asc" ? "▲" : "▼") : "⇅";
      });
    }
    paint();
    return el("thead", null, [el("tr", null, ths)]);
  }

  // One quiet "Clear" button for every filter bar; hidden while nothing is filtered.
  function filterClearButton(onClear) {
    return el("button", { type: "button", className: "btn sm filter-clear", textContent: "Clear", title: "Clear filters", hidden: true, onclick: onClear });
  }
  function showingCount(shown, total, noun, filtered) {
    return filtered ? "Showing " + fmtInt(shown) + " of " + fmtInt(total) + " " + noun : fmtInt(total) + " " + noun;
  }

  // Keep a document list's scroll position when the reader re-renders for
  // another document in the same list; returns a restore() for the new list.
  function docListScrollKeeper(viewKey) {
    const main = $("#appMain");
    const prevList = main && main.dataset.docView === viewKey ? $(".doc-list", main) : null;
    const top = prevList ? prevList.scrollTop : null;
    const wasSame = prevList != null;
    if (main) main.dataset.docView = viewKey;
    return {
      wasSame,
      restore(listEl) {
        if (!listEl) return;
        if (top != null) listEl.scrollTop = top;
        const act = $(".doc-item.active", listEl);
        if (!act) return;
        const lt = listEl.scrollTop, lh = listEl.clientHeight;
        const at = act.offsetTop - listEl.offsetTop, ah = act.offsetHeight;
        if (at < lt) listEl.scrollTop = Math.max(0, at - 8);
        else if (at + ah > lt + lh) listEl.scrollTop = at + ah - lh + 8;
      }
    };
  }

  // Wire a rendered Markdown body: in-document "#heading" links scroll inside
  // the article (and keep a shareable ?sec= link) instead of changing page.
  function wireDocAnchors(body, routeBase) {
    if (!body) return;
    const find = (anchor) => {
      const a = docAnchorSlug(anchor);
      if (!a) return null;
      const esc = (window.CSS && CSS.escape) ? CSS.escape : ((x) => x.replace(/[^\w-]/g, "\\$&"));
      return body.querySelector("#" + esc("h-" + a)) || body.querySelector("#" + esc(a)) ||
        Array.from(body.querySelectorAll("[id^='h-" + a.replace(/['\\]/g, "") + "-']"))[0] || null;
    };
    body.querySelectorAll("a[data-doc-anchor]").forEach((a) => {
      const anchor = a.getAttribute("data-doc-anchor");
      a.setAttribute("href", routeBase + "?sec=" + encodeURIComponent(anchor));
      a.addEventListener("click", (ev) => {
        if (ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
        const target = find(anchor);
        ev.preventDefault();
        if (!target) return;
        const reduce = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
        target.scrollIntoView({ behavior: reduce ? "auto" : "smooth", block: "start" });
        try { window.history.replaceState(null, "", routeBase + "?sec=" + encodeURIComponent(anchor)); } catch (_) { /* ignore */ }
      });
    });
    const q = (window.location.hash || "").split("?")[1] || "";
    const sec = new URLSearchParams(q).get("sec");
    const pathNow = (window.location.hash || "").split("?")[0];
    if (sec && pathNow === routeBase) {
      const t = find(sec);
      if (t) requestAnimationFrame(() => t.scrollIntoView({ block: "start" }));
    }
  }

  // "Previous / Next" links at the end of an article.
  function docPrevNext(list, activeSlug, hrefOf, titleOf) {
    const i = list.findIndex((d) => d.slug === activeSlug);
    if (i < 0 || list.length < 2) return null;
    const prev = i > 0 ? list[i - 1] : null;
    const next = i < list.length - 1 ? list[i + 1] : null;
    const link = (d, dir) => el("a", { className: "doc-pn " + dir, href: hrefOf(d) }, [
      el("span", { className: "doc-pn-dir", textContent: dir === "prev" ? "‹ Previous" : "Next ›" }),
      el("span", { className: "doc-pn-title", textContent: titleOf(d) })
    ]);
    return el("nav", { className: "doc-prevnext", "aria-label": "Previous and next" }, [
      prev ? link(prev, "prev") : el("span"),
      next ? link(next, "next") : el("span")
    ]);
  }

  // On narrow screens the list sits above the article; bring the article up.
  function revealArticleOnMobile(articleWrap, keeper) {
    if (keeper.wasSame && window.innerWidth <= 820 && articleWrap) {
      requestAnimationFrame(() => articleWrap.scrollIntoView({ block: "start" }));
    }
  }

  async function renderBlueprintsView(bpArg) {
    const main = $("#appMain");
    const keeper = docListScrollKeeper("blueprints");
    clearEl(main);
    const bps = (state.manifest && state.manifest.blueprints) || [];
    if (!bps.length) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No blueprints" }),
        el("p", { textContent: "This build does not include any blueprints." })
      ]));
      return;
    }

    const active = bps.find((b) => b.id === bpArg) || bps.find((b) => b.id === state.bpId) || bps[0];
    state.bpId = active.id;
    if (state.bpListQ == null) state.bpListQ = "";

    const sidebarList = el("div", { className: "doc-list", id: "bpListEl" });
    const listCount = el("span", { className: "doc-filter-count" });
    const listClear = filterClearButton(() => { state.bpListQ = ""; listInp.value = ""; fillBpList(); listInp.focus(); });
    const listMeta = el("div", { className: "doc-filter-meta" }, [listCount, listClear]);
    const listInp = el("input", {
      type: "search", className: "input", id: "bpListSearch", placeholder: "Filter blueprints…", "aria-label": "Filter blueprints",
      value: state.bpListQ,
      oninput: (ev) => { state.bpListQ = ev.target.value; fillBpList(); }
    });
    function fillBpList() {
      clearEl(sidebarList);
      const q = state.bpListQ.trim().toLowerCase();
      const shown = bps.filter((b) => !q || ((b.id || "") + " " + (b.title || "")).toLowerCase().includes(q));
      shown.forEach((b) => {
        sidebarList.appendChild(el("button", {
          type: "button",
          className: "doc-item" + (b.id === active.id ? " active" : ""),
          "aria-current": b.id === active.id ? "page" : null,
          onclick: () => { state.bpPage = 0; state.bpSelectedNode = ""; navigate("#blueprints/" + encodeURIComponent(b.id)); }
        }, [
          el("div", { className: "di-title", textContent: b.title || b.id }),
          el("div", { className: "di-meta", textContent: fmtInt(b.node_count) + " declarations · " + fmtInt(b.non_opaque_count) + " read" })
        ]));
      });
      if (!shown.length) sidebarList.appendChild(el("div", { className: "cir-ins-note doc-list-empty", textContent: "No matching blueprints." }));
      listCount.textContent = showingCount(shown.length, bps.length, "blueprints", !!q);
      listMeta.hidden = !q;
      listClear.hidden = !q;
    }

    const contentBox = el("div", { id: "bpContentBox" }, [
      el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading blueprint…" })])
    ]);

    main.appendChild(el("div", { className: "doc-layout" }, [
      el("aside", { className: "doc-sidebar", "aria-label": "Blueprints" }, [
        el("div", { className: "doc-sidebar-top" }, [
          el("strong", { className: "doc-sidebar-title", textContent: "Blueprints" }),
          listInp,
          listMeta
        ]),
        sidebarList
      ]),
      contentBox
    ]));
    fillBpList();
    keeper.restore(sidebarList);

    try {
      const doc = await fetchJson(active.path);
      renderBlueprintDetail(doc, active);
    } catch (err) {
      clearEl(contentBox);
      contentBox.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Could not load this blueprint" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  const BP_STATUS_RANK = { READ: 0, PARTIAL: 1, OPAQUE: 2 };
  // "OPAQUE" in the blueprint data means the reading did not open the proof;
  // it is unrelated to Lean's `opaque` keyword, so it reads "Not inspected".
  const BP_STATUS_LABEL = { READ: "Read", PARTIAL: "Partial", OPAQUE: "Not inspected" };
  const BP_STATUS_TIP = { READ: "The proof was read", PARTIAL: "The proof was partly read", OPAQUE: "Not yet inspected: the reading did not open this proof (unrelated to Lean's opaque keyword)" };
  function bpStatusPill(status, extra) {
    const u = String(status || "").toUpperCase();
    return el("span", Object.assign({ className: "pill " + statusPillClass(status), title: BP_STATUS_TIP[u] || null, textContent: BP_STATUS_LABEL[u] || status || "—" }, extra || {}));
  }

  // Builds the blueprint shell once; filters, sorting, paging and row
  // selection update only the table body, count, pager and inspector.
  function renderBlueprintDetail(doc, metaEntry) {
    const box = $("#bpContentBox");
    if (!box) return;
    clearEl(box);

    const nodes = normalizeBlueprintNodes(doc);
    const claims = Array.isArray(doc.claims) ? doc.claims : [];
    const horn = Array.isArray(doc.horn) ? doc.horn : [];
    const PAGE = 60;
    const roleOf = (n) => n.role || n.kind || "";

    // Header
    box.appendChild(el("div", { className: "bp-head" }, [
      el("h2", { textContent: metaEntry.title || doc.pillar || metaEntry.id }),
      trustBadge(metaEntry.provenance ? (metaEntry.provenance === "tool_generated" ? "tool" : "notes") : "notes"),
      el("p", { className: "bp-head-meta", textContent: [
        doc.root ? "Root: " + shortName(doc.root) : null,
        fmtInt(nodes.length) + " declarations",
        fmtInt((doc.edges || []).length) + " edges",
        claims.length ? fmtInt(claims.length) + " claims" : null,
        horn.length ? plural(horn.length, "dependency clause") : null
      ].filter(Boolean).join(" · ") })
    ]));

    // Controls (mounted once)
    const stButtons = [["all", "All"], ["READ", "Read"], ["PARTIAL", "Partial"], ["OPAQUE", "Not inspected"]].map(([st, lbl]) =>
      el("button", {
        type: "button", className: state.bpStatus === st ? "active" : "", textContent: lbl, "data-status": st,
        "aria-pressed": state.bpStatus === st ? "true" : "false",
        onclick: () => { state.bpStatus = st; state.bpPage = 0; paintStatus(); update(); }
      })
    );
    const paintStatus = () => stButtons.forEach((b) => {
      const on = b.getAttribute("data-status") === state.bpStatus;
      b.classList.toggle("active", on);
      b.setAttribute("aria-pressed", on ? "true" : "false");
    });
    const countEl = el("span", { className: "toolbar-count", "aria-live": "polite" });
    const searchInp = el("input", {
      type: "search", className: "input grow", id: "bpNodeSearch",
      placeholder: "Filter by name, summary or file…", "aria-label": "Filter declarations",
      value: state.bpQ,
      oninput: (ev) => { state.bpQ = ev.target.value; state.bpPage = 0; update(); }
    });
    const clearBtn = filterClearButton(() => {
      state.bpQ = ""; state.bpStatus = "all"; state.bpPage = 0;
      searchInp.value = ""; paintStatus(); update(); searchInp.focus();
    });
    box.appendChild(el("div", { className: "toolbar-row" }, [el("div", { className: "seg" }, stButtons), searchInp, countEl, clearBtn]));

    // Sortable table + side inspector
    const sort = state.bpSort;
    const cols = [
      { key: "id", label: "Declaration", get: (n) => n.id },
      { key: "status", label: "Status", get: (n) => { const r = BP_STATUS_RANK[String(n.status || "").toUpperCase()]; return r != null ? r : (n.status ? 3 : null); } },
      { key: "dom", label: "Subtree", num: true, get: (n) => (n.dom_sub >= 0 ? n.dom_sub : null) },
      { key: "role", label: "Role", get: (n) => roleOf(n) || null }
    ];
    const tbody = el("tbody");
    const pagerHost = el("div");
    const ins = el("aside", { className: "bp-inspector", "aria-label": "Selected declaration" });
    const table = el("table", { className: "data-table bp-table" }, [sortableHead(cols, sort, () => { state.bpPage = 0; update(); }), tbody]);
    box.appendChild(el("div", { className: "bp-detail-split" }, [
      el("div", null, [el("div", { className: "table-wrap" }, [table]), pagerHost]),
      ins
    ]));

    function renderInspector(sel) {
      clearEl(ins);
      if (!sel) {
        ins.appendChild(el("div", { className: "cir-ins-note", textContent: "Nothing matches the current filter." }));
        return;
      }
      const cir = findAnyCircuitForSymbol(sel.id);
      ins.appendChild(el("div", { className: "cir-ins-hd" }, [
        el("span", { textContent: "Declaration" }),
        bpStatusPill(sel.status)
      ]));
      ins.appendChild(el("div", { className: "cir-ins-title", textContent: sel.id }));
      if (sel.header) ins.appendChild(el("div", { className: "bp-header-box", textContent: sel.header }));
      if (sel.summary) ins.appendChild(el("div", { className: "cir-ins-note", textContent: sel.summary }));
      const kv = el("div", { className: "cir-ins-kv" });
      const addKv = (k, v) => { if (v != null && v !== "") { kv.appendChild(el("div", { className: "k", textContent: k })); kv.appendChild(el("div", { className: "v", textContent: String(v) })); } };
      addKv("Kind / role", (sel.kind || "—") + " / " + (sel.role || "—"));
      addKv("Module", sel.module || "—");
      if (sel.dom_sub >= 0) addKv("Exclusive subtree", fmtInt(sel.dom_sub));
      if (sel.dom && sel.dom.idom) addKv("Reached through", sel.dom.idom);
      ins.appendChild(kv);
      const acts = el("div", { className: "cir-ins-acts" });
      acts.appendChild(el("a", { className: "btn sm primary", href: "#item/" + encodeURIComponent(sel.id), textContent: "Inspect ›" }));
      if (cir) {
        acts.appendChild(el("button", {
          type: "button", className: "btn sm", textContent: "Open diagram ›",
          onclick: () => navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name))
        }));
      }
      if (sel.anchor) {
        const gh = buildGithubUrl(sel.anchor);
        if (gh) {
          const peek = makeSrcButton(gh, sel.id, { className: "btn sm", text: "Show source inline" });
          if (peek) acts.appendChild(peek);
          acts.appendChild(el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }));
        }
      }
      ins.appendChild(acts);
    }

    function selectRow(n, tr) {
      state.bpSelectedNode = n.id;
      tbody.querySelectorAll("tr.selected").forEach((r) => { r.classList.remove("selected"); r.setAttribute("aria-selected", "false"); });
      if (tr) { tr.classList.add("selected"); tr.setAttribute("aria-selected", "true"); }
      renderInspector(n);
      if (window.innerWidth <= 1060) ins.scrollIntoView({ block: "nearest", behavior: "smooth" });
    }

    function rowFor(n, selected) {
      const cir = findAnyCircuitForSymbol(n.id);
      const tr = el("tr", {
        className: "clickable" + (selected ? " selected" : ""), tabindex: "0", "aria-selected": selected ? "true" : "false"
      }, [
        el("td", null, [
          n.tag ? el("span", { className: "ev-tag " + (["K", "L", "S", "M"].includes(n.tag) ? n.tag : "L"), textContent: "[" + n.tag + "]", style: { marginRight: "5px" } }) : null,
          el("code", { className: "bp-id" }, [identWbr(n.id)]),
          // File name only under the declaration; the full path is the link title.
          n.anchor ? el("div", { className: "bp-anchor", title: String(n.anchor) }, [makeSourceLink(n.anchor, null, String(n.anchor).split("/").pop(), n.id)]) : null
        ]),
        el("td", null, [
          bpStatusPill(n.status),
          n.verdict ? el("span", { className: "pill " + statusPillClass(n.verdict), textContent: n.verdict, style: { marginLeft: "4px" } }) : null
        ]),
        el("td", { className: "num", textContent: n.dom_sub >= 0 ? fmtInt(n.dom_sub) : "—" }),
        el("td", null, [
          el("span", { className: "cir-ins-note", textContent: roleOf(n) || "—" }),
          cir ? el("button", {
            type: "button", className: "btn sm bp-diagram-btn", textContent: "Diagram ›",
            onclick: (ev) => { ev.stopPropagation(); navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name)); }
          }) : null
        ])
      ]);
      tr.addEventListener("click", (ev) => {
        if (ev.target.closest("a, button")) return;
        selectRow(n, tr);
      });
      tr.addEventListener("keydown", (ev) => {
        if (ev.target !== tr) return;
        if (ev.key === "Enter" || ev.key === " ") { ev.preventDefault(); selectRow(n, tr); }
        else if (ev.key === "ArrowDown" || ev.key === "ArrowUp") {
          const sib = ev.key === "ArrowDown" ? tr.nextElementSibling : tr.previousElementSibling;
          if (sib) { ev.preventDefault(); sib.focus(); }
        }
      });
      return tr;
    }

    function update() {
      const q = state.bpQ.trim().toLowerCase();
      const filtered = nodes.filter((n) => {
        if (state.bpStatus !== "all" && String(n.status || "").toUpperCase() !== state.bpStatus) return false;
        if (!q) return true;
        return ((n.id || "") + " " + (n.role || "") + " " + (n.summary || "") + " " + (n.header || "") + " " + (n.anchor || "")).toLowerCase().includes(q);
      });
      const sorted = sortRowsBy(filtered, cols, sort);
      const maxPage = Math.max(0, Math.ceil(sorted.length / PAGE) - 1);
      if (state.bpPage > maxPage) state.bpPage = 0;
      const slice = sorted.slice(state.bpPage * PAGE, (state.bpPage + 1) * PAGE);
      const sel = sorted.find((n) => n.id === state.bpSelectedNode) || slice[0] || null;
      state.bpSelectedNode = sel ? sel.id : "";

      clearEl(tbody);
      slice.forEach((n) => tbody.appendChild(rowFor(n, sel && sel.id === n.id)));
      if (!slice.length) tbody.appendChild(el("tr", null, [el("td", { colspan: "4", className: "cir-ins-note", textContent: "No declarations match." })]));
      const isF = !!q || state.bpStatus !== "all";
      countEl.textContent = showingCount(sorted.length, nodes.length, "declarations", isF);
      clearBtn.hidden = !isF;

      clearEl(pagerHost);
      if (sorted.length > PAGE) {
        pagerHost.appendChild(el("div", { className: "pager" }, [
          el("button", { type: "button", className: "btn sm", disabled: state.bpPage <= 0, textContent: "← Previous", onclick: () => { state.bpPage--; update(); } }),
          el("span", { textContent: "Page " + (state.bpPage + 1) + " of " + (maxPage + 1) + " (" + fmtInt(sorted.length) + " declarations)" }),
          el("button", { type: "button", className: "btn sm", disabled: state.bpPage >= maxPage, textContent: "Next →", onclick: () => { state.bpPage++; update(); } })
        ]));
      }
      renderInspector(sel);
    }
    update();

    // Claims
    if (claims.length) {
      const LIMIT = 40;
      let showAll = false;
      const claimsBody = el("tbody");
      const subEl = el("span", { className: "sub" });
      const moreBtn = claims.length > LIMIT ? el("button", { type: "button", className: "btn sm", onclick: () => { showAll = !showAll; fillClaims(); } }) : null;
      const fillClaims = () => {
        clearEl(claimsBody);
        (showAll ? claims : claims.slice(0, LIMIT)).forEach((c) => {
          const txt = typeof c === "string" ? c : (c.text || "");
          const tag = typeof c === "string" ? "L" : (c.tag || "L");
          const ancs = (c && Array.isArray(c.anchors)) ? c.anchors : [];
          claimsBody.appendChild(el("tr", null, [
            el("td", null, [el("span", { className: "ev-tag " + (["K", "L", "S", "M"].includes(tag) ? tag : "L"), textContent: "[" + tag + "]" })]),
            el("td", { textContent: txt }),
            el("td", null, ancs.slice(0, 3).map((a) => el("div", null, [makeSourceLink(a)])))
          ]));
        });
        subEl.textContent = claims.length > LIMIT && !showAll ? "First " + LIMIT + " of " + fmtInt(claims.length) : fmtInt(claims.length) + " in total";
        if (moreBtn) moreBtn.textContent = showAll ? "Show fewer" : "Show all " + fmtInt(claims.length);
      };
      box.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "Claims" }), subEl, moreBtn]));
      box.appendChild(el("div", { className: "table-wrap" }, [
        el("table", { className: "data-table" }, [
          el("thead", null, [el("tr", null, [el("th", { textContent: "Evidence" }), el("th", { textContent: "Claim" }), el("th", { textContent: "Source" })])]),
          claimsBody
        ])
      ]));
      fillClaims();
    }
  }

  // ==========================================================================
  // VIEW 6: CLUSTERS (name-blinded structural clusters)
  // ==========================================================================
  // Readable names for the tokens in cluster and misfile data. The original
  // token stays available as a title tooltip wherever one is shown.
  const CLUSTER_TOKEN_LABEL = {
    pillar_theta: "Part A (Theta)", pillar_galois: "Part B (Galois)", pillar_window: "Part C (Window)", pillar_volume_lit: "Part D (Volume)",
    shared_diamond: "Shared diamond", tcb_mathlib_core: "TCB / Mathlib", bridge: "Bridge",
    dom_subtree: "Subtree", residual_neighborhood: "Residual neighborhood", residual_tail: "Residual tail", tcb_library_root: "Library root",
    algebra_rings_poly: "Algebra & rings", padic_local_fields: "p-adic local fields", algebraic_geometry: "Algebraic geometry",
    analytic_nt_zeta: "Analytic number theory", linear_matrix_rep: "Linear algebra & representations", measure_integration: "Measure & integration",
    prime_elem_arith: "Primes & arithmetic", complex_real_analysis: "Complex & real analysis", meta_lean_elab: "Lean metaprogramming",
    topology_manifold: "Topology & manifolds", computational_kernel_check: "Kernel computation",
    cross_domain_misplaced: "Unexpected folder", partial_drift: "Partly mismatched", aligned: "Matches",
    isolated_ns_outlier: "Namespace mismatch", cross_domain_misfile: "Topic mismatch", extreme_outlier: "Strong outlier"
  };
  function clusterToken(tok) {
    const t = String(tok == null ? "" : tok).trim();
    if (!t) return "";
    if (t.includes("+")) return t.split("+").map(clusterToken).join(" + ");
    const key = t.replace(/\s+/g, "_");
    if (CLUSTER_TOKEN_LABEL[key]) return CLUSTER_TOKEN_LABEL[key];
    const words = t.replace(/_/g, " ");
    return words.charAt(0).toUpperCase() + words.slice(1);
  }
  // "BP001" -> "Cluster 1"; anything else is shown as is.
  function clusterIdLabel(id) {
    const m = String(id || "").match(/^[A-Z]{1,4}0*(\d+)$/);
    return m ? "Cluster " + Number(m[1]) : String(id || "");
  }

  async function renderFlirtView() {
    const main = $("#appMain");
    clearEl(main);
    const assetPath = state.manifest && state.manifest.assets && state.manifest.assets.cluster_labels;
    const tier1 = state.manifest && state.manifest.assets && state.manifest.assets.flirt_tier1;
    if (!assetPath && tier1) {
      main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading clusters…" })]));
      try {
        renderTier1Body(await fetchJson(tier1));
      } catch (err) {
        clearEl(main);
        main.appendChild(el("div", { className: "empty-card" }, [el("h3", { textContent: "Could not load clusters" }), el("p", { textContent: String(err.message || err) })]));
      }
      return;
    }
    if (!assetPath) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No cluster data" }),
        el("p", { textContent: "This build does not include cluster labels." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading clusters…" })]));
    try {
      const doc = await fetchJson(assetPath);
      renderFlirtBody(doc);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Could not load clusters" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  // Turn an audit reason string into one plain sentence (or nothing).
  function clusterReasonText(reason) {
    const r = String(reason || "");
    const m = r.match(/Blinded \(([^)]*)\)(?: and Tier1 \(([^)]*)\))?.*?folder '([^']*)' expected \[([^\]]*)\]/);
    if (!m) return "";
    const nice = (x) => String(x || "").replace(/'/g, "").split(/\s*[+,]\s*/).filter(Boolean)
      .map((t) => { const h = clusterToken(t); return /^Lean\b/.test(h) ? h : h.replace(/^([A-Z])(?=[a-z])/, (c) => c.toLowerCase()); }).join(" + ");
    const niceList = (x) => String(x || "").split(/\s*,\s*/).map(nice).filter(Boolean).join(" or ");
    return "Reads as " + nice(m[1]) + (m[2] && m[2] !== m[1] ? " (names suggest " + nice(m[2]) + ")" : "") + "; the folder " + m[3] + " suggests " + niceList(m[4]) + ".";
  }

  function renderFlirtBody(doc) {
    const main = $("#appMain");
    clearEl(main);
    const clusters = Array.isArray(doc.clusters) ? doc.clusters : [];
    const totals = doc.totals || {};
    const statusCounts = totals.mismatch_status_counts || {};
    const sevCounts = totals.mismatch_severity_counts || {};
    const misplaced = Number(statusCounts.cross_domain_misplaced || clusters.filter((c) => (c.mismatch_audit && c.mismatch_audit.status) === "cross_domain_misplaced").length);
    const drift = Number(statusCounts.partial_drift || clusters.filter((c) => (c.mismatch_audit && c.mismatch_audit.status) === "partial_drift").length);
    const aligned = Number(statusCounts.aligned || clusters.filter((c) => (c.mismatch_audit && c.mismatch_audit.status) === "aligned").length);
    const highSev = Number(sevCounts.high || clusters.filter((c) => (c.mismatch_audit && c.mismatch_audit.severity) === "high").length);
    const totalN = Math.max(1, misplaced + drift + aligned);

    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Clusters" }),
      trustBadge("tool", "Clusters computed by leanre · topic labels heuristic"),
      el("p", { className: "page-lede", textContent: plural(clusters.length, "group") + " of declarations that share the same structural shape. Each group has a topic inferred from anonymized statement types and imports, which is then compared with the folder the code actually lives in." })
    ]));

    if (doc.epistemic_note) {
      main.appendChild(el("p", { className: "quiet-note", textContent: "Labels are heuristic. They are inferred from statements and imports only; proofs were not read." }));
    }

    main.appendChild(el("section", { className: "kpi-strip" }, [
      { label: "Clusters", val: fmtInt(clusters.length), sub: (totals.collapse_pct != null ? totals.collapse_pct + "% of declarations fall in the largest groups" : "") },
      { label: "In an unexpected folder", val: fmtInt(misplaced), sub: fmtInt(highSev) + " clearly out of place" },
      { label: "Partly mismatched", val: fmtInt(drift), sub: "folder and topic only partly agree" },
      { label: "Folder matches topic", val: fmtInt(aligned), sub: "" }
    ].map((k) => el("div", { className: "kpi-card" }, [
      el("div", { className: "kpi-val", textContent: k.val }),
      el("div", { className: "kpi-label", textContent: k.label }),
      k.sub ? el("div", { className: "kpi-sub", textContent: k.sub }) : null
    ]))));

    // Stacked breakdown bar
    main.appendChild(el("div", { className: "stacked-bar", title: "Unexpected folder / partly mismatched / matches" }, [
      el("div", { className: "seg-misplaced", style: { width: ((misplaced / totalN) * 100).toFixed(1) + "%" } }),
      el("div", { className: "seg-drift", style: { width: ((drift / totalN) * 100).toFixed(1) + "%" } }),
      el("div", { className: "seg-aligned", style: { width: ((aligned / totalN) * 100).toFixed(1) + "%" } })
    ]));

    // Filters: mounted once; typing only refreshes rows, count and pager.
    const statusBtns = [
      ["all", "All"], ["cross_domain_misplaced", "Unexpected folder"], ["partial_drift", "Partly mismatched"], ["aligned", "Matches"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.flirt.status === k ? "active" : "", textContent: lbl, "data-status": k,
      "aria-pressed": state.flirt.status === k ? "true" : "false",
      onclick: () => { state.flirt.status = k; state.flirt.page = 0; paintStatus(); update(); }
    }));
    const paintStatus = () => statusBtns.forEach((b) => {
      const on = b.getAttribute("data-status") === state.flirt.status;
      b.classList.toggle("active", on);
      b.setAttribute("aria-pressed", on ? "true" : "false");
    });

    const sevSel = el("select", {
      className: "select",
      "aria-label": "Severity",
      onchange: (ev) => { state.flirt.severity = ev.target.value; state.flirt.page = 0; update(); }
    }, [["all", "Any severity"], ["high", "High"], ["moderate", "Moderate"], ["low", "Low"], ["none", "None"]].map(([s, lbl]) =>
      el("option", { value: s, selected: state.flirt.severity === s, textContent: lbl })
    ));

    const searchInp = el("input", {
      type: "search", className: "input grow", id: "flirtSearchInput", placeholder: "Search by cluster, topic, folder or declaration…",
      "aria-label": "Search clusters", value: state.flirt.q,
      oninput: (ev) => { state.flirt.q = ev.target.value; state.flirt.page = 0; update(); }
    });
    const countEl = el("span", { className: "toolbar-count", id: "flirtCount", "aria-live": "polite" });
    const clearBtn = filterClearButton(() => {
      state.flirt.q = ""; state.flirt.status = "all"; state.flirt.severity = "all"; state.flirt.page = 0;
      searchInp.value = ""; sevSel.value = "all"; paintStatus(); update(); searchInp.focus();
    });
    main.appendChild(el("div", { className: "toolbar-row" }, [el("div", { className: "seg" }, statusBtns), sevSel, searchInp, countEl, clearBtn]));

    const STATUS_RANK = { cross_domain_misplaced: 0, partial_drift: 1, aligned: 2 };
    const SEV_RANK = { high: 0, moderate: 1, low: 2, none: 3 };
    const labelOf = (c) => { const bl = c.blinded_label || {}; return String(bl.label || bl.primary_domain || "").replace(/^\[M\]\s*/, ""); };
    const cols = [
      { key: "cluster", label: "Cluster", get: (c) => c.cluster_id },
      { key: "topic", label: "Inferred topic", get: (c) => labelOf(c) || null },
      { key: "folder", label: "Folder", get: (c) => (c.mismatch_audit || {}).folder_l2 || null },
      { key: "match", label: "Match", title: "Unexpected folder first, then by severity", get: (c) => {
        const ma = c.mismatch_audit || {};
        const sr = STATUS_RANK[ma.status];
        if (sr == null) return null;
        const vr = SEV_RANK[ma.severity];
        return sr * 10 + (vr == null ? 5 : vr);
      } },
      { key: "live_decls", label: "Declarations", num: true, get: (c) => { const v = Number((c.counts || {}).live_decls); return Number.isFinite(v) ? v : null; } }
    ];
    const sort = tableSort("flirt", { key: "", dir: "desc" });
    const tbody = el("tbody", { id: "flirtTbody" });
    const pagerHost = el("div", { id: "flirtPager" });
    main.appendChild(el("div", { className: "table-wrap" }, [
      el("table", { className: "data-table", id: "flirtTable" }, [sortableHead(cols, sort, () => { state.flirt.page = 0; update(); }), tbody])
    ]));
    main.appendChild(pagerHost);

    const PAGE = 50;
    const rowFor = (c) => {
      const cnt = c.counts || {};
      const bl = c.blinded_label || {};
      const ma = c.mismatch_audit || {};
      const reps = Array.isArray(c.top3_rep_decls) ? c.top3_rep_decls : [];
      return el("tr", null, [
        el("td", null, [
          el("strong", { className: "fl-id", title: c.cluster_id, textContent: clusterIdLabel(c.cluster_id) }),
          (c.pillar || c.kind) ? el("div", { className: "cir-ins-note", title: c.pillar || c.kind, textContent: clusterToken(c.pillar || c.kind) }) : null
        ]),
        el("td", null, [
          el("strong", { textContent: labelOf(c) || "—", style: { color: "var(--text-hi)", fontWeight: "600" } }),
          bl.primary_domain ? el("div", { className: "cir-ins-note", title: bl.primary_domain + (bl.secondary_domain ? " / " + bl.secondary_domain : ""), textContent: clusterToken(bl.primary_domain) + (bl.secondary_domain ? " / " + clusterToken(bl.secondary_domain) : "") }) : null
        ]),
        el("td", null, [
          el("code", null, [identWbr(ma.folder_l2 || "—")]),
          reps.length ? el("div", { className: "fl-reps" }, reps.slice(0, 2).map((r) => {
            const u = safeHref(r.github_url) || buildGithubUrl(r.module, r.line);
            const peek = u ? makeSrcButton(u, r.name) : null;
            return el("div", { className: "src-link", title: r.name || null }, [
              u ? el("a", { href: u, target: "_blank", rel: "noopener noreferrer", className: "mono" }, [identWbr(shortName(r.name))])
                : el("code", null, [identWbr(shortName(r.name))]),
              peek
            ]);
          })) : null
        ]),
        el("td", null, [
          el("span", { className: "pill " + statusPillClass(ma.status), title: ma.status || null, textContent: ma.status ? clusterToken(ma.status) : "—" }),
          ma.severity ? el("span", { className: "pill", textContent: ma.severity, style: { marginLeft: "4px" } }) : null,
          clusterReasonText(ma.reason) ? el("div", { className: "cir-ins-note", style: { marginTop: "3px" }, textContent: clusterReasonText(ma.reason) }) : null
        ]),
        el("td", { className: "num" }, [
          el("div", { textContent: fmtInt(cnt.live_decls) }),
          el("div", { className: "cir-ins-note", textContent: fmtInt(cnt.effective_core_decls) + " core" })
        ])
      ]);
    };

    function update() {
      const q = state.flirt.q.trim().toLowerCase();
      const filtered = clusters.filter((c) => {
        const ma = c.mismatch_audit || {};
        const bl = c.blinded_label || {};
        if (state.flirt.status !== "all" && ma.status !== state.flirt.status) return false;
        if (state.flirt.severity !== "all" && ma.severity !== state.flirt.severity) return false;
        if (!q) return true;
        const hay = [c.cluster_id, clusterIdLabel(c.cluster_id), c.pillar, clusterToken(c.pillar), c.root_decl, bl.label, bl.primary_domain, clusterToken(bl.primary_domain), ma.folder_l2, ma.reason].join(" ").toLowerCase();
        return hay.includes(q);
      });
      const sorted = sortRowsBy(filtered, cols, sort);
      const maxPage = Math.max(0, Math.ceil(sorted.length / PAGE) - 1);
      if (state.flirt.page > maxPage) state.flirt.page = 0;
      const slice = sorted.slice(state.flirt.page * PAGE, (state.flirt.page + 1) * PAGE);

      clearEl(tbody);
      slice.forEach((c) => tbody.appendChild(rowFor(c)));
      if (!slice.length) tbody.appendChild(el("tr", null, [el("td", { colspan: "5", className: "cir-ins-note", textContent: "No clusters match these filters." })]));
      const isF = !!q || state.flirt.status !== "all" || state.flirt.severity !== "all";
      countEl.textContent = showingCount(sorted.length, clusters.length, "clusters", isF);
      clearBtn.hidden = !isF;

      clearEl(pagerHost);
      if (sorted.length > PAGE) {
        pagerHost.appendChild(el("div", { className: "pager" }, [
          el("button", { type: "button", className: "btn sm", disabled: state.flirt.page <= 0, textContent: "← Previous", onclick: () => { state.flirt.page--; update(); } }),
          el("span", { textContent: "Page " + (state.flirt.page + 1) + " of " + (maxPage + 1) }),
          el("button", { type: "button", className: "btn sm", disabled: state.flirt.page >= maxPage, textContent: "Next →", onclick: () => { state.flirt.page++; update(); } })
        ]));
      }
    }
    update();
  }

  // ==========================================================================
  // VIEW 6B: EDGE MAP (dependency contact matrix, Mathlib overlap, same-statement pairs)
  // ==========================================================================
  const ATLAS_PILLAR_SHORT = {
    pillar_a: "A",
    pillar_d: "D",
    pillar_c: "C",
    pillar_b: "B",
    shared_diamond: "DM",
    bridge: "BR"
  };

  const SYNTENY_CORPUS_COLORS = [
    "#38bdf8", // mathlib4
    "#34d399", // lean4
    "#2dd4bf", // batteries
    "#f59e0b", // PrimeNumberTheoremAnd
    "#fb7185", // FLT
    "#60a5fa", // carleson
    "#facc15", // SpherePacking
    "#94a3b8"  // library_other
  ];

  // Canvas colors that follow the light/dark theme.
  const isLightTheme = () => state.theme === "light";
  const canvasBgRGB = () => (isLightTheme() ? [250, 250, 247] : [10, 12, 18]);
  const canvasBg = () => (isLightTheme() ? "#fafaf7" : "#080b14");
  const canvasInk = (a) => (isLightTheme() ? "rgba(30, 41, 59, " + a + ")" : "rgba(226, 232, 240, " + a + ")");
  const canvasLabel = () => (isLightTheme() ? "#334155" : "#cbd5e1");
  const mix = (a, b, t) => a.map((v, k) => Math.round(v + (b[k] - v) * t));

  // Atlas canvases draw in fixed logical coordinates. In full screen a scale
  // factor (canvas._fsK) enlarges the backing store so the plot stays crisp;
  // hit tests map pointer positions back to logical coordinates.
  function atlasSizeCanvas(canvas, w, h) {
    const k = (canvas && canvas._fsK) || 1;
    canvas.width = Math.round(w * k);
    canvas.height = Math.round(h * k);
    canvas._logW = w;
    canvas._logH = h;
    const ctx = canvas.getContext("2d");
    if (ctx) ctx.setTransform(k, 0, 0, k, 0, 0);
    return ctx;
  }
  function atlasCanvasXY(canvas, ev) {
    const r = canvas.getBoundingClientRect();
    const w = canvas._logW || canvas.width, h = canvas._logH || canvas.height;
    return [((ev.clientX - r.left) / Math.max(1, r.width)) * w, ((ev.clientY - r.top) / Math.max(1, r.height)) * h];
  }
  // Full-screen callback for a chart card: grow the canvas to the largest
  // square that fits below the card's header and notes, redraw, and restore
  // the inline size on exit.
  function atlasFsFit(card, canvas, redraw) {
    const fit = (on) => {
      if (!canvas.isConnected) return;
      if (!on || !card.classList.contains("fs-on")) {
        canvas._fsK = 0;
        Object.assign(canvas.style, { width: "", height: "", aspectRatio: "" });
        delete canvas.dataset.fsSide;
        redraw();
        return;
      }
      const wrap = canvas.parentNode;
      Object.assign(canvas.style, { width: "64px", height: "64px", aspectRatio: "auto" });
      const cs = getComputedStyle(wrap);
      const availW = wrap.clientWidth - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight);
      const availH = wrap.clientHeight - parseFloat(cs.paddingTop) - parseFloat(cs.paddingBottom);
      const lw = canvas._logW || canvas.width, lh = canvas._logH || canvas.height;
      const side = Math.max(240, Math.floor(Math.min(availW, availH * (lw / lh))));
      canvas._fsK = (side / lw) * Math.min(2, window.devicePixelRatio || 1);
      redraw();
      canvas.style.width = side + "px";
      canvas.style.height = Math.round(side * (lh / lw)) + "px";
      canvas.dataset.fsSide = String(side);
    };
    const onResize = () => {
      if (!card.isConnected) { window.removeEventListener("resize", onResize); return; }
      if (card.classList.contains("fs-on")) fit(true);
    };
    window.addEventListener("resize", onResize);
    return fit;
  }

  function atlasRegionForDfs(regions, dfsIdx) {
    if (!Array.isArray(regions)) return null;
    for (const r of regions) {
      if (dfsIdx >= r.dfs_start && dfsIdx < r.dfs_end) return r;
    }
    return regions[regions.length - 1] || null;
  }

  function atlasDrawHicCanvas(canvas, hic, mode) {
    if (!canvas || !hic || !hic.tile_128) return;
    const tile = hic.tile_128;
    const N = Number(tile.size) || 128;
    const totGrid = tile.total_log1p_q8 || [];
    const ratGrid = tile.ratio_diverging_q8 || [];
    const neutral = Number(tile.neutral_ratio_q8 ?? 128);
    const scale = 4;
    const pad = 26;
    const size = N * scale;
    const ctx = atlasSizeCanvas(canvas, size + pad, size + pad);
    if (!ctx) return;

    ctx.fillStyle = canvasBg();
    ctx.fillRect(0, 0, size + pad, size + pad);

    // Offscreen 128x128 ImageData for crisp pixel-art blit
    const off = document.createElement("canvas");
    off.width = N;
    off.height = N;
    const octx = off.getContext("2d");
    const img = octx.createImageData(N, N);
    const data = img.data;

    for (let y = 0; y < N; y++) {
      const tRow = totGrid[y] || [];
      const rRow = ratGrid[y] || [];
      for (let x = 0; x < N; x++) {
        const idx = (y * N + x) * 4;
        const tq = Number(tRow[x] || 0);
        if (tq <= 0) {
          const e0 = canvasBgRGB();
          data[idx] = e0[0]; data[idx + 1] = e0[1]; data[idx + 2] = e0[2]; data[idx + 3] = 255;
          continue;
        }
        const inten = Math.pow(tq / 255, 0.72);
        let r, g, b;
        if (mode === "density" && isLightTheme()) {
          const c = inten < 0.5 ? mix([236, 242, 246], [56, 150, 186], inten * 2) : mix([56, 150, 186], [180, 83, 9], (inten - 0.5) * 2);
          r = c[0]; g = c[1]; b = c[2];
        } else if (mode === "density") {
          // Dark -> teal -> cyan -> amber hotspot
          if (inten < 0.5) {
            const u = inten * 2;
            r = Math.round(12 + u * 28);
            g = Math.round(30 + u * 165);
            b = Math.round(58 + u * 182);
          } else {
            const u = (inten - 0.5) * 2;
            r = Math.round(40 + u * 215);
            g = Math.round(195 + u * 10);
            b = Math.round(240 - u * 195);
          }
        } else {
          // Diverging cyan (#1ed7ff) <- silver (#dce2f7) -> amber (#ffaa23)
          const rq = Number(rRow[x] ?? neutral);
          const d = Math.max(-1, Math.min(1, (rq - neutral) / 127));
          let cr, cg, cb;
          if (d >= 0) {
            cr = 220 + (30 - 220) * d;
            cg = 226 + (215 - 226) * d;
            cb = 247 + (255 - 247) * d;
          } else {
            const a = -d;
            cr = 220 + (255 - 220) * a;
            cg = 226 + (170 - 226) * a;
            cb = 247 + (35 - 247) * a;
          }
          const k = 0.22 + 0.78 * inten;
          if (isLightTheme()) {
            const col = d >= 0 ? mix([148, 163, 184], [2, 132, 199], d) : mix([148, 163, 184], [217, 119, 6], -d);
            const c = mix(canvasBgRGB(), col, 0.25 + 0.75 * inten);
            r = c[0]; g = c[1]; b = c[2];
          } else {
            r = Math.round(10 + (cr - 10) * k);
            g = Math.round(12 + (cg - 12) * k);
            b = Math.round(18 + (cb - 18) * k);
          }
        }
        data[idx] = r; data[idx + 1] = g; data[idx + 2] = b; data[idx + 3] = 255;
      }
    }
    octx.putImageData(img, 0, 0);
    ctx.imageSmoothingEnabled = false;
    ctx.drawImage(off, pad, pad, size, size);

    // Pillar boundary lines + labels (A | D | C | B | DM | BR)
    const ticks = (hic.pillar_ticks || []).filter((t) => ATLAS_PILLAR_SHORT[t.key]);
    ctx.strokeStyle = canvasInk(0.28);
    ctx.lineWidth = 1;
    ctx.font = "bold 10px ui-monospace, Menlo, Consolas, monospace";
    ctx.fillStyle = canvasLabel();
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";

    for (const t of ticks) {
      const b0 = Number(t.bin128_start || 0);
      const b1 = Number(t.bin128_end || 0);
      const p0 = pad + b0 * scale;
      const p1 = pad + b1 * scale;
      const mid = (p0 + p1) / 2;
      if (b0 > 0.5) {
        ctx.beginPath();
        ctx.moveTo(p0 + 0.5, pad);
        ctx.lineTo(p0 + 0.5, pad + size);
        ctx.moveTo(pad, p0 + 0.5);
        ctx.lineTo(pad + size, p0 + 0.5);
        ctx.stroke();
      }
      const lbl = ATLAS_PILLAR_SHORT[t.key];
      if (p1 - p0 >= 14) {
        ctx.fillText(lbl, mid, pad / 2);
        ctx.fillText(lbl, pad / 2, mid);
      }
    }
    ctx.strokeStyle = canvasInk(0.4);
    ctx.strokeRect(pad + 0.5, pad + 0.5, size - 1, size - 1);
  }

  function atlasDrawSyntenyCanvas(canvas, synteny, hic, opts) {
    if (!canvas || !synteny) return;
    const gm = synteny.grid_meta || {};
    const G = Number(gm.grid_size) || 128;
    const scale = 4;
    const padL = 32;
    const padB = 24;
    const padT = 14;
    const padR = 10;
    const size = G * scale;
    const ctx = atlasSizeCanvas(canvas, size + padL + padR, size + padT + padB);
    if (!ctx) return;

    ctx.fillStyle = canvasBg();
    ctx.fillRect(0, 0, size + padL + padR, size + padT + padB);

    // 1. Optional Terra Incognita vertical bands (pitch-black + subtle crimson edge)
    const ti = synteny.terra_incognita_bands || {};
    if (opts.showTerra && Array.isArray(ti.bands)) {
      for (const b of ti.bands) {
        const x0 = padL + (Number(b.bin256_start || 0) / 2) * scale;
        const x1 = padL + (Number(b.bin256_end || 0) / 2) * scale;
        const w = Math.max(2, x1 - x0);
        ctx.fillStyle = "rgba(239, 68, 68, 0.13)";
        ctx.fillRect(x0, padT, w, size);
        ctx.strokeStyle = "rgba(239, 68, 68, 0.40)";
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(x0 + 0.5, padT); ctx.lineTo(x0 + 0.5, padT + size);
        ctx.moveTo(x0 + w - 0.5, padT); ctx.lineTo(x0 + w - 0.5, padT + size);
        ctx.stroke();
      }
    }

    // 2. Pillar vertical guides
    const ticks = ((hic && hic.pillar_ticks) || []).filter((t) => ATLAS_PILLAR_SHORT[t.key]);
    ctx.strokeStyle = canvasInk(0.2);
    ctx.lineWidth = 1;
    ctx.font = "bold 10px ui-monospace, Menlo, Consolas, monospace";
    ctx.fillStyle = canvasLabel();
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    for (const t of ticks) {
      const b0 = Number(t.bin128_start || 0);
      const b1 = Number(t.bin128_end || 0);
      const x0 = padL + b0 * scale;
      const x1 = padL + b1 * scale;
      if (b0 > 0.5) {
        ctx.beginPath();
        ctx.moveTo(x0 + 0.5, padT);
        ctx.lineTo(x0 + 0.5, padT + size);
        ctx.stroke();
      }
      if (x1 - x0 >= 14) {
        ctx.fillText(ATLAS_PILLAR_SHORT[t.key], (x0 + x1) / 2, padT + size + padB / 2);
      }
    }

    // 3. Library strata horizontal guides
    const strata = Array.isArray(synteny.library_strata) ? synteny.library_strata : [];
    const nLib = Math.max(1, Number(synteny.n_library_decls) || 1);
    ctx.textAlign = "right";
    for (let s = 0; s < strata.length; s++) {
      const st = strata[s];
      const frac = Number(st.lib_idx_start || 0) / nLib;
      const y = padT + (1 - frac) * size;
      if (s > 0) {
        ctx.strokeStyle = canvasInk(0.12);
        ctx.beginPath();
        ctx.moveTo(padL, y + 0.5);
        ctx.lineTo(padL + size, y + 0.5);
        ctx.stroke();
      }
      const midFrac = ((Number(st.lib_idx_start || 0) + Number(st.lib_idx_end || 0)) / 2) / nLib;
      ctx.fillStyle = canvasLabel();
      ctx.fillText("L" + s, padL - 5, padT + (1 - midFrac) * size);
    }

    // 4. Binned points [proj_bin, lib_bin, total_hits, named_hits, dominant_repo_idx]
    const pts = Array.isArray(synteny.binned_points) ? synteny.binned_points : [];
    for (const pt of pts) {
      const pb = Number(pt[0]);
      const lb = Number(pt[1]);
      const tot = Number(pt[2] || 1);
      const named = Number(pt[3] || 0);
      const rIdx = Number(pt[4] || 0);
      const px = padL + pb * scale;
      const py = padT + (G - 1 - lb) * scale;
      const alpha = Math.min(0.95, 0.22 + Math.log1p(tot) * 0.16);
      ctx.fillStyle = named > 0 ? "#34d399" : (SYNTENY_CORPUS_COLORS[rIdx] || "#38bdf8");
      ctx.globalAlpha = alpha;
      ctx.fillRect(px, py, scale, scale);
    }
    ctx.globalAlpha = 1;

    // 5. Named scatter points [proj_dfs_idx, lib_order_idx, kind_idx, repo_idx, type_nodes]
    const nLive = Math.max(1, Number(synteny.n_live_decls) || 1);
    if (opts.showNamed && Array.isArray(synteny.named_scatter)) {
      for (const ns of synteny.named_scatter) {
        const px = padL + (Number(ns[0]) / nLive) * size;
        const py = padT + (1 - Number(ns[1]) / nLib) * size;
        const rIdx = Number(ns[3] || 0);
        ctx.fillStyle = SYNTENY_CORPUS_COLORS[rIdx] || "#34d399";
        ctx.beginPath();
        ctx.arc(px, py, 2.3, 0, Math.PI * 2);
        ctx.fill();
      }
    }

    // 6. Golden diagonal streaks
    if (opts.showStreaks && Array.isArray(synteny.diagonal_streaks)) {
      ctx.strokeStyle = "#facc15";
      ctx.lineWidth = 2.4;
      for (const ds of synteny.diagonal_streaks) {
        const pr = ds.proj_bin_range || [0, 0];
        const lr = ds.lib_bin_range || [0, 0];
        const x0 = padL + (Number(pr[0]) + 0.5) * scale;
        const x1 = padL + (Number(pr[1]) + 0.5) * scale;
        const y0 = padT + (G - 0.5 - Number(lr[0])) * scale;
        const y1 = padT + (G - 0.5 - Number(lr[1])) * scale;
        ctx.beginPath();
        ctx.moveTo(x0, y0);
        ctx.lineTo(x1, y1);
        ctx.stroke();
      }
    }

    ctx.strokeStyle = canvasInk(0.4);
    ctx.lineWidth = 1;
    ctx.strokeRect(padL + 0.5, padT + 0.5, size - 1, size - 1);
  }

  function atlasTwinRatio(pair) {
    const a = Math.max(1, Number((pair.thm_a && pair.thm_a.value_nodes) || 1));
    const b = Math.max(1, Number((pair.thm_b && pair.thm_b.value_nodes) || 1));
    return Math.max(a / b, b / a);
  }

  function fmtCompact(n) {
    const v = Number(n) || 0;
    if (v >= 1e9) return (v / 1e9).toFixed(1).replace(/\.0$/, "") + "B";
    if (v >= 1e6) return (v / 1e6).toFixed(v >= 1e8 ? 0 : (v >= 1e7 ? 1 : 2)) + "M";
    if (v >= 1e4) return Math.round(v / 1e3) + "K";
    return fmtInt(v);
  }

  async function renderAtlasView(sub) {
    const main = $("#appMain");
    clearEl(main);
    const a = (state.manifest && state.manifest.assets) || {};
    const assetPath = a.atlas;
    if (!assetPath && !a.module_matrix && !a.embedding_2d) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No edge map" }),
        el("p", { textContent: "This build does not include the dependency matrix." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [
      el("div", { className: "spinner" }),
      el("div", { textContent: "Loading…" })
    ]));
    try {
      if (assetPath) renderAtlasBody(await fetchJson(assetPath));
      else if (a.module_matrix) renderModuleMatrixBody(await fetchJson(a.module_matrix));
      else {
        clearEl(main);
        main.appendChild(el("header", { className: "page-head" }, [el("h1", { textContent: "2D Map" })]));
        const host = el("section", { className: "map2d-section", id: "map2dSection" });
        main.appendChild(host);
        await mountMap2d(host);
      }
      if (sub === "map") {
        const sec = $("#map2dSection");
        if (sec) requestAnimationFrame(() => sec.scrollIntoView({ block: "start" }));
      }
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Could not load the edge map" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  // Source spec for one side of a same-statement pair (project side: pinned
  // GitHub blob; library side: documentation link only).
  function atlasTwinSourceSpec(thm, label) {
    if (!thm) return null;
    const srcPath = thm.src_rel_path || thm.module || "";
    const gh = (thm.origin === "project" && srcPath) ? buildGithubUrl(srcPath, thm.line_no) : (safeHref(thm.github_url) || null);
    const docs = /mathlib/i.test(String(thm.origin || "")) && thm.name
      ? "https://leanprover-community.github.io/mathlib4_docs/find/?pattern=" + encodeURIComponent(String(thm.name).replace(/^_root_\./, "")) + "#doc"
      : "";
    return {
      url: gh || "",
      title: thm.name,
      line: thm.line_no || null,
      label,
      peekable: Boolean(gh && isLeanBlob(gh)),
      fallbackUrl: docs,
      fallbackLabel: "Mathlib docs ↗"
    };
  }

  // 32-grid block of a 128-grid contact-map cell (the tray's granularity).
  function atlasHicBlock(hic, cell) {
    const G32 = Number((hic.cell_samples_meta || {}).grid_size) || 32;
    return { G32, r32: Math.floor((cell.by * G32) / cell.N), c32: Math.floor((cell.bx * G32) / cell.N) };
  }

  function atlasHicRing(canvas, hic, cell) {
    const { G32, r32, c32 } = atlasHicBlock(hic, cell);
    const ctx = canvas.getContext("2d");
    if (!ctx) return;
    const step = (cell.N / G32) * 4;
    ctx.strokeStyle = canvasBg();
    ctx.lineWidth = 4;
    ctx.strokeRect(26 + c32 * step, 26 + r32 * step, step, step);
    ctx.strokeStyle = isLightTheme() ? "#0f172a" : "#ffffff";
    ctx.lineWidth = 2;
    ctx.strokeRect(26 + c32 * step, 26 + r32 * step, step, step);
  }

  function openHicTray(tray, canvas, hic, cell, couplingMap, onClose) {
    const { r32, c32 } = atlasHicBlock(hic, cell);
    atlasDrawHicCanvas(canvas, hic, state.atlas.hicMode);
    atlasHicRing(canvas, hic, cell);
    const nLive = Number(hic.n_live_decls) || 1;
    const srcReg = atlasRegionForDfs(hic.regions, Math.floor(((cell.by + 0.5) / cell.N) * nLive));
    const dstReg = atlasRegionForDfs(hic.regions, Math.floor(((cell.bx + 0.5) / cell.N) * nLive));
    const samples = (hic.cell_samples || {})[r32 + "," + c32] || [];
    const regionSamples = (srcReg && dstReg && hic.region_edge_samples) ? (hic.region_edge_samples[srcReg.key + "->" + dstReg.key] || []) : [];
    const rc = (srcReg && dstReg) ? couplingMap.get(srcReg.key + "->" + dstReg.key) : null;
    const cat = hic.bin_catalog || [];
    const rowDecls = cat[cell.by] || [];
    const colDecls = cat[cell.bx] || [];
    clearEl(tray);
    tray.hidden = false;
    tray.appendChild(trayHeader((srcReg ? srcReg.label : "Row " + cell.by) + " → " + (dstReg ? dstReg.label : "Column " + cell.bx), rc ? plural(rc.total, "edge") + " between these parts" : "", () => { tray.hidden = true; atlasDrawHicCanvas(canvas, hic, state.atlas.hicMode); if (onClose) onClose(); }));
    tray.appendChild(el("div", { className: "tray-cols" }, [
      el("div", null, [el("h4", { textContent: "Row: leading declarations" }), ...(rowDecls.length ? rowDecls.map(declTrayRow) : [el("p", { className: "nb-empty", textContent: "None recorded." })])]),
      el("div", null, [el("h4", { textContent: "Column: leading declarations" }), ...(colDecls.length ? colDecls.map(declTrayRow) : [el("p", { className: "nb-empty", textContent: "None recorded." })])])
    ]));
    if (samples.length) {
      tray.appendChild(el("h4", { textContent: "Sample edges in this block" }));
      samples.slice(0, 6).forEach((e) => tray.appendChild(edgeTrayRow(e)));
    } else {
      tray.appendChild(el("p", { className: "nb-empty", textContent: "No edges are recorded in this block." }));
    }
    if (regionSamples.length) {
      tray.appendChild(el("h4", { textContent: "Bridges between these parts" }));
      regionSamples.slice(0, 4).forEach((e) => tray.appendChild(edgeTrayRow(e)));
    }
  }

  // Snap a dot-plot click to the nearest recorded match (within 2 bins).
  function atlasSynSnap(syn, pb, lb) {
    const ms = syn.match_samples || {};
    let key = pb + "," + lb;
    let found = ms[key];
    if (!found) {
      let best = null, bd = Infinity;
      for (let dx = -2; dx <= 2; dx++) {
        for (let dy = -2; dy <= 2; dy++) {
          const k = (pb + dx) + "," + (lb + dy);
          if (ms[k] && dx * dx + dy * dy < bd) { bd = dx * dx + dy * dy; best = k; }
        }
      }
      if (best) { key = best; found = ms[best]; }
    }
    const [kb, kl] = key.split(",").map(Number);
    return { kb, kl, found };
  }

  function atlasSynRing(canvas, syn, kb, kl) {
    const ctx = canvas.getContext("2d");
    if (!ctx) return;
    const G = Number((syn.grid_meta && syn.grid_meta.grid_size) || 128);
    const x = 32 + kb * 4 + 2, y = 14 + (G - 1 - kl) * 4 + 2;
    ctx.beginPath();
    ctx.arc(x, y, 7, 0, Math.PI * 2);
    ctx.strokeStyle = canvasBg();
    ctx.lineWidth = 4;
    ctx.stroke();
    ctx.strokeStyle = isLightTheme() ? "#0f172a" : "#ffffff";
    ctx.lineWidth = 2;
    ctx.stroke();
  }

  function openSyntenyTray(tray, syn, hic, pb, lb, onClose) {
    const { kb, kl, found } = atlasSynSnap(syn, pb, lb);
    const G = Number((syn.grid_meta && syn.grid_meta.grid_size) || 128);
    const nLive = Number(syn.n_live_decls) || 1;
    const reg = atlasRegionForDfs(hic.regions, Math.floor(((kb + 0.5) / G) * nLive));
    const libLabel = (syn.lib_bins || [])[kl] || ("layer " + kl);
    clearEl(tray);
    tray.hidden = false;
    tray.appendChild(trayHeader((reg ? reg.label : "Proof position " + kb) + " ↔ " + libLabel, found ? plural(found.length, "sample match", "sample matches") : "", () => { tray.hidden = true; if (onClose) onClose(); }));
    if (!found || !found.length) {
      tray.appendChild(el("p", { className: "nb-empty", textContent: "No matches are recorded near this point. Try a brighter dot." }));
      return;
    }
    // m = [proj_name, proj_mod, proj_line, lib_name, lib_repo, type_nodes, match_kind]
    for (const mt of found.slice(0, 8)) {
      const [pName, pMod, pLine, lName, lRepo, tn, kind] = mt;
      const docs = /mathlib/i.test(String(lRepo || "")) ? "https://leanprover-community.github.io/mathlib4_docs/find/?pattern=" + encodeURIComponent(String(lName).startsWith("_private.") ? shortName(lName) : String(lName)) + "#doc" : "";
      const pUrl = pMod ? buildGithubUrl(pMod, pLine) : null;
      tray.appendChild(el("div", { className: "tray-row" }, [
        el("div", { className: "tray-main" }, [
          el("span", { className: "tray-name", title: pName + " ↔ " + lName }, [
            el("a", { href: "#item/" + encodeURIComponent(pName), textContent: shortName(pName) }),
            el("span", { className: "tray-arrow", textContent: " ↔ " }),
            el("span", { textContent: shortName(lName) })
          ]),
          el("span", { className: "tray-meta", textContent: [lRepo ? synRepoLabel(lRepo) : null, kind === "k1n" ? "same statement hash" : kind, tn ? "statement: " + plural(tn, "AST node") : null].filter(Boolean).join(" · ") })
        ]),
        el("div", { className: "cir-ins-acts" }, [
          el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(pName), textContent: "Inspect ›" }),
          pUrl ? makeSrcButton(pUrl, pName, { className: "btn sm", text: "Source" }) : null,
          docs ? el("a", { className: "btn sm", href: docs, target: "_blank", rel: "noopener noreferrer", textContent: "Mathlib docs ↗" }) : null
        ])
      ]));
    }
  }

  // v2.4 atlas/map self-test (owned by the atlas pass).
  async function runV24AtlasSelfTest(assert) {
    const m = state.manifest || {};
    const a = m.assets || {};
    const tick = (ms) => new Promise((r) => setTimeout(r, ms || 0));
    const saved = Object.assign({}, state.atlas);
    const savedMap = { layer: state.map2d.layer, color: state.map2d.color };

    // Item 5 and 22a: map lede wording and the Comments % color mode, per layer.
    if (a.embedding_2d) {
      const emb = await fetchJson(a.embedding_2d);
      const layers = emb.layers || {};
      for (const [k, layer] of Object.entries(layers)) {
        if (!layer || !Array.isArray(layer.points) || !layer.points.length) continue;
        const s = map2dDriftSentence(k, layer);
        if (k === "landmarks") {
          assert(!s || /^\d+\.\d% of declarations with 1,000 or more declarations in their exclusive subtree have/.test(s), "landmarks lede keeps the exclusive-subtree wording (" + s + ")");
        } else {
          assert(!s || (new RegExp("^\\d+\\.\\d% of " + ({ modules: "modules", folders: "folders", clusters_141: "clusters" }[k] || "points") + " have their nearest neighbor in a different folder\\.$").test(s) && !/exclusive subtree/.test(s)), k + " lede names its own unit (" + s + ")");
        }
        const F = layerFieldIndex(layer);
        if (F.comment_pct != null) {
          const any = layer.points.some((p) => Number(p[F.comment_pct]) > 0);
          assert(colorModesFor(layer).some((md) => md.key === "comments") === any, k + ": Comments % is offered only when some comment value is above 0");
        }
      }
    }

    if (a.atlas) {
      await renderAtlasView("");
      const doc = await fetchJson(a.atlas);
      const main = $("#appMain");
      const rendered = $("#map2dSection > .section-lede");
      if (rendered) {
        const lk = state.map2d.layer;
        assert(lk === "landmarks" || !/exclusive subtree/.test(rendered.textContent), "rendered map lede uses the exclusive-subtree wording only on landmarks");
      }
      // Item 10: dot-plot title, subtitle and legend tokens.
      const synCard = ($("#syntenyCanvas") || {}).closest ? $("#syntenyCanvas").closest(".atlas-card") : null;
      if (synCard) {
        const h3 = synCard.querySelector("h3");
        assert(h3 && h3.textContent === "Library and benchmark overlap", "dot plot is titled Library and benchmark overlap");
        const sub = $("#synSubtitle");
        const nLib = Number((doc.synteny || {}).n_library_decls || 0);
        assert(!nLib || (sub && sub.textContent.startsWith(fmtInt(nLib) + " declarations across ")), "dot plot subtitle reads the library size from data (" + (sub ? sub.textContent : "none") + ")");
        const legendTxt = $$(".syn-corpus", synCard).map((n) => n.textContent).join(" | ");
        assert(!/strong_src|library_other|mathlib4|lean4/.test(legendTxt), "dot plot legend uses readable corpus names (" + legendTxt + ")");
      }
      // Item 10: scope chip and the external-library note.
      const chips = $$("#psiScope button").map((b) => b.textContent);
      if (chips.length) {
        assert(chips.includes("External libraries") && !/Against Mathlib/.test(main.textContent || ""), "proof similarity scope chip reads External libraries");
        const hs = ((doc.alien_twins || {}).histograms_by_scope) || {};
        const tot = (k) => Number(((hs[k] || {}).counts || {}).total);
        const rest = tot("all") - tot("intra") - tot("cross_repo");
        const note = $("#psiScopeNote");
        if (Number.isFinite(rest) && rest > 0) assert(note && note.textContent.includes(plural(rest, "pair")) && /both theorems in external libraries/.test(note.textContent), "scope note counts the " + fmtInt(rest) + " pairs within external libraries");
        else assert(!note, "no scope note when the scopes add up");
      }
      // Item 8: statement hash and AST-node wording on pair cards.
      const card = $("#twinsGridHost .twin-card");
      if (card) {
        const txt = card.textContent || "";
        const hash = card.querySelector(".psi-hash");
        assert(!/Signature k1|proof size \d|statement size \d|k1n:/.test(txt) && hash && /^Statement hash \S+/.test(hash.textContent), "pair cards say Statement hash and AST nodes (" + (hash ? hash.textContent : "") + ")");
        const meta = $$(".twin-side-top .twin-side-meta", card).map((n) => n.textContent);
        assert(meta.length === 2 && meta.every((t) => /^proof: [\d,]+ AST nodes? · [\d,]+ references?$/.test(t)), "pair sides read proof: N AST nodes · M references (" + meta.join(" / ") + ")");
      }
    }

    // Item 19b: full screen grows the matrix canvases to fill the free square and restores on exit.
    const fsCheck = async (canvas, label) => {
      const card = canvas && canvas.closest(".atlas-card");
      const btn = card && card.querySelector(".fs-btn");
      if (!btn) return;
      const before = canvas.getBoundingClientRect().width;
      const logW = canvas._logW || canvas.width;
      btn.click();
      for (let i = 0; i < 40 && !canvas.dataset.fsSide; i++) await tick(50);
      const side = Number(canvas.dataset.fsSide || 0);
      const w = canvas.getBoundingClientRect().width;
      const cs = getComputedStyle(canvas.parentNode);
      const free = Math.min(canvas.parentNode.clientWidth - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight), window.innerHeight);
      assert(card.classList.contains("fs-on") && side > 0 && Math.abs(w - side) <= 1 && (free < before + 40 || w > before + 20), label + " canvas fills the full-screen square (" + Math.round(before) + "px to " + Math.round(w) + "px)");
      btn.click();
      for (let i = 0; i < 40 && canvas.dataset.fsSide; i++) await tick(50);
      assert(!card.classList.contains("fs-on") && canvas.style.width === "" && (canvas._logW || canvas.width) === logW && canvas.width === logW && Math.abs(canvas.getBoundingClientRect().width - before) <= 1, label + " canvas restores its inline size after full screen");
    };
    if (a.atlas) {
      await fsCheck($("#hicCanvas"), "contact map");
      await fsCheck($("#syntenyCanvas"), "dot plot");
    } else if (a.module_matrix) {
      await renderAtlasView("");
      await fsCheck($("#moduleMatrixCanvas"), "module matrix");
    }
    Object.assign(state.atlas, saved);
    Object.assign(state.map2d, savedMap);
  }

  // v2.3 atlas self-test (owned by the atlas pass).
  async function runV23AtlasSelfTest(assert) {
    const m = state.manifest || {};
    const a = m.assets || {};
    const tick = (ms) => new Promise((r) => setTimeout(r, ms || 0));
    const saved = Object.assign({}, state.atlas);
    if (a.atlas) {
      await renderAtlasView("");
      const main = $("#appMain");
      const h2s = $$(".section-hdr h2", main).map((h) => h.textContent);
      assert(h2s.includes("Proof similarity index") && !/Same Statement, Different Proof/.test(main.textContent || ""), "edge map section is titled Proof similarity index");
      const hicCanvas = $("#hicCanvas");
      const synCanvas = $("#syntenyCanvas");
      const mapSec = $("#map2dSection");
      const intact = () => hicCanvas && hicCanvas.isConnected && synCanvas.isConnected && (!mapSec || mapSec.isConnected);

      // P0-1: the contact-map mode updates the canvas in place.
      const densBtn = $$("#hicModeSeg button").find((b) => b.dataset.mode === "density");
      if (densBtn) {
        densBtn.click();
        assert(intact() && state.atlas.hicMode === "density" && densBtn.getAttribute("aria-pressed") === "true" && /log scale/.test(($("#hicLegend") || {}).textContent || ""), "contact-map mode switches in place without rebuilding the page");
        $$("#hicModeSeg button").find((b) => b.dataset.mode === "ratio").click();
      }

      // P1-1: clicking a cell locks the readout; a second click toggles it off.
      if (hicCanvas) {
        const rc = hicCanvas.getBoundingClientRect();
        const at = (fx, fy) => ({ bubbles: true, clientX: rc.left + rc.width * fx, clientY: rc.top + rc.height * fy });
        hicCanvas.dispatchEvent(new MouseEvent("click", at(0.3, 0.3)));
        const locked = $("#hicReadout").textContent;
        hicCanvas.dispatchEvent(new MouseEvent("mousemove", at(0.7, 0.6)));
        assert(!$("#hicTray").hidden && $("#hicReadout").textContent === locked && $("#hicReadout").classList.contains("locked"), "contact-map readout stays on the selected cell while its tray is open");
        hicCanvas.dispatchEvent(new MouseEvent("click", at(0.3, 0.3)));
        assert($("#hicTray").hidden && !$("#hicReadout").classList.contains("locked"), "clicking the selected contact-map cell again closes its tray");
      }
      const syn = (await fetchJson(a.atlas)).synteny || {};
      const sKeys = Object.keys(syn.match_samples || {});
      if (synCanvas && sKeys.length) {
        const [pb, lb] = sKeys[0].split(",").map(Number);
        const G = Number((syn.grid_meta && syn.grid_meta.grid_size) || 128);
        const rc = synCanvas.getBoundingClientRect();
        const ev = { bubbles: true, clientX: rc.left + ((32 + pb * 4 + 2) / synCanvas.width) * rc.width, clientY: rc.top + ((14 + (G - 1 - lb) * 4 + 2) / synCanvas.height) * rc.height };
        synCanvas.dispatchEvent(new MouseEvent("click", ev));
        const open = !$("#synTray").hidden && synCanvas.dataset.sel === pb + "," + lb;
        synCanvas.dispatchEvent(new MouseEvent("click", ev));
        assert(open && $("#synTray").hidden && !synCanvas.dataset.sel, "dot-plot marks the selected match and a second click clears it");
      }

      // Proof similarity index: histogram, scope, scale, bins, sort, filter.
      const aliens = (await fetchJson(a.atlas)).alien_twins || {};
      const hist = $("#psiHist");
      if (hist && !hist.hidden) {
        const pool = () => (($("#psiHist .psi-pool") || {}).textContent || "");
        assert($$("#psiHist .hist-bar-col").length === 20 && /^All pairs \([\d,]+\)$/.test(pool()), "similarity histogram has 20 bins and names the plotted pool");
        const scopeBtn = (k) => $$("#psiScope button").find((b) => b.dataset.k === k);
        if (aliens.histograms_by_scope && aliens.histograms_by_scope.intra && scopeBtn("intra")) {
          const before = $$("#psiHist .hist-bar-col").map((b) => b.title).join("|");
          scopeBtn("intra").click();
          const after = $$("#psiHist .hist-bar-col").map((b) => b.title).join("|");
          assert(/^Within project \([\d,]+\)$/.test(pool()) && before !== after && intact() && $("#psiHist") === hist, "histogram follows the scope chips in place");
          scopeBtn("all").click();
        }
        const h0 = () => parseFloat(($("#psiHist .hist-bar-col .hist-bar") || { style: {} }).style.height) || 0;
        const linH = h0();
        const logBtn = $$("#psiScale button").find((b) => b.dataset.k === "log");
        if (logBtn) {
          logBtn.click();
          const logH = h0();
          const logNow = $$("#psiScale button").find((b) => b.dataset.k === "log");
          assert(logNow && logNow.getAttribute("aria-pressed") === "true" && logH > linH, "log scale lifts the small low-overlap bins (" + linH + "% to " + logH + "%)");
          $$("#psiScale button").find((b) => b.dataset.k === "linear").click();
        }
        const bin0 = $("#psiHist .hist-bar-col");
        bin0.click();
        const js = $$("#twinsGridHost .twin-card").map((c) => Number(c.dataset.j));
        assert(bin0.classList.contains("sel") && bin0.getAttribute("aria-pressed") === "true" && js.every((j) => j < 0.05) && /^Showing [\d,]+ of [\d,]+ sampled representative pairs/.test($("#psiCount").textContent), "clicking a histogram bar filters the sampled pairs to that bin");
        bin0.click();
        assert(!bin0.classList.contains("sel"), "clicking the selected bar again clears the bin filter");
        const highChip = $$("#psiBand button").find((b) => b.dataset.k === "clone");
        if (highChip) {
          highChip.click();
          const hj = $$("#twinsGridHost .twin-card").map((c) => Number(c.dataset.j));
          assert((hj.length > 0 || !(aliens.top_clone_pairs_intra || []).length) && hj.every((j) => j >= 0.7) && $$("#psiHist .hist-bar-col.dim").length === 14, "High band chip filters pairs and dims the other bars");
          $$("#psiBand button").find((b) => b.dataset.k === "all").click();
        }
        const total = $$("#twinsGridHost .twin-card").length;
        const nSampled = new Set(["top_alien_pairs", "top_alien_pairs_intra", "top_alien_pairs_cross_repo", "top_variant_pairs_intra", "top_variant_pairs_cross_repo", "top_clone_pairs_intra", "top_clone_pairs_cross_repo"]
          .flatMap((k) => (aliens[k] || []).map((p) => [p.thm_a && p.thm_a.name, p.thm_b && p.thm_b.name].sort().join("|")))).size;
        assert(total === nSampled && /from [\d,]+ total pairs in this scope/.test($("#psiCount").textContent), "all sampled pools load, deduplicated (" + total + " pairs)");
        if ((aliens.top_alien_pairs_intra || []).some((p) => (p.thm_a && p.thm_a.wrapper_tag) || (p.thm_b && p.thm_b.wrapper_tag))) {
          assert($$("#twinsGridHost .psi-wrap-pill").length > 0, "pairs with a wrapper proof show a quiet pill");
        }
        // Sort direction flip keeps canvases and flips the order.
        const dirBtn = $("#psiDir");
        const first = () => ($("#twinsGridHost .twin-card") || { dataset: {} }).dataset.j;
        const j1 = first();
        dirBtn.click();
        const j2 = first();
        assert(dirBtn.getAttribute("aria-pressed") === "true" && /Desc/.test(dirBtn.textContent) && Number(j2) >= Number(j1) && intact(), "sort direction flips in place");
        dirBtn.click();
        const sortSel = $("#psiSort");
        assert(sortSel && sortSel.options.length === 7, "pair sort offers 7 keys");
        // Typing in the filter keeps focus on the same input.
        const inp = $("#psiFilter");
        const probe = $("#twinsGridHost .twin-card .twin-side-name");
        if (inp && probe) {
          inp.focus();
          inp.value = probe.textContent.slice(0, 12);
          inp.dispatchEvent(new Event("input", { bubbles: true }));
          await tick(0);
          const n = $$("#twinsGridHost .twin-card").length;
          assert(document.activeElement === inp && $("#psiFilter") === inp && n >= 1 && n <= total && intact(), "pair filter narrows the list while keeping focus");
          $("#psiClear").click();
          assert(inp.value === "" && $$("#twinsGridHost .twin-card").length === total && $("#psiClear").disabled, "Clear resets the pair filters");
        }
        const shell = $("#proofSimilarity").cloneNode(true);
        shell.querySelectorAll(".twins-grid, select").forEach((n) => n.remove());
        assert(!UI_SLOP_WORDING.test(shell.textContent || ""), "proof similarity copy reads plainly");
      }
    }

    // 2D map: wheel passthrough, Ctrl+wheel zoom, empty click clears, no spinner on color change.
    if (a.embedding_2d) {
      const host = $("#map2dSection") || (await renderAtlasView("map"), $("#map2dSection"));
      for (let i = 0; i < 60 && !(host && host._map2d); i++) await tick(50);
      const api = host && host._map2d;
      if (api) {
        api.resetView();
        const plain = new WheelEvent("wheel", { bubbles: true, cancelable: true, deltaY: 120, clientX: 10, clientY: 10 });
        api.canvas.dispatchEvent(plain);
        assert(!plain.defaultPrevented && Math.abs(api.state.zoom - 1) < 0.01 && host.querySelector(".map-zoom-hint.on"), "plain scroll over an unzoomed map scrolls the page and shows a zoom hint");
        const rc = api.canvas.getBoundingClientRect();
        const ctrl = new WheelEvent("wheel", { bubbles: true, cancelable: true, deltaY: -200, ctrlKey: true, clientX: rc.left + rc.width / 2, clientY: rc.top + rc.height / 2 });
        api.canvas.dispatchEvent(ctrl);
        assert(ctrl.defaultPrevented && api.state.zoom > 1.01, "Ctrl + scroll zooms the map");
        api.resetView();
        api.pick(0);
        let cleared = false;
        for (const [fx, fy] of [[0.01, 0.01], [0.99, 0.01], [0.01, 0.99], [0.99, 0.99]]) {
          const pe = { bubbles: true, clientX: rc.left + rc.width * fx, clientY: rc.top + rc.height * fy, button: 0, pointerId: 9, pointerType: "mouse" };
          api.canvas.dispatchEvent(new PointerEvent("pointerdown", pe));
          api.canvas.dispatchEvent(new PointerEvent("pointerup", pe));
          if (api.state.sel === -1) { cleared = true; break; }
          api.pick(0);
        }
        assert(cleared, "clicking empty map space clears the selection");
        const find = host.querySelector(".map-find");
        const colorSel = host.querySelector(".map-color");
        if (find && colorSel && colorSel.options.length > 1) {
          find.value = "zz";
          find.dispatchEvent(new Event("input", { bubbles: true }));
          const prev = colorSel.value;
          colorSel.value = Array.from(colorSel.options).find((op) => op.value !== prev).value;
          colorSel.dispatchEvent(new Event("change", { bubbles: true }));
          assert(!host.querySelector(".loading-card") && (host.querySelector(".map-find") || {}).value === "zz" && host.querySelector(".map2d-canvas"), "changing the map color keeps the find text without a loading flash");
          const cs2 = host.querySelector(".map-color");
          cs2.value = prev;
          cs2.dispatchEvent(new Event("change", { bubbles: true }));
          const f2 = host.querySelector(".map-find");
          f2.value = "";
          f2.dispatchEvent(new Event("input", { bubbles: true }));
        }
      }
    }
    Object.assign(state.atlas, saved);
  }

  // Sampled pair pools written by the atlas step (all three overlap bands).
  const TWIN_POOL_KEYS = ["top_alien_pairs", "top_alien_pairs_intra", "top_alien_pairs_cross_repo", "top_variant_pairs_intra", "top_variant_pairs_cross_repo", "top_clone_pairs_intra", "top_clone_pairs_cross_repo"];
  const TWIN_SORTS = [
    ["jaccard", "Proof-only overlap J", "asc"],
    ["ratio", "Size ratio", "desc"],
    ["type_nodes", "Statement size", "desc"],
    ["shared", "Shared lemmas", "desc"],
    ["proof_a", "Proof A size", "desc"],
    ["proof_b", "Proof B size", "desc"],
    ["name", "Name", "asc"]
  ];
  const TWIN_BANDS = [["all", "All"], ["alien", "Low (<0.20)"], ["variant", "Partial (0.20–0.70)"], ["clone", "High (≥0.70)"]];
  const TWIN_BAND_SHORT = { alien: "Low overlap", variant: "Partial overlap", clone: "High overlap" };
  // [state key, chip label, histograms_by_scope key, pool label]
  const TWIN_SCOPES = [["all", "All", "all", "All pairs"], ["intra", "Within project", "intra", "Within project"], ["cross", "External libraries", "cross_repo", "External libraries"]];
  const WRAPPER_TAGS = { inferInstance: "inferInstance", thin_wrapper: "thin wrapper" };

  function atlasBinBand(idx) { return idx < 4 ? "alien" : (idx < 14 ? "variant" : "clone"); }
  function atlasJBin(j) { return Math.max(0, Math.min(19, Math.floor(Number(j || 0) * 20 + 1e-9))); }

  function atlasTwinPool(aliens) {
    const th = aliens.thresholds || {};
    const vMin = Number(th.variant_min_jaccard ?? 0.2), cMin = Number(th.clone_min_jaccard ?? 0.7);
    const seen = new Set();
    const out = [];
    for (const k of TWIN_POOL_KEYS) {
      for (const p of (Array.isArray(aliens[k]) ? aliens[k] : [])) {
        if (!p || !p.thm_a || !p.thm_b) continue;
        const key = [String(p.thm_a.name), String(p.thm_b.name)].sort().join("|");
        if (seen.has(key)) continue;
        seen.add(key);
        const j = Number(p.jaccard || 0);
        const band = (p.band === "alien" || p.band === "variant" || p.band === "clone") ? p.band : (j < vMin ? "alien" : (j < cMin ? "variant" : "clone"));
        const cross = p.is_cross_repo === true || p.pair_scope === "cross_repo";
        const hay = [p.thm_a, p.thm_b].flatMap((t) => [t.name, t.module, t.origin, t.src_rel_path, t.wrapper_tag ? WRAPPER_TAGS[t.wrapper_tag] || t.wrapper_tag : ""]).concat([p.sighash]).filter(Boolean).join(" ").toLowerCase();
        out.push({ p, j, band, bin: atlasJBin(j), cross, hay });
      }
    }
    return out;
  }

  // Histogram for one scope, falling back to the all-pairs histogram.
  function atlasScopeHist(aliens, scopeKey) {
    const fromBins = (bins, counts, exact) => {
      const b = bins.map((n) => Number(n) || 0);
      const sum = b.reduce((s, v) => s + v, 0);
      return { bins: b, total: Number((counts || {}).total) || sum, counts: counts || null, exact };
    };
    const h = (aliens.histograms_by_scope || {})[scopeKey];
    if (h && Array.isArray(h.bins_20) && h.bins_20.length === 20) return fromBins(h.bins_20, h.counts, true);
    const all = Array.isArray(aliens.jaccard_histogram_20bins) && aliens.jaccard_histogram_20bins.length === 20 ? aliens.jaccard_histogram_20bins : null;
    if (!all) return null;
    const ap = (aliens.partitions || {}).all_sampled_pairs || {};
    const counts = ap.alien_proof != null ? { alien: ap.alien_proof, variant: ap.variant, clone: ap.clone } : null;
    return fromBins(all, counts, scopeKey === "all");
  }

  // Dot-plot corpora: readable names, with "strong_src:<repo>" folded into <repo>.
  const SYN_REPO_LABELS = { mathlib4: "Mathlib", lean4: "Lean 4", batteries: "Batteries", library_other: "Other libraries" };
  const SYN_LIBRARY_REPOS = ["lean4", "mathlib4", "batteries", "library_other"];
  function synRepoLabel(repo) {
    const r = String(repo || "").replace(/^strong_src:/, "");
    return SYN_REPO_LABELS[r] || r.replace(/_/g, " ");
  }
  function synCorpusGroups(syn) {
    const byCorpus = ((syn && syn.hit_totals) || {}).by_corpus || {};
    const repos = ((syn && syn.grid_meta) || {}).repos || [];
    const groups = new Map();
    const add = (repo, key, n) => {
      if (!groups.has(repo)) {
        const idx = repos.indexOf(repo);
        groups.set(repo, { repo, label: synRepoLabel(repo), keys: [], count: 0, library: SYN_LIBRARY_REPOS.includes(repo), color: SYNTENY_CORPUS_COLORS[idx >= 0 ? idx : SYNTENY_CORPUS_COLORS.length - 1] });
      }
      const g = groups.get(repo);
      if (key) g.keys.push(key);
      g.count += Number(n) || 0;
    };
    repos.forEach((r) => add(r, "", 0));
    Object.entries(byCorpus).forEach(([k, v]) => add(String(k).replace(/^strong_src:/, ""), k, v));
    return Array.from(groups.values()).sort((a, b) => b.count - a.count || a.label.localeCompare(b.label));
  }
  function synSubtitleText(nLib, groups) {
    if (!nLib) return "";
    const libs = SYN_LIBRARY_REPOS.filter((r) => r !== "library_other" && groups.some((g) => g.repo === r)).map(synRepoLabel);
    const parts = libs.concat(groups.some((g) => !g.library) ? ["benchmark proofs"] : []);
    if (!parts.length) return fmtInt(nLib) + " library declarations";
    const list = parts.length <= 2 ? parts.join(" and ") : parts.slice(0, -1).join(", ") + ", and " + parts[parts.length - 1];
    return plural(nLib, "declaration") + " across " + list;
  }

  function renderAtlasBody(doc) {
    const main = $("#appMain");
    clearEl(main);
    const A = state.atlas;

    const hic = doc.hic_matrix || {};
    const et = hic.edge_totals || {};
    const aliens = doc.alien_twins || {};
    const ac = aliens.counts || {};
    const ap = aliens.partitions || {};
    const syn = doc.synteny || {};
    const ht = syn.hit_totals || {};
    const ti = syn.terra_incognita_bands || {};
    const totalEdges = Number(et.total_streamed || 0);
    const nLib = Number(syn.n_library_decls || 0);
    const hasMap2d = Boolean(state.manifest && state.manifest.assets && state.manifest.assets.embedding_2d);

    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Dependency matrix and proof similarity" }),
      trustBadge("tool"),
      el("p", { className: "page-lede", textContent: (hasMap2d ? "Four" : "Three") + " views of the same dependency graph. Declarations are laid out in one fixed order (" + fmtInt(hic.n_live_decls || 0) + " reachable declarations, grouped by the part of the proof that owns them), so each part sits in one contiguous block." }),
      el("p", { className: "quiet-note", textContent: "Several numbers below rely on a normalized statement hash: a fingerprint of a declaration's statement with names erased. Two theorems with the same hash state the same thing up to renaming." })
    ]));

    // Key numbers
    const allAliens = (ap.all_sampled_pairs && ap.all_sampled_pairs.alien_proof) || 0;
    const crossAliens = (ap.cross_repo_pairs && ap.cross_repo_pairs.alien_proof) || 0;
    main.appendChild(el("section", { className: "kpi-strip" }, [
      { label: "Dependency edges", val: fmtInt(totalEdges), sub: fmtInt(et.type_only || 0) + " in statements · " + fmtInt(et.value_only || 0) + " in proofs · " + fmtInt(et.both || 0) + " both" +
        (Number(et.unmapped_nonlive) > 0 ? " (" + fmtInt(Number(et.type_only || 0) + Number(et.value_only || 0) + Number(et.both || 0)) + " live edges; the other " + plural(Number(et.unmapped_nonlive), "edge") + (Number(hic.total_decls_in_db) > Number(hic.n_live_decls) ? " sit on " + plural(Number(hic.total_decls_in_db) - Number(hic.n_live_decls), "unreachable declaration") : " sit on unreachable declarations") + ")" : "") },
      { label: "Shared signatures", val: fmtInt(ac.nontrivial_collision_buckets || 0), sub: "groups of theorems with the same statement shape" },
      { label: "Low-overlap proof pairs", val: fmtInt(allAliens), sub: "same statement, under 20% shared lemmas · " + fmtInt(crossAliens) + " against external libraries" },
      { label: "Library matches", val: fmtInt(ht.total_matches || 0), sub: (() => {
        const corpusHits = Object.values(ht.by_corpus || {}).reduce((s, v) => s + (Number(v) || 0), 0);
        return fmtInt(ht.named_matches || 0) + " by name · unique matched declarations" +
          (corpusHits > Number(ht.total_matches || 0) ? "; the legend counts " + fmtInt(corpusHits) + " library hits because one declaration can match several libraries" : "");
      })() },
      { label: "Unmatched regions", val: fmtInt(ti.zero_named_match_bins_256 || 0) + " of " + fmtInt(ti.eligible_project_bins_256 || 0), sub: (ti.zero_named_share_pct != null ? ti.zero_named_share_pct + "% of the ordering has no named Mathlib match" : "no named Mathlib match") }
    ].map((k) => el("div", { className: "kpi-card" }, [
      el("div", { className: "kpi-val", textContent: k.val }),
      el("div", { className: "kpi-label", textContent: k.label }),
      k.sub ? el("div", { className: "kpi-sub", textContent: k.sub }) : null
    ]))));

    // Edge contact map + Mathlib overlap dot-plot
    const pillarTicks = (hic.pillar_ticks || []).filter((t) => ATLAS_PILLAR_SHORT[t.key] && /^pillar_/.test(t.key));
    const pillarLetters = pillarTicks.map((t) => ATLAS_PILLAR_SHORT[t.key]);
    const joinLetters = (xs) => xs.length <= 1 ? (xs[0] || "") : xs.slice(0, -1).join(", ") + " and " + xs[xs.length - 1];
    const hicExplain = "All " + fmtCompact(totalEdges) + " directed edges. Rows and columns are slices of the declarations in dominator-tree order (a depth-first walk), and a cell counts edges from declarations in its row to declarations in its column. Most edges point forward to declarations listed later, above the diagonal; the sparser lower-left holds edges back into earlier parts" +
      (pillarLetters.length >= 2 ? ", and empty strips between columns " + joinLetters(pillarLetters) + " show those parts rarely use each other." : ".");
    const partLegend = (hic.pillar_ticks || []).filter((t) => ATLAS_PILLAR_SHORT[t.key]).map((t) => ATLAS_PILLAR_SHORT[t.key]).filter((c, i, arr) => arr.indexOf(c) === i)
      .map((c) => c + " " + (PART_NAMES[c] || c)).join(" · ");

    const HIC_HINT = "Hover a cell to see which parts it connects; click it to list the declarations and edges inside.";
    const hicCanvas = el("canvas", { id: "hicCanvas", className: "atlas-canvas", "aria-label": "Edge contact map" });
    const hicReadout = el("div", { id: "hicReadout", className: "atlas-readout", textContent: HIC_HINT });
    const hicTray = el("div", { className: "cell-tray", id: "hicTray", hidden: true });
    const hicLegend = el("div", { className: "atlas-legend", id: "hicLegend" });
    let hicSel = null; // selected 128-grid cell while its tray is open
    const drawHic = () => {
      atlasDrawHicCanvas(hicCanvas, hic, A.hicMode);
      if (hicSel) atlasHicRing(hicCanvas, hic, hicSel);
    };
    const fillHicLegend = () => {
      clearEl(hicLegend);
      (A.hicMode === "ratio" ? [
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#1ed7ff" } }), "Mostly statement edges"]),
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#dce2f7" } }), "Balanced"]),
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#ffaa23" } }), "Mostly proof edges"]),
        et.diagonal_256_share_pct != null ? el("span", { textContent: "Near the diagonal: " + et.diagonal_256_share_pct + "%" }) : null
      ] : [
        el("span", { textContent: "Brighter cells hold more edges (log scale)." })
      ]).forEach((n) => { if (n) hicLegend.appendChild(n); });
    };
    fillHicLegend();

    // Mode switch redraws the canvas in place (no page rebuild).
    const hicModeSeg = el("div", { className: "seg", id: "hicModeSeg", role: "group", "aria-label": "Contact map coloring" }, [
      ["ratio", "Statements vs proofs"],
      ["density", "Density"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: A.hicMode === k ? "active" : "", textContent: lbl, "data-mode": k, "aria-pressed": A.hicMode === k ? "true" : "false",
      onclick: () => {
        if (A.hicMode === k) return;
        A.hicMode = k;
        $$("button", hicModeSeg).forEach((b) => { const on = b.dataset.mode === k; b.classList.toggle("active", on); b.setAttribute("aria-pressed", on ? "true" : "false"); });
        fillHicLegend();
        drawHic();
      }
    })));

    const fsHic = el("span");
    const hicCard = el("section", { className: "atlas-card" }, [
      el("div", { className: "atlas-card-hd" }, [
        el("h3", { textContent: "Edge contact map" }),
        el("div", { className: "atlas-card-tools" }, [hicModeSeg, fsHic])
      ]),
      el("p", { className: "atlas-explain", textContent: hicExplain }),
      hicLegend,
      el("div", { className: "atlas-canvas-wrap" }, [hicCanvas]),
      el("p", { className: "atlas-axis", textContent: "Rows use columns." + (partLegend ? " Parts: " + partLegend + "." : "") }),
      hicReadout,
      hicTray
    ]);

    const SYN_HINT = "Hover the plot to see which part of the proof and which library layer a point compares; click a dot to list the matches.";
    const synCanvas = el("canvas", { id: "syntenyCanvas", className: "atlas-canvas", "aria-label": "Library and benchmark overlap dot plot" });
    const synReadout = el("div", { id: "syntenyReadout", className: "atlas-readout", textContent: SYN_HINT });
    const synTray = el("div", { className: "cell-tray", id: "synTray", hidden: true });
    let synSel = null; // { kb, kl } while its tray is open
    const drawSyn = () => {
      atlasDrawSyntenyCanvas(synCanvas, syn, hic, A);
      if (synSel) atlasSynRing(synCanvas, syn, synSel.kb, synSel.kl);
    };

    const synToggle = (key, label) => el("label", { className: "atlas-toggle" }, [
      el("input", { type: "checkbox", checked: A[key], onchange: (ev) => { A[key] = ev.target.checked; drawSyn(); } }),
      label
    ]);
    const synToggles = el("div", { className: "atlas-toggles" }, [
      synToggle("showTerra", "Unmatched regions"),
      synToggle("showStreaks", "Diagonal runs"),
      synToggle("showNamed", "Name matches")
    ]);

    const synGroups = synCorpusGroups(syn);
    const corpusPills = synGroups.filter((g) => g.count > 0).map((g) =>
      el("span", { className: "syn-corpus", title: g.keys.join(" + ") + ": " + plural(g.count, "match", "matches") }, [el("i", { className: "atlas-swatch", style: { background: g.color } }), g.label + " " + fmtInt(g.count)])
    );
    const synSubtitle = synSubtitleText(nLib, synGroups);

    const fsSyn = el("span");
    const synCard = el("section", { className: "atlas-card" }, [
      el("div", { className: "atlas-card-hd" }, [
        el("div", { className: "syn-titles" }, [
          el("h3", { textContent: "Library and benchmark overlap" }),
          synSubtitle ? el("p", { className: "syn-subtitle", id: "synSubtitle", textContent: synSubtitle }) : null
        ]),
        el("div", { className: "atlas-card-tools" }, [synToggles, fsSyn])
      ]),
      el("p", { className: "atlas-explain", textContent: "Compares this proof's statement hashes against those declarations. Each dot is a match; a diagonal run follows the library in order, and shaded columns have no match by name." }),
      el("div", { className: "atlas-legend" }, [
        ...corpusPills,
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#facc15" } }), "Diagonal runs (" + fmtInt((syn.diagonal_streaks || []).length) + ")"])
      ]),
      el("div", { className: "atlas-canvas-wrap" }, [synCanvas]),
      synReadout,
      synTray
    ]);

    fsHic.replaceWith(fullscreenButton(hicCard, atlasFsFit(hicCard, hicCanvas, () => drawHic())));
    fsSyn.replaceWith(fullscreenButton(synCard, atlasFsFit(synCard, synCanvas, () => drawSyn())));
    main.appendChild(el("div", { className: "atlas-grid" }, [hicCard, synCard]));

    drawHic();
    drawSyn();

    // Contact map hover readout
    const couplingMap = new Map();
    for (const rc of (hic.region_couplings || [])) {
      couplingMap.set(rc.src_region + "->" + rc.dst_region, rc);
    }
    const hicCellText = (bx, by, N) => {
      const tile = hic.tile_128 || {};
      const tq = Number((tile.total_log1p_q8 && tile.total_log1p_q8[by] && tile.total_log1p_q8[by][bx]) || 0);
      const rq = Number((tile.ratio_diverging_q8 && tile.ratio_diverging_q8[by] && tile.ratio_diverging_q8[by][bx]) ?? (tile.neutral_ratio_q8 ?? 128));
      const estEdges = tq > 0 ? Math.round(Math.expm1((tq / 255) * Number(tile.max_log1p || 1))) : 0;
      const ratioNat = ((rq - Number(tile.neutral_ratio_q8 ?? 128)) / 127) * Number(tile.ratio_clip_nat || 3.5);
      const nLive = Number(hic.n_live_decls) || 1;
      const srcReg = atlasRegionForDfs(hic.regions, Math.floor(((by + 0.5) / N) * nLive));
      const dstReg = atlasRegionForDfs(hic.regions, Math.floor(((bx + 0.5) / N) * nLive));
      const rc = (srcReg && dstReg) ? couplingMap.get(srcReg.key + "->" + dstReg.key) : null;
      const regTxt = (srcReg ? srcReg.label : "row " + by) + " → " + (dstReg ? dstReg.label : "column " + bx);
      const lean = Math.abs(ratioNat) < 0.25 ? "balanced" : (ratioNat > 0 ? "mostly statement edges" : "mostly proof edges");
      const rcTxt = rc ? " · between these parts: " + plural(rc.total, "edge") : "";
      return regTxt + (tq > 0 && estEdges > 0 ? " · about " + plural(estEdges, "edge") + " in this cell, " + lean : " · No edges in this cell") + rcTxt;
    };
    const hicCellAt = (ev) => {
      const [cx, cy] = atlasCanvasXY(hicCanvas, ev);
      const N = Number((hic.tile_128 || {}).size) || 128;
      const bx = Math.floor((cx - 26) / 4);
      const by = Math.floor((cy - 26) / 4);
      return (bx < 0 || bx >= N || by < 0 || by >= N) ? null : { bx, by, N };
    };
    hicCanvas.addEventListener("mousemove", (ev) => {
      if (hicSel) return; // the open tray owns the readout
      const cell = hicCellAt(ev);
      if (cell) hicReadout.textContent = hicCellText(cell.bx, cell.by, cell.N);
    });

    // Dot-plot hover readout
    const synBinMap = new Map();
    for (const pt of (syn.binned_points || [])) {
      synBinMap.set(pt[0] + ":" + pt[1], pt);
    }
    const synG = Number((syn.grid_meta && syn.grid_meta.grid_size) || 128);
    const synCellAt = (ev) => {
      const [cx, cy] = atlasCanvasXY(synCanvas, ev);
      const pb = Math.floor((cx - 32) / 4);
      const lb = synG - 1 - Math.floor((cy - 14) / 4);
      return (pb < 0 || pb >= synG || lb < 0 || lb >= synG) ? null : { pb, lb };
    };
    const synCellText = (pb, lb) => {
      const nLive = Number(syn.n_live_decls) || 1;
      const nL = Number(syn.n_library_decls) || 1;
      const reg = atlasRegionForDfs(hic.regions, Math.floor(((pb + 0.5) / synG) * nLive));
      const libIdx = Math.floor(((lb + 0.5) / synG) * nL);
      const st = (syn.library_strata || []).find((s) => libIdx >= s.lib_idx_start && libIdx < s.lib_idx_end);
      const pt = synBinMap.get(pb + ":" + lb);
      const b256 = pb * 2;
      const band = (ti.bands || []).find((b) => b256 >= b.bin256_start && b256 <= b.bin256_end);
      const streak = (syn.diagonal_streaks || []).find((ds) => {
        const pr = ds.proj_bin_range || [0, 0];
        const lr = ds.lib_bin_range || [0, 0];
        return pb >= Math.min(pr[0], pr[1]) - 1 && pb <= Math.max(pr[0], pr[1]) + 1 && lb >= Math.min(lr[0], lr[1]) - 1 && lb <= Math.max(lr[0], lr[1]) + 1;
      });
      const repos = (syn.grid_meta && syn.grid_meta.repos) || [];
      let msg = (reg ? reg.label : "Proof position " + pb) + " × library layer L" + (st ? st.stratum + " (" + (st.top_namespaces || []).join(", ") + ")" : lb);
      if (pt) msg += " · " + plural(pt[2], "match", "matches") + " (" + fmtInt(pt[3]) + " by name, mostly " + (repos[pt[4]] ? synRepoLabel(repos[pt[4]]) : "library") + ")";
      if (streak) msg += " · diagonal run in " + streak.library_domain + " (" + plural(streak.length_bins, "step") + ")";
      if (band) msg += " · no match by name across " + plural(band.decl_count, "declaration");
      return msg;
    };
    synCanvas.addEventListener("mousemove", (ev) => {
      if (synSel) return;
      const c = synCellAt(ev);
      if (c) synReadout.textContent = synCellText(c.pb, c.lb);
    });

    // Click a contact-map cell: declarations in its row/column and sample edges.
    // A second click on the same block closes the tray.
    const closeHic = () => {
      hicSel = null;
      hicReadout.classList.remove("locked");
      hicReadout.textContent = HIC_HINT;
    };
    hicCanvas.addEventListener("click", (ev) => {
      const cell = hicCellAt(ev);
      if (!cell) return;
      if (hicSel) {
        const p = atlasHicBlock(hic, hicSel), q = atlasHicBlock(hic, cell);
        if (p.r32 === q.r32 && p.c32 === q.c32) { hicTray.hidden = true; closeHic(); drawHic(); return; }
      }
      hicSel = cell;
      openHicTray(hicTray, hicCanvas, hic, cell, couplingMap, closeHic);
      hicReadout.textContent = "Selected: " + hicCellText(cell.bx, cell.by, cell.N) + ". Click the cell again or × to close.";
      hicReadout.classList.add("locked");
    });
    const closeSyn = () => {
      synSel = null;
      delete synCanvas.dataset.sel;
      synReadout.classList.remove("locked");
      synReadout.textContent = SYN_HINT;
      drawSyn();
    };
    synCanvas.addEventListener("click", (ev) => {
      const c = synCellAt(ev);
      if (!c) return;
      const snap = atlasSynSnap(syn, c.pb, c.lb);
      if (synSel && synSel.kb === snap.kb && synSel.kl === snap.kl) { synTray.hidden = true; closeSyn(); return; }
      synSel = { kb: snap.kb, kl: snap.kl };
      synCanvas.dataset.sel = snap.kb + "," + snap.kl;
      openSyntenyTray(synTray, syn, hic, c.pb, c.lb, closeSyn);
      drawSyn();
      synReadout.textContent = "Selected: " + synCellText(snap.kb, snap.kl) + ". Click the dot again or × to close.";
      synReadout.classList.add("locked");
    });

    // 2D map
    if (state.manifest.assets && state.manifest.assets.embedding_2d) {
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "2D map" })]));
      const mapHost = el("section", { className: "map2d-section", id: "map2dSection" });
      main.appendChild(mapHost);
      mountMap2d(mapHost);
    }

    renderProofSimilarity(main, aliens);
  }

  // Proof similarity index: scope-linked histogram, sampled pairs and a
  // toolbar that stays mounted, so typing and sorting never rebuild the page.
  function renderProofSimilarity(main, aliens) {
    const A = state.atlas;
    if (!TWIN_SCOPES.some((s) => s[0] === A.twinScope)) A.twinScope = "all";
    if (!TWIN_SORTS.some((s) => s[0] === A.twinSort)) A.twinSort = "jaccard";
    if (A.twinDir !== "asc" && A.twinDir !== "desc") A.twinDir = (TWIN_SORTS.find((s) => s[0] === A.twinSort) || [])[2] || "asc";
    if (!TWIN_BANDS.some((b) => b[0] === A.twinBand)) A.twinBand = "all";
    if (typeof A.twinQ !== "string") A.twinQ = "";
    if (!Number.isInteger(A.twinBin)) A.twinBin = -1;
    if (A.histScale !== "log") A.histScale = "linear";

    const pool = atlasTwinPool(aliens);
    const sec = el("section", { className: "psi-section", id: "proofSimilarity" });
    main.appendChild(sec);
    sec.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "Proof similarity index" })]));
    sec.appendChild(el("p", { className: "section-lede", textContent: "Theorem pairs whose statements share a normalized signature, compared by the constants their proof terms refer to. Proof-only overlap J is the share of those proof references the two have in common: 0 means none, 1 means the same set. Cross-refs compare also reports an all-references J that counts statement constants too." }));

    const histHost = el("div", { className: "hist-wrap psi-hist", id: "psiHist" });
    sec.appendChild(histHost);

    const chipGroup = (id, label, items, key, onPick) => el("div", { className: "psi-chips", id, role: "group", "aria-label": label }, items.map(([k, lbl]) => el("button", {
      type: "button", className: "psi-chip", "data-k": k, textContent: lbl,
      onclick: () => onPick(k)
    })));
    const scopeChips = chipGroup("psiScope", "Scope", TWIN_SCOPES, "twinScope", (k) => { A.twinScope = k; refresh(); });
    const bandChips = chipGroup("psiBand", "Overlap band", TWIN_BANDS, "twinBand", (k) => { A.twinBand = k; A.twinBin = -1; refresh(); });
    const input = el("input", { type: "search", className: "input psi-filter", id: "psiFilter", placeholder: "Filter pairs by name, module, or library…", "aria-label": "Filter pairs by name, module, or library", value: A.twinQ });
    input.addEventListener("input", () => { A.twinQ = input.value; renderList(); syncControls(); });
    const sortSel = el("select", { className: "select", id: "psiSort", "aria-label": "Sort pairs by" },
      TWIN_SORTS.map(([k, lbl]) => el("option", { value: k, selected: A.twinSort === k, textContent: lbl })));
    sortSel.addEventListener("change", () => {
      A.twinSort = sortSel.value;
      A.twinDir = (TWIN_SORTS.find((s) => s[0] === A.twinSort) || [])[2] || "asc";
      renderList(); syncControls();
    });
    const dirBtn = el("button", { type: "button", className: "btn sm psi-dir", id: "psiDir", title: "Flip sort direction" });
    dirBtn.addEventListener("click", () => { A.twinDir = A.twinDir === "asc" ? "desc" : "asc"; renderList(); syncControls(); });
    const clearBtn = el("button", { type: "button", className: "btn sm", id: "psiClear", textContent: "Clear", title: "Reset filters and sort" });
    clearBtn.addEventListener("click", () => {
      Object.assign(A, { twinQ: "", twinScope: "all", twinBand: "all", twinBin: -1, twinSort: "jaccard", twinDir: "asc" });
      input.value = "";
      sortSel.value = "jaccard";
      refresh();
    });
    const countEl = el("p", { className: "psi-count", id: "psiCount" });
    sec.appendChild(el("div", { className: "psi-toolbar" }, [
      el("div", { className: "psi-row" }, [input, el("label", { className: "psi-sort" }, ["Sort ", sortSel]), dirBtn, clearBtn]),
      el("div", { className: "psi-row" }, [
        el("span", { className: "psi-group" }, [el("span", { className: "psi-lbl" }, "Scope"), scopeChips]),
        el("span", { className: "psi-group" }, [el("span", { className: "psi-lbl" }, "Overlap"), bandChips])
      ])
    ]));
    const scopeNote = psiScopeNoteText(aliens);
    if (scopeNote) sec.appendChild(el("p", { className: "quiet-note psi-scope-note", id: "psiScopeNote", textContent: scopeNote }));
    sec.appendChild(countEl);
    const evaluated = Number(((aliens && aliens.counts) || {}).sampled_pairs_evaluated) || 0;
    const sampleNote = el("p", { className: "quiet-note psi-sample-note", id: "psiSampleNote" });
    sec.appendChild(sampleNote);
    const listHost = el("div", { className: "twins-grid", id: "twinsGridHost" });
    sec.appendChild(listHost);

    const scopeDef = () => TWIN_SCOPES.find((s) => s[0] === A.twinScope) || TWIN_SCOPES[0];
    const isDefault = () => !A.twinQ && A.twinScope === "all" && A.twinBand === "all" && A.twinBin < 0 && A.twinSort === "jaccard" && A.twinDir === "asc";

    // ---- histogram (rebuilt only when scope or scale changes) ----
    let histKey = "";
    let histData = null;
    const renderHist = () => {
      const sd = scopeDef();
      const key = sd[0] + "|" + A.histScale;
      if (key === histKey) return;
      const hadFocus = histHost.contains(document.activeElement) ? document.activeElement : null;
      const focusSel = hadFocus ? (hadFocus.closest("#psiScale") ? "#psiScale button[data-k='" + A.histScale + "']" : (hadFocus.dataset.bin ? ".hist-bar-col[data-bin='" + hadFocus.dataset.bin + "']" : null)) : null;
      histKey = key;
      clearEl(histHost);
      histData = atlasScopeHist(aliens, sd[2]);
      if (!histData) { histHost.hidden = true; return; }
      histHost.hidden = false;
      const log = A.histScale === "log";
      const val = (n) => (log ? Math.log10(1 + n) : n);
      const vMax = Math.max(1e-9, ...histData.bins.map(val));
      const scaleSeg = el("div", { className: "seg psi-scale", id: "psiScale", role: "group", "aria-label": "Histogram scale" }, [["linear", "Linear"], ["log", "Log"]].map(([k, lbl]) => el("button", {
        type: "button", className: A.histScale === k ? "active" : "", "data-k": k, "aria-pressed": A.histScale === k ? "true" : "false", textContent: lbl,
        onclick: () => { if (A.histScale !== k) { A.histScale = k; renderHist(); syncHist(); } }
      })));
      const c = histData.counts || {};
      const poolLabel = histData.exact ? sd[3] + " (" + fmtInt(histData.total) + ")" : "All pairs (" + fmtInt(histData.total) + "); no separate breakdown for this scope";
      histHost.appendChild(el("div", { className: "psi-hist-hd" }, [
        el("div", { className: "psi-hist-titles" }, [
          el("h3", { className: "hist-title", textContent: "Proof-only overlap J (Jaccard) distribution" }),
          el("span", { className: "psi-pool", textContent: poolLabel })
        ]),
        scaleSeg
      ]));
      if (c.alien != null) {
        histHost.appendChild(el("div", { className: "atlas-legend psi-legend" }, [
          el("span", null, [el("i", { className: "atlas-swatch", style: { background: "var(--crimson)" } }), "Low (<0.20): " + fmtInt(c.alien)]),
          el("span", null, [el("i", { className: "atlas-swatch", style: { background: "var(--amber)" } }), "Partial (0.20–0.70): " + fmtInt(c.variant || 0)]),
          el("span", null, [el("i", { className: "atlas-swatch", style: { background: "var(--emerald)" } }), "High (≥0.70): " + fmtInt(c.clone || 0)])
        ]));
      }
      histHost.appendChild(el("div", { className: "hist-bars" }, histData.bins.map((cnt, idx) => {
        const lo = (idx * 0.05).toFixed(2), hi = ((idx + 1) * 0.05).toFixed(2);
        const pctH = cnt > 0 ? Math.max(3, Math.round((val(cnt) / vMax) * 100)) : 0;
        const label = "Overlap " + lo + "–" + hi + ": " + plural(cnt, "pair");
        return el("button", {
          type: "button", className: "hist-bar-col", "data-bin": String(idx), title: label, "aria-label": label + ". Show sampled pairs in this range.",
          onclick: () => {
            if (A.twinBin === idx) A.twinBin = -1;
            else { A.twinBin = idx; A.twinBand = atlasBinBand(idx); }
            syncHist(); syncControls(); renderList();
          }
        }, [el("div", { className: "hist-bar " + atlasBinBand(idx), style: { height: pctH + "%" } })]);
      })));
      histHost.appendChild(el("div", { className: "hist-axis" }, [
        el("span", { textContent: "0 · no shared lemmas" }),
        el("span", { textContent: "0.20" }),
        el("span", { textContent: "0.50" }),
        el("span", { textContent: "0.70" }),
        el("span", { textContent: "1 · same lemmas" })
      ]));
      if (focusSel) { const n = histHost.querySelector(focusSel); if (n) n.focus({ preventScroll: true }); }
    };
    const syncHist = () => {
      $$(".hist-bar-col", histHost).forEach((b) => {
        const idx = Number(b.dataset.bin);
        const sel = A.twinBin === idx;
        const dim = A.twinBin >= 0 ? !sel : (A.twinBand !== "all" && atlasBinBand(idx) !== A.twinBand);
        b.classList.toggle("sel", sel);
        b.classList.toggle("dim", dim);
        b.setAttribute("aria-pressed", sel ? "true" : "false");
      });
    };

    const syncControls = () => {
      const pressChips = (group, cur) => $$("button", group).forEach((b) => { const on = b.dataset.k === cur; b.classList.toggle("active", on); b.setAttribute("aria-pressed", on ? "true" : "false"); });
      pressChips(scopeChips, A.twinScope);
      pressChips(bandChips, A.twinBand);
      const desc = A.twinDir === "desc";
      dirBtn.textContent = desc ? "↓ Desc" : "↑ Asc";
      dirBtn.setAttribute("aria-pressed", desc ? "true" : "false");
      dirBtn.setAttribute("aria-label", "Sort direction: " + (desc ? "descending" : "ascending") + ". Flip sort direction");
      if (sortSel.value !== A.twinSort) sortSel.value = A.twinSort;
      clearBtn.disabled = isDefault();
    };

    // ---- pair list ----
    const sortVal = {
      jaccard: (x) => x.j,
      ratio: (x) => atlasTwinRatio(x.p),
      type_nodes: (x) => Number(x.p.type_nodes || 0),
      shared: (x) => Number(x.p.shared_ev_count || 0),
      proof_a: (x) => Number(x.p.thm_a.value_nodes || 0),
      proof_b: (x) => Number(x.p.thm_b.value_nodes || 0)
    };
    const renderList = () => {
      const q = A.twinQ.trim().toLowerCase();
      const terms = q ? q.split(/\s+/) : [];
      const inScope = pool.filter((x) => A.twinScope === "all" || (A.twinScope === "cross") === x.cross);
      const shown = inScope.filter((x) =>
        (A.twinBin >= 0 ? x.bin === A.twinBin : (A.twinBand === "all" || x.band === A.twinBand)) &&
        terms.every((t) => x.hay.includes(t)));
      const dir = A.twinDir === "desc" ? -1 : 1;
      const nameOf = (x) => String(x.p.thm_a.name || "");
      shown.sort((a, b) => {
        let d = 0;
        if (A.twinSort === "name") d = nameOf(a).localeCompare(nameOf(b));
        else d = (sortVal[A.twinSort] || sortVal.jaccard)(a) - (sortVal[A.twinSort] || sortVal.jaccard)(b);
        return (d * dir) || (a.j - b.j) || nameOf(a).localeCompare(nameOf(b));
      });
      const scopeTotal = histData && histData.exact ? histData.total : null;
      countEl.textContent = "Showing " + fmtInt(shown.length) + " of " + fmtInt(inScope.length) + " sampled representative pairs" + (scopeTotal ? " (from " + fmtInt(scopeTotal) + " total pairs in this scope)" : "") + ".";
      sampleNote.textContent = "Sampling rule: the lowest-overlap, partial and highest-overlap exemplars, drawn from " + fmtInt(evaluated || scopeTotal || inScope.length) + " same-statement pairs; histogram bars count every pair, the list shows only the sample.";
      clearEl(listHost);
      if (!shown.length) {
        listHost.appendChild(el("div", { className: "empty-card psi-empty" }, [
          el("p", { textContent: inScope.length ? "No sampled pairs match these filters." : "No sampled pairs were recorded for this scope." }),
          isDefault() ? null : el("button", { type: "button", className: "btn sm", textContent: "Clear filters", onclick: () => clearBtn.click() })
        ]));
        return;
      }
      const frag = document.createDocumentFragment();
      for (const x of shown) frag.appendChild(renderTwinCard(x));
      listHost.appendChild(frag);
    };

    const refresh = () => { renderHist(); syncHist(); syncControls(); renderList(); };
    refresh();
  }

  // Pairs counted under All but in neither scope chip: both theorems come from
  // external libraries. Returns "" when the scopes add up.
  function psiScopeNoteText(aliens) {
    const hs = (aliens && aliens.histograms_by_scope) || {};
    const tot = (k) => Number(((hs[k] || {}).counts || {}).total);
    const all = tot("all"), intra = tot("intra"), cross = tot("cross_repo");
    if (![all, intra, cross].every(Number.isFinite) || all <= intra + cross) return "";
    const rest = all - intra - cross;
    return "Of the " + plural(all, "pair") + ", " + fmtInt(intra) + " are within the project and " + fmtInt(cross) + " pair the project with an external library. The other " + plural(rest, "pair") + " have both theorems in external libraries (such as Lean 4 and Mathlib), so they appear only under All.";
  }

  const PSI_J_TIP = "Jaccard overlap of the proof-term dependencies (E_V): constants both proof terms refer to, divided by those either refers to. Statement-only constants are left out. Cross-refs compare shows both this proof-only J and an all-references J.";

  function psiShortHash(h) {
    const s = String(h || "").replace(/^k1[an]:/, "");
    return s ? (s.length > 10 ? s.slice(0, 10) + "…" : s) : "—";
  }

  function renderTwinSide(thm, label, spec) {
    if (!thm) return el("div", { className: "twin-side" });
    const cir = findAnyCircuitForSymbol(thm.name);
    const isProject = thm.origin === "project";
    const ghHref = spec && spec.url ? safeHref(spec.url) : null;
    const docHref = spec && !ghHref && spec.fallbackUrl ? safeHref(spec.fallbackUrl) : null;
    const wrapTag = thm.wrapper_tag ? (WRAPPER_TAGS[thm.wrapper_tag] || String(thm.wrapper_tag).replace(/_/g, " ")) : "";
    return el("div", { className: "twin-side" }, [
      el("div", { className: "twin-side-top" }, [
        el("span", { className: "twin-side-tag", textContent: label + " · " + (isProject ? "this project" : (thm.origin || "library")) }),
        el("span", { className: "twin-side-meta", title: "Size of the proof term, and the number of constants it refers to (lemmas, definitions and binder types such as Nat or OfNat.ofNat)", textContent: "proof: " + plural(thm.value_nodes, "AST node") + " · " + plural(thm.ev_size, "reference") })
      ]),
      el("div", { className: "psi-name-row" }, [
        el("div", { className: "twin-side-name", title: thm.name }, [identWbr(thm.name)]),
        wrapTag ? el("span", { className: "psi-wrap-pill", title: "This proof mostly hands off to another declaration, so a low overlap may only reflect the wrapper", textContent: wrapTag }) : null
      ]),
      thm.module ? el("div", { className: "twin-side-meta", textContent: thm.module + (thm.line_no ? ":" + thm.line_no : "") }) : null,
      el("div", { className: "cir-ins-acts", style: { marginTop: "3px" } }, [
        isProject ? el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(thm.name), textContent: "Inspect ›" }) : null,
        ghHref ? el("a", { className: "btn sm", href: ghHref, target: "_blank", rel: "noopener noreferrer", textContent: "Proof file ↗" }) : null,
        docHref ? el("a", { className: "btn sm", href: docHref, target: "_blank", rel: "noopener noreferrer", textContent: "Mathlib docs ↗" }) : null,
        cir ? el("a", { className: "btn sm", href: "#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name), textContent: "Diagram ›" }) : null
      ])
    ]);
  }

  function renderTwinCard(x) {
    const p = x.p;
    const ratio = atlasTwinRatio(p);
    const vnA = Number((p.thm_a && p.thm_a.value_nodes) || 0);
    const vnB = Number((p.thm_b && p.thm_b.value_nodes) || 0);
    const ratioNote = ratio >= 2
      ? (x.cross && vnA < vnB ? ratio.toFixed(1) + "× shorter than the library proof" : ratio.toFixed(1) + "× difference in proof size")
      : "";
    const specA = atlasTwinSourceSpec(p.thm_a, "A");
    const specB = atlasTwinSourceSpec(p.thm_b, "B");
    const peekBtn = (spec, txt) => (spec && spec.peekable)
      ? el("button", { type: "button", className: "btn sm", textContent: txt, title: "Preview Lean source inline", onclick: () => openSourcePeek(spec) })
      : null;
    const canCompare = (specA && specA.peekable) || (specB && specB.peekable);
    const pd = p.proof_diff;
    return el("article", { className: "twin-card", "data-j": String(x.j), "data-band": x.band }, [
      el("div", { className: "twin-card-hd" }, [
        el("div", { className: "twin-card-facts" }, [
          el("span", { className: "psi-band " + x.band, textContent: TWIN_BAND_SHORT[x.band] }),
          el("span", { className: "twin-j", title: PSI_J_TIP, textContent: "proof-only overlap J = " + x.j.toFixed(3) }),
          el("span", { title: PSI_J_TIP, textContent: fmtInt(p.shared_ev_count) + " of " + fmtInt(p.union_ev_count) + " proof references shared" }),
          el("span", { textContent: x.cross ? "against an external library" : "within this project" }),
          ratioNote ? el("span", { textContent: ratioNote }) : null
        ])
      ]),
      el("div", { className: "twin-sides" }, [
        renderTwinSide(p.thm_a, "A", specA),
        renderTwinSide(p.thm_b, "B", specB)
      ]),
      pd ? el("div", { className: "twin-card-diff" }, [buildProofDiffBar(pd, false, { onPick: (k) => openProofDiff(p, { filter: k }) })]) : null,
      el("div", { className: "twin-card-ft" }, [
        el("span", { className: "twin-side-meta psi-hash", title: p.sighash ? "Normalized statement hash shared by both statements: " + String(p.sighash).replace(/^k1[an]:/, "") : "Normalized statement hash", textContent: "Statement hash " + psiShortHash(p.sighash) + (p.bucket_size ? " · shared by " + plural(p.bucket_size, "theorem") : "") + (p.type_nodes ? " · statement: " + plural(p.type_nodes, "AST node") : "") }),
        el("div", { className: "cir-ins-acts" }, [
          peekBtn(specA, "Peek A"),
          peekBtn(specB, "Peek B"),
          pd ? el("button", { type: "button", className: "btn sm pdiff-open", textContent: "View diff", title: "Lemma-by-lemma diff of the two proofs (no download needed)", onclick: () => openProofDiff(p) }) : null,
          canCompare ? el("button", { type: "button", className: "btn sm primary", textContent: "Compare side-by-side", onclick: () => openSourceCompare(specA, specB, { pair: p }) }) : null
        ])
      ])
    ]);
  }

  // ==========================================================================
  // === PROOF DIFF VIEW (v2.5) ===
  // Two layers for a pair of proofs of the same statement:
  //   1. Lemma diff: offline, read from `proof_diff` in atlas_summary.json.
  //   2. Line diff: the two Lean files, fetched only on request, compared with
  //      a Myers diff (patience fallback for large windows), moved-block
  //      detection and word-level highlights on modified lines.
  // Both live inside the source drawer, so Esc, focus trapping and full-screen
  // placement are shared with the existing viewer.
  // ==========================================================================
  const PDIFF_ROLE = { value: "proof", type: "statement", both: "both" };
  const PDIFF_ROLE_TIP = { value: "Used in the proof only", type: "Used in the statement only", both: "Used in the statement and the proof" };
  const PDIFF_ORIGIN = { project: "this project", mathlib4: "Mathlib", lean4: "Lean core" };
  // The corpus match tags every non-project constant "mathlib4", including
  // constants that live in Lean core (Init). These are relabeled "Lean core".
  const LEAN_CORE_ROOTS = new Set(("Eq HEq And Or Not True False Exists Iff Ne Xor Nat Int Fin List Array Option Subtype Prod PProd MProd Sum PSum Sigma PSigma " +
    "Bool Char String Quot Quotient Setoid Classical Decidable DecidableEq DecidablePred DecidableRel Inhabited Nonempty Unit PUnit Empty PEmpty " +
    "OfNat HAdd HMul HSub HDiv HPow HMod HAppend HSMul HAnd HOr HXor Add Mul Sub Div Neg Pow Mod LE LT Max Min BEq Hashable NatCast IntCast " +
    "Function.comp Function.const propext funext id cast congrArg congrFun congr absurd rfl trivial ite dite of_eq_true of_eq_false eq_self eq_true eq_false " +
    "eq_self_iff_true iff_self and_self or_self not_false_eq_true implies_true forall_const ne_eq if_pos if_neg dif_pos dif_neg Eq.mpr Eq.mp UInt8 UInt16 UInt32 UInt64 USize Float Thunk Task IO").split(/\s+/));
  // Namespaces where Mathlib also adds lemmas: only these members count as core.
  const LEAN_CORE_MIXED = new Set(["Nat", "Int", "Fin", "List", "Array", "Option", "Subtype", "Prod", "Sum", "Sigma", "Bool", "Char", "String", "Quotient", "Function", "Classical", "Decidable"]);
  const LEAN_CORE_MEMBERS = new Set("succ zero add mul sub div mod pow le lt ble beq pred rec recOn casesOn cast ofNat negSucc neg natAbs toNat cons nil map length get some none mk val isLt property fst snd inl inr true false intro elim choose choose_spec em byContradiction byCases decide mk' lift ind sound rfl".split(" "));
  function pdiffIsLeanCore(name) {
    const n = String(name || "").replace(/^_root_\./, "");
    if (!n) return false;
    if (LEAN_CORE_ROOTS.has(n)) return true;
    if (/^inst(H(Add|Mul|Sub|Div|Pow|Mod|Append|SMul|And|Or|Xor)|OfNat(Nat)?|NatCast(Int)?|IntCast(Int)?|(Add|Mul|Sub|Div|Neg|Mod|Pow|LT|LE|Max|Min|BEq|DecidableEq|Inhabited|Nonempty|Hashable|Repr|ToString)(Nat|Int|Bool|Fin|Char|String|Prop|Float|UInt(8|16|32|64)|USize)?|Decidable(And|Or|Not|Iff|True|False|EqNat|EqInt|EqBool|EqFin|LtNat|LeNat|Eq))$/.test(n)) return true;
    const dot = n.indexOf(".");
    if (dot < 0) return false;
    const root = n.slice(0, dot);
    if (!LEAN_CORE_ROOTS.has(root)) return false;
    if (!LEAN_CORE_MIXED.has(root)) return true;
    const rest = n.slice(dot + 1);
    return rest.indexOf(".") < 0 && LEAN_CORE_MEMBERS.has(rest);
  }
  function pdiffOriginLabel(it) {
    const o = it && it.origin;
    if (o === "mathlib4" && pdiffIsLeanCore(it.name)) return "Lean core";
    return PDIFF_ORIGIN[o] || String(o || "library");
  }
  // Disjoint lemma buckets for one orientation. A role shift is counted only
  // under "Role differs", even when the lemma also sits in one proof's
  // removed or added list, so Only A + Only B + Role differs + Shared lists
  // every proof reference exactly once (a renamed helper pair is one row).
  function pdiffBuckets(D) {
    const roleIds = new Set(D.role.map((r) => r.decl_id));
    const inList = (list) => list.filter((x) => roleIds.has(x.decl_id)).length;
    const ovA = D.tr.removed || D.tr.role ? D.role.filter((r) => r.role_b === "type" && r.role_a !== "type").length : inList(D.removed);
    const ovB = D.tr.added || D.tr.role ? D.role.filter((r) => r.role_a === "type" && r.role_b !== "type").length : inList(D.added);
    const total = { removed: Math.max(0, D.c.removed - ovA), added: Math.max(0, D.c.added - ovB), moved: D.c.role + D.c.helper, shared: D.c.shared };
    total.all = total.removed + total.added + total.moved + total.shared;
    return { roleIds, total };
  }
  const PDIFF_REASON = { same_sig: "same signature", same_sig_anon: "same shape", same_short_name: "same short name" };
  const PDIFF_REASON_TIP = {
    same_sig: "Different names, identical statement",
    same_sig_anon: "Different names, identical statement up to bound-variable names",
    same_short_name: "Same last name component in a different namespace"
  };
  // [filter key, label, glyph, row kind]
  const PDIFF_KINDS = [["all", "All", "", ""], ["removed", "Only in A", "−", "del"], ["added", "Only in B", "+", "add"], ["moved", "Role differs", "⇄", "mv"], ["shared", "Shared", "=", "eq"]];
  const PDIFF_SRC_VIEWS = [["side", "Side-by-side"], ["unified", "Unified diff"], ["split", "Split diff"]];
  const PDIFF_GLYPH = { del: "−", add: "+", mv: "⇄", eq: "=" };
  const PDIFF_KIND_WORD = { del: "only in A", add: "only in B", mv: "role differs", eq: "shared" };
  const LD_MAX_LINES = 2500;
  const LD_FOLD_CTX = 3;
  const pdiffState = { view: "unified", filter: "all", projectOnly: false, q: "", sharedOpen: false, ignoreWs: false, hideSame: true, expanded: new Set(), hunk: -1 };

  function appendNode(parent, node) {
    if (node) parent.appendChild(node);
  }

  function pdiffDocsUrl(name) {
    return "https://leanprover-community.github.io/mathlib4_docs/find/?pattern=" + encodeURIComponent(String(name || "").replace(/^_root_\./, "")) + "#doc";
  }

  // proof_diff seen from the reader's orientation: with `swapped`, proof B
  // becomes A, so removed and added trade places and role shifts reverse.
  function pdiffOrient(pd, swapped) {
    const L = (x) => (Array.isArray(x) ? x : []);
    const c = pd.counts || {};
    const tr = pd.truncated || {};
    const to = pd.type_only || {};
    const n = (v) => Math.max(0, Number(v) || 0);
    const D = {
      removed: L(pd.removed), added: L(pd.added), shared: L(pd.shared), role: L(pd.moved_role), helper: L(pd.moved_helper),
      tr: { removed: n(tr.removed), added: n(tr.added), shared: n(tr.shared), role: n(tr.moved_role), helper: n(tr.moved_helper) },
      c: { removed: n(c.removed), added: n(c.added), shared: n(c.shared), role: n(c.moved_role), helper: n(c.moved_helper), aEv: n(c.a_ev), bEv: n(c.b_ev) },
      typeOnly: { shared: n(to.n_type_shared), aOnly: n(to.n_type_a_only), bOnly: n(to.n_type_b_only) }
    };
    if (!swapped) return D;
    return {
      removed: D.added, added: D.removed, shared: D.shared,
      role: D.role.map((r) => Object.assign({}, r, { role_a: r.role_b, role_b: r.role_a })),
      helper: D.helper.map((h) => ({ a: h.b, b: h.a, reason: h.reason })),
      tr: { removed: D.tr.added, added: D.tr.removed, shared: D.tr.shared, role: D.tr.role, helper: D.tr.helper },
      c: { removed: D.c.added, added: D.c.removed, shared: D.c.shared, role: D.c.role, helper: D.c.helper, aEv: D.c.bEv, bEv: D.c.aEv },
      typeOnly: { shared: D.typeOnly.shared, aOnly: D.typeOnly.bOnly, bOnly: D.typeOnly.aOnly }
    };
  }

  // Slim proportional bar plus four counts. With opts.onPick the counts are
  // buttons that open the diff filtered to that kind.
  function buildProofDiffBar(pd, swapped, opts) {
    const o = opts || {};
    const D = pdiffOrient(pd, swapped);
    const c = D.c;
    const b = pdiffBuckets(D).total;
    const parts = [
      ["removed", "del", b.removed, "only in A", plural(b.removed, "lemma") + " used by proof A and by neither part of B"],
      ["added", "add", b.added, "only in B", plural(b.added, "lemma") + " used by proof B and by neither part of A"],
      ["moved", "mv", b.moved, "role differs", plural(c.role, "lemma") + " used in the statement by one theorem and in the proof by the other (role in A → role in B)" + (c.helper ? ", and " + plural(c.helper, "helper") + " renamed between the two" : "")],
      ["shared", "eq", b.shared, "shared", plural(b.shared, "lemma") + " used the same way by both proofs"]
    ];
    const total = parts.reduce((s, p) => s + p[2], 0);
    const track = el("div", { className: "pdb-track", "aria-hidden": "true" }, total
      ? parts.filter((p) => p[2] > 0).map((p) => el("span", { className: "pdb-seg " + p[1], style: { flexGrow: String(p[2]) } }))
      : [el("span", { className: "pdb-seg none" })]);
    const chips = parts.map(([k, cls, num, word, tip]) => {
      const attrs = { className: "pdb-chip " + cls + (num ? "" : " zero"), title: tip, "data-k": k };
      const kids = [el("span", { className: "pdb-g", "aria-hidden": "true", textContent: PDIFF_GLYPH[cls] }), fmtInt(num) + " " + word];
      if (!o.onPick) return el("span", attrs, kids);
      return el("button", Object.assign({ type: "button", "aria-label": fmtInt(num) + " " + word + ": show in the lemma diff", onclick: (ev) => { ev.stopPropagation(); o.onPick(k); } }, attrs), kids);
    });
    return el("div", { className: "pdiff-bar" + (o.compact ? " compact" : ""), role: "group", "aria-label": "Lemma diff summary" }, [track, el("div", { className: "pdb-chips" }, chips)]);
  }

  // Open the drawer on a pair. opts: { swap, filter, tab, view, specs }.
  function openProofDiff(pair, opts) {
    const o = opts || {};
    if (!pair || !pair.thm_a || !pair.thm_b) return Promise.resolve(false);
    let specs = Array.isArray(o.specs) && o.specs.length === 2 ? o.specs.slice() : null;
    if (!specs) {
      specs = [atlasTwinSourceSpec(pair.thm_a, "A"), atlasTwinSourceSpec(pair.thm_b, "B")];
      if (o.swap) specs.reverse();
    }
    specs = specs.map((s, i) => Object.assign({}, s, { label: i ? "B" : "A" }));
    return openSourceCompare(specs[0], specs[1], {
      pair, swap: Boolean(o.swap), filter: o.filter, view: o.view,
      tab: pair.proof_diff ? (o.tab || "lemmas") : "source"
    });
  }

  function pdiffPrepare(mode, o) {
    srcView.back = null;
    srcView.pair = mode === "compare" && o.pair && o.pair.proof_diff ? o.pair : null;
    srcView.swapped = Boolean(srcView.pair && o.swap);
    srcView.tab = srcView.pair && o.tab === "lemmas" ? "lemmas" : "source";
    srcView.view = mode === "compare" && PDIFF_SRC_VIEWS.some(([k]) => k === o.view) ? o.view : "side";
    if (!o.keepFilters) {
      pdiffState.filter = PDIFF_KINDS.some(([k]) => k === o.filter) ? o.filter : "all";
      pdiffState.q = "";
      pdiffState.sharedOpen = pdiffState.filter === "shared";
    }
    pdiffState.expanded = new Set();
    pdiffState.hunk = -1;
    srcView.ldHunks = [];
  }

  function pdiffOwnsBody() {
    return srcView.mode === "compare" && (srcView.tab === "lemmas" || srcView.view !== "side");
  }

  function pdiffRenderBody() {
    if (srcView.tab === "lemmas" && srcView.pair) pdiffRenderLemmaBody();
    else pdiffRenderSourceDiff();
  }

  // Tabs (Lemma diff | Lean source), the source layout switch and the line
  // diff options are added to the drawer once, then shown or hidden per mode.
  function pdiffEnsureChrome() {
    const root = srcView.root;
    if (!root || root.querySelector("#srcTabs")) return;
    const tabs = el("div", { className: "pdiff-tabs hidden", id: "srcTabs" }, [
      el("div", { className: "seg", role: "tablist", "aria-label": "Compare by" }, [["lemmas", "Lemma diff"], ["source", "Lean source"]].map(([k, lbl]) =>
        el("button", { type: "button", role: "tab", "data-tab": k, textContent: lbl, onclick: () => pdiffSetTab(k) }))),
      el("div", { className: "spacer" }),
      el("button", { type: "button", className: "btn sm", id: "srcSwapBtn", title: "Swap which proof is A and which is B", textContent: "Swap A ↔ B", onclick: pdiffSwap })
    ]);
    root.querySelector(".src-hd").insertAdjacentElement("afterend", tabs);
    const ctxSeg = root.querySelector("#srcCtxSeg");
    const viewSeg = el("div", { className: "seg hidden", id: "srcViewSeg", role: "group", "aria-label": "Source layout" }, PDIFF_SRC_VIEWS.map(([k, lbl]) =>
      el("button", { type: "button", "data-view": k, textContent: lbl, onclick: () => pdiffSetView(k) })));
    const ws = el("input", { type: "checkbox", id: "srcIgnoreWs", onchange: (ev) => { pdiffState.ignoreWs = ev.currentTarget.checked; pdiffState.expanded = new Set(); pdiffState.hunk = -1; pdiffRenderSourceDiff(); } });
    const same = el("input", { type: "checkbox", id: "srcHideSame", onchange: (ev) => { pdiffState.hideSame = ev.currentTarget.checked; pdiffRenderSourceDiff(); } });
    const opts = el("div", { className: "ld-opts hidden", id: "srcDiffOpts" }, [
      el("label", { className: "ld-check" }, [ws, "Ignore whitespace"]),
      el("label", { className: "ld-check" }, [same, "Hide unchanged"]),
      el("button", { type: "button", className: "btn sm", id: "srcPrevHunk", title: "Previous change (p)", textContent: "↑ Prev", onclick: () => pdiffJumpHunk(-1) }),
      el("button", { type: "button", className: "btn sm", id: "srcNextHunk", title: "Next change (n)", textContent: "↓ Next", onclick: () => pdiffJumpHunk(1) })
    ]);
    ctxSeg.insertAdjacentElement("beforebegin", viewSeg);
    ctxSeg.insertAdjacentElement("afterend", opts);
    const toolbar = root.querySelector(".src-toolbar");
    toolbar.insertBefore(el("button", { type: "button", className: "btn sm hidden", id: "srcBackBtn", textContent: "‹ Back to comparison", onclick: pdiffBack }), toolbar.firstChild);
    root.addEventListener("keydown", pdiffKeys);
  }

  function pdiffSyncChrome() {
    if (!srcView.root) return;
    pdiffEnsureChrome();
    const cmp = srcView.mode === "compare";
    const onSource = cmp && srcView.tab === "source";
    const tabs = $("#srcTabs");
    tabs.classList.toggle("hidden", !cmp);
    $$("button[data-tab]", tabs).forEach((b) => {
      const on = b.dataset.tab === srcView.tab;
      b.classList.toggle("active", on);
      b.setAttribute("aria-selected", on ? "true" : "false");
      if (b.dataset.tab === "lemmas") b.classList.toggle("hidden", !srcView.pair);
    });
    const viewSeg = $("#srcViewSeg");
    viewSeg.classList.toggle("hidden", !onSource);
    $$("button", viewSeg).forEach((b) => { const on = b.dataset.view === srcView.view; b.classList.toggle("active", on); b.setAttribute("aria-pressed", on ? "true" : "false"); });
    $("#srcDiffOpts").classList.toggle("hidden", !(onSource && srcView.view !== "side"));
    $("#srcIgnoreWs").checked = pdiffState.ignoreWs;
    $("#srcHideSame").checked = pdiffState.hideSame;
    $("#srcCtxSeg").classList.toggle("hidden", cmp && srcView.tab === "lemmas");
    // Nothing is fetched for the offline lemma diff, so the live-fetch note is hidden there.
    const foot = srcView.root.querySelector(".src-foot");
    if (foot) foot.classList.toggle("hidden", cmp && srcView.tab === "lemmas");
    srcView.root.querySelector(".src-toolbar").classList.toggle("hidden", cmp && srcView.tab === "lemmas");
    $("#srcBackBtn").classList.toggle("hidden", !(srcView.mode === "single" && srcView.back));
    if (cmp) $("#srcDrawerPath").textContent = srcView.specs.map((s) => (s.label ? s.label + ": " : "") + s.title).join("  ·  ");
  }

  function pdiffSetTab(tab) {
    if (tab === "lemmas" && !srcView.pair) return;
    srcView.tab = tab;
    pdiffSyncChrome();
    if (tab === "lemmas") { pdiffRenderLemmaBody(); return; }
    if (srcView.view === "side") { buildSourcePanesShell(); rerenderSourcePanes(); }
    else pdiffRenderSourceDiff();
    loadSourceTexts(srcView.seq);
  }

  function pdiffSetView(view) {
    srcView.view = view;
    pdiffState.hunk = -1;
    pdiffSyncChrome();
    if (view === "side") { buildSourcePanesShell(); rerenderSourcePanes(); }
    else pdiffRenderSourceDiff();
  }

  // Flip which proof is A: panes, texts, labels and the lemma orientation.
  function pdiffSwap() {
    if (srcView.mode !== "compare") return;
    srcView.specs.reverse();
    srcView.texts.reverse();
    srcView.errors.reverse();
    srcView.specs.forEach((s, i) => { s.label = i ? "B" : "A"; });
    srcView.swapped = !srcView.swapped;
    pdiffState.expanded = new Set();
    pdiffState.hunk = -1;
    pdiffSyncChrome();
    if (pdiffOwnsBody()) pdiffRenderBody();
    else { buildSourcePanesShell(); rerenderSourcePanes(); }
  }

  // Peek at one lemma from inside the comparison, with a way back.
  function pdiffPeek(spec) {
    const back = srcView.mode === "compare" ? {
      specs: srcView.specs.slice(), texts: srcView.texts.slice(), errors: srcView.errors.slice(),
      pair: srcView.pair, swapped: srcView.swapped, tab: srcView.tab, view: srcView.view
    } : null;
    const p = openSourcePeek(spec);
    srcView.back = back;
    pdiffSyncChrome();
    return p;
  }

  function pdiffBack() {
    const b = srcView.back;
    if (!b) return Promise.resolve(false);
    return openSourceViewer("compare", b.specs, { pair: b.pair, swap: b.swapped, tab: b.tab, view: b.view, texts: b.texts, errors: b.errors, keepFilters: true });
  }

  function pdiffKeys(ev) {
    if ((ev.key !== "n" && ev.key !== "p") || ev.ctrlKey || ev.metaKey || ev.altKey || ev.defaultPrevented) return;
    const t = ev.target;
    if (t && t.closest && t.closest("input, textarea, select, [contenteditable='true']")) return;
    if (!(srcView.mode === "compare" && srcView.tab === "source" && srcView.view !== "side")) return;
    ev.preventDefault();
    pdiffJumpHunk(ev.key === "n" ? 1 : -1);
  }

  // ---------- Lemma diff (offline) ----------
  function pdiffNameNode(it) {
    const short = it.short || shortName(it.name);
    if (it.origin === "project") {
      return el("a", { className: "pd-name", href: "#item/" + encodeURIComponent(it.name), title: it.name, onclick: () => closeSourceDrawer() }, [identWbr(short)]);
    }
    return el("span", { className: "pd-name", title: it.name }, [identWbr(short)]);
  }

  function pdiffNsNode(it) {
    const name = String(it.name || "");
    const short = it.short || shortName(name);
    const ns = name.endsWith("." + short) ? name.slice(0, -short.length - 1) : "";
    return ns ? el("span", { className: "pd-ns", title: name, textContent: ns + "." }) : null;
  }

  // Qualified name in reading order: muted namespace prefix, then the leaf.
  function pdiffQualNode(it) {
    return el("span", { className: "pd-qual" }, [pdiffNsNode(it), pdiffNameNode(it)]);
  }

  function pdiffActs(it, tag) {
    const out = [];
    if (it.origin === "project" && it.mod) {
      const url = buildGithubUrl(it.mod, it.line);
      if (url && isLeanBlob(url)) {
        out.push(el("button", { type: "button", className: "pd-act", textContent: tag ? "Peek " + tag : "Peek", title: "Preview " + it.name, onclick: () => pdiffPeek({ url, title: it.name, line: it.line }) }));
      }
      if (url) out.push(el("a", { className: "pd-act pd-loc", href: url, target: "_blank", rel: "noopener noreferrer", title: it.mod + (it.line ? ":" + it.line : ""), textContent: shortName(it.mod) + (it.line ? ":" + it.line : "") + " ↗" }));
    } else if (it.origin === "mathlib4" || it.origin === "lean4") {
      out.push(el("a", { className: "pd-act", href: pdiffDocsUrl(it.name), target: "_blank", rel: "noopener noreferrer", title: "Documentation for " + it.name, textContent: "docs ↗" }));
    }
    return out;
  }

  function pdiffRolePill(role) {
    return el("span", { className: "pd-pill role", title: PDIFF_ROLE_TIP[role] || "", textContent: PDIFF_ROLE[role] || String(role || "") });
  }

  function pdiffShiftPill(from, to) {
    return el("span", { className: "pd-pill shift", title: "In A: " + (PDIFF_ROLE_TIP[from] || from).toLowerCase() + ". In B: " + (PDIFF_ROLE_TIP[to] || to).toLowerCase() + ".", textContent: (PDIFF_ROLE[from] || from) + " → " + (PDIFF_ROLE[to] || to) });
  }

  // One lemma row. `side` ("a" | "b") renders one half of a split row.
  function pdiffRowNode(r, side) {
    const h = r.helper;
    let it = r.it;
    let names;
    const pills = [];
    if (h) {
      it = side === "a" ? h.a : h.b;
      names = side ? [pdiffQualNode(it)] : [pdiffQualNode(h.a), el("span", { className: "pd-arrow", "aria-label": "renamed to", textContent: "→" }), pdiffQualNode(h.b)];
      pills.push(pdiffRolePill(it.role));
      if (!side || side === "b") pills.push(el("span", { className: "pd-pill reason", title: PDIFF_REASON_TIP[h.reason] || "", textContent: PDIFF_REASON[h.reason] || String(h.reason || "relocated") }));
    } else {
      names = [pdiffQualNode(it)];
      if (r.role) pills.push(side ? pdiffRolePill(side === "a" ? r.role.role_a : r.role.role_b) : pdiffShiftPill(r.role.role_a, r.role.role_b));
      else pills.push(pdiffRolePill(it.role));
    }
    const originLbl = pdiffOriginLabel(it);
    pills.push(el("span", { className: "pd-pill origin " + (it.origin === "project" ? "proj" : (originLbl === "Lean core" ? "core" : "lib")), textContent: originLbl }));
    if (Number(it.fan_in) > 0) pills.push(el("span", { className: "pd-used", title: "Number of declarations that use this one", textContent: "used by " + fmtInt(it.fan_in) }));
    const acts = h && !side ? pdiffActs(h.a, "A").concat(pdiffActs(h.b, "B")) : pdiffActs(it);
    return el("div", { className: "pd-row " + r.kind, role: "listitem", "data-kind": r.kind }, [
      el("span", { className: "pd-g", role: "img", "aria-label": PDIFF_KIND_WORD[r.kind], textContent: PDIFF_GLYPH[r.kind] }),
      el("div", { className: "pd-main" }, [el("div", { className: "pd-names" }, names), el("div", { className: "pd-meta" }, pills)]),
      acts.length ? el("div", { className: "pd-acts" }, acts) : null
    ]);
  }

  function buildLemmaDiffPanel(pair, swapped, opts) {
    const o = opts || {};
    const st = pdiffState;
    const D = pdiffOrient(pair.proof_diff, swapped);
    const thmA = swapped ? pair.thm_b : pair.thm_a;
    const thmB = swapped ? pair.thm_a : pair.thm_b;
    const hay = (...its) => its.flatMap((it) => [it.name, it.mod, pdiffOriginLabel(it)]).filter(Boolean).join(" ").toLowerCase();
    const B = pdiffBuckets(D);
    const rows = [];
    // Buckets are disjoint: a role shift is listed only under Role differs.
    D.removed.forEach((it) => { if (!B.roleIds.has(it.decl_id)) rows.push({ kind: "del", it, project: it.origin === "project", hay: hay(it) }); });
    D.added.forEach((it) => { if (!B.roleIds.has(it.decl_id)) rows.push({ kind: "add", it, project: it.origin === "project", hay: hay(it) }); });
    D.role.forEach((r) => rows.push({ kind: "mv", role: r, it: r, project: r.origin === "project", hay: hay(r) }));
    D.helper.forEach((hp) => rows.push({ kind: "mv", helper: hp, it: hp.b, project: hp.a.origin === "project" || hp.b.origin === "project", hay: hay(hp.a, hp.b) }));
    D.shared.forEach((it) => rows.push({ kind: "eq", it, project: it.origin === "project", hay: hay(it) }));
    const KIND = { removed: "del", added: "add", moved: "mv", shared: "eq" };
    const listed = (k) => rows.filter((r) => r.kind === KIND[k]).length;
    // Lemmas counted in the totals but left out of this preview's lists.
    const TRUNC = {};
    Object.keys(KIND).forEach((k) => { TRUNC[k] = Math.max(0, B.total[k] - listed(k)); });
    const TRUNC_NOUN = { removed: "lemmas only in A", added: "lemmas only in B", moved: "lemmas whose role differs", shared: "shared lemmas" };
    const SEC = {
      removed: ["Only in proof A", "used by A, by neither part of B"],
      added: ["Only in proof B", "used by B, by neither part of A"],
      moved: ["Role differs", "role in A → role in B, plus helpers renamed between the two proofs"],
      shared: ["Shared", "same role in both"]
    };

    const viewSeg = el("div", { className: "seg pd-viewseg", role: "group", "aria-label": "Layout" }, [["unified", "Unified"], ["split", "Split"]].map(([k, lbl]) =>
      el("button", { type: "button", "data-k": k, textContent: lbl, onclick: () => { st.view = k; draw(); } })));
    const chips = el("div", { className: "pd-chips", role: "group", "aria-label": "Show" }, PDIFF_KINDS.map(([k, lbl, g, cls]) =>
      el("button", { type: "button", className: "pd-chip " + (cls || "all"), "data-k": k, onclick: () => { st.filter = k; if (k === "shared") st.sharedOpen = true; draw(); } }, [
        g ? el("span", { className: "pd-chip-g", "aria-hidden": "true", textContent: g }) : null,
        el("span", { className: "pd-chip-l", textContent: lbl }),
        el("span", { className: "pd-chip-n" })
      ])));
    const proj = el("input", { type: "checkbox", className: "pd-proj", onchange: (ev) => { st.projectOnly = ev.currentTarget.checked; draw(); } });
    proj.checked = st.projectOnly;
    const q = el("input", {
      type: "search", className: "input pd-q", placeholder: "Filter lemmas", "aria-label": "Filter lemmas by name or module", autocomplete: "off", spellcheck: "false",
      oninput: (ev) => { st.q = ev.currentTarget.value; draw(); },
      onkeydown: (ev) => {
        if (ev.key === "Escape" && ev.currentTarget.value) { ev.preventDefault(); ev.stopPropagation(); ev.currentTarget.value = ""; st.q = ""; draw(); }
      }
    });
    q.value = st.q;
    const list = el("div", { className: "pd-list", role: "list", "aria-live": "polite" });
    const sideLine = (label, thm, ev) => el("div", { className: "pd-side" }, [
      el("span", { className: "pd-tag", textContent: label }),
      el("span", { className: "pd-side-name", title: thm.name }, [identWbr(thm.name)]),
      el("span", { className: "pd-side-meta", title: "Constants the proof term refers to, including binder types such as Nat or OfNat.ofNat", textContent: plural(ev, "reference") + " in the proof" })
    ]);
    const head = el("div", { className: "pd-head" }, [
      el("div", { className: "pd-sides" }, [sideLine("A", thmA, D.c.aEv), sideLine("B", thmB, D.c.bEv)]),
      buildProofDiffBar(pair.proof_diff, swapped, { onPick: (k) => { st.filter = k; if (k === "shared") st.sharedOpen = true; draw(); } })
    ]);
    const ctrls = el("div", { className: "pd-ctrls" }, [
      viewSeg, chips,
      el("label", { className: "ld-check pd-proj-l", title: "Hide Mathlib and Lean core lemmas" }, [proj, "Project only"]),
      q
    ]);
    const to = D.typeOnly;
    const hasXrefCmp = Boolean(xrefsBaseUrl() && window.LeanreXrefs && thmA && thmA.name && thmB && thmB.name);
    const fullCmpHref = hasXrefCmp ? "#xrefs/" + encodeURIComponent(thmA.name) + "?cmp=" + encodeURIComponent(thmB.name) : null;
    const foot = el("p", { className: "pd-foot" }, [
      "A lemma counts as used by a proof when its proof term refers to it. Used only in the statement (not the proof): " +
      fmtInt(to.shared) + " in both, " + fmtInt(to.aOnly) + " only in A, " + fmtInt(to.bOnly) + " only in B." +
      (to.aOnly || to.bOnly ? " The statements match, so a difference here means the other theorem's proof also uses that constant." : ""),
      fullCmpHref ? " " : null,
      fullCmpHref ? el("a", {
        href: fullCmpHref, textContent: "Complete untruncated diff in Cross-refs ›",
        onclick: (ev) => { ev.preventDefault(); closeSourceDrawer(); navigate(fullCmpHref); }
      }) : null
    ]);

    const draw = () => {
      $$("button", viewSeg).forEach((b) => { const on = b.dataset.k === st.view; b.classList.toggle("active", on); b.setAttribute("aria-pressed", on ? "true" : "false"); });
      const terms = st.q.trim().toLowerCase().split(/\s+/).filter(Boolean);
      const narrowed = st.projectOnly || terms.length > 0;
      const vis = rows.filter((r) => (!st.projectOnly || r.project) && terms.every((t) => r.hay.includes(t)));
      const of = (kind) => vis.filter((r) => r.kind === kind);
      // Chip counts are the full totals; once narrowed, the visible rows.
      const n = narrowed
        ? { removed: of("del").length, added: of("add").length, moved: of("mv").length, shared: of("eq").length }
        : Object.assign({}, B.total);
      n.all = n.removed + n.added + n.moved + n.shared;
      $$("button", chips).forEach((b) => {
        const on = b.dataset.k === st.filter;
        b.classList.toggle("active", on);
        b.setAttribute("aria-pressed", on ? "true" : "false");
        b.querySelector(".pd-chip-n").textContent = fmtInt(n[b.dataset.k]);
      });
      clearEl(list);
      const keys = st.filter === "all" ? ["removed", "added", "moved", "shared"] : [st.filter];
      const truncNote = (k) => (TRUNC[k] > 0 ? el("p", { className: "pd-trunc", textContent: "+ " + fmtInt(TRUNC[k]) + " more " + TRUNC_NOUN[k] + " not included in this preview." }) : null);
      const secHead = (k, count) => el("div", { className: "pd-sec " + KIND[k] }, [
        el("span", { className: "pd-sec-g", "aria-hidden": "true", textContent: PDIFF_GLYPH[KIND[k]] }),
        el("span", { className: "pd-sec-t", textContent: SEC[k][0] }),
        el("span", { className: "pd-sec-n", textContent: !narrowed && TRUNC[k] > 0 ? fmtInt(count) + " shown of " + fmtInt(B.total[k]) : fmtInt(count) }),
        el("span", { className: "pd-sec-s", textContent: SEC[k][1] })
      ]);
      let shown = 0;
      if (st.view === "split") {
        list.classList.add("split");
        list.appendChild(el("div", { className: "pd-split-hd" }, [
          el("div", null, [el("span", { className: "pd-tag", textContent: "A" }), el("span", { className: "pd-side-name", title: thmA.name, textContent: shortName(thmA.name) })]),
          el("div", null, [el("span", { className: "pd-tag", textContent: "B" }), el("span", { className: "pd-side-name", title: thmB.name, textContent: shortName(thmB.name) })])
        ]));
        if (keys.includes("moved")) {
          const mv = of("mv");
          if (mv.length || st.filter === "moved") list.appendChild(secHead("moved", mv.length));
          mv.forEach((r) => { shown++; list.appendChild(el("div", { className: "pd-srow" }, [pdiffRowNode(r, "a"), pdiffRowNode(r, "b")])); });
          if (mv.length) appendNode(list, truncNote("moved"));
        }
        if (keys.includes("removed") || keys.includes("added")) {
          const left = keys.includes("removed") ? of("del") : [];
          const right = keys.includes("added") ? of("add") : [];
          shown += left.length + right.length;
          const col = (rs, k) => el("div", { className: "pd-col" }, [secHead(k, rs.length)].concat(
            rs.length ? rs.map((r) => pdiffRowNode(r)) : [el("p", { className: "pd-empty", textContent: keys.includes(k) ? "None." : "Hidden by the filter." })],
            [truncNote(k)]));
          if (left.length || right.length || st.filter !== "all") list.appendChild(el("div", { className: "pd-cols" }, [col(left, "removed"), col(right, "added")]));
        }
        if (keys.includes("shared")) shown += pdiffSharedBlock(list, of("eq"), st, secHead, truncNote, draw, true);
      } else {
        list.classList.remove("split");
        for (const k of keys) {
          if (k === "shared") { shown += pdiffSharedBlock(list, of("eq"), st, secHead, truncNote, draw, false); continue; }
          const rs = of(KIND[k]);
          if (!rs.length && st.filter === "all" && !TRUNC[k]) continue;
          list.appendChild(secHead(k, rs.length));
          rs.forEach((r) => { shown++; list.appendChild(pdiffRowNode(r)); });
          appendNode(list, truncNote(k));
        }
      }
      if (!shown && !list.querySelector(".pd-shared-btn")) list.appendChild(el("p", { className: "pd-empty", textContent: narrowed ? "No lemmas match these filters." : "Nothing to show for this filter." }));
    };
    draw();
    const legend = el("p", { className: "pd-legend" }, [
      el("b", { textContent: "−" }), " only in proof A · ", el("b", { textContent: "+" }), " only in proof B · ",
      el("b", { textContent: "⇄" }), " role differs, read as role in A → role in B (statement: only in the statement; proof: only in the proof; both: in both) · ",
      el("b", { textContent: "=" }), " shared, same role in both"
    ]);
    return el("div", { className: "pdiff-panel" + (o.compact ? " compact" : "") }, [head, ctrls, legend, list, foot]);
  }

  // Shared lemmas start collapsed under All; returns the number of rows drawn.
  function pdiffSharedBlock(list, rs, st, secHead, truncNote, draw, split) {
    const total = rs.length;
    if (!total && st.filter === "all" && !truncNote("shared")) return 0;
    list.appendChild(secHead("shared", total));
    if (st.filter === "all" && !st.sharedOpen) {
      if (total) list.appendChild(el("button", { type: "button", className: "btn sm pd-shared-btn", textContent: "Show " + plural(total, "shared lemma"), onclick: () => { st.sharedOpen = true; draw(); } }));
      appendNode(list, truncNote("shared"));
      return 0;
    }
    rs.forEach((r) => list.appendChild(split ? el("div", { className: "pd-srow span" }, [pdiffRowNode(r)]) : pdiffRowNode(r)));
    appendNode(list, truncNote("shared"));
    return total;
  }

  function pdiffRenderLemmaBody() {
    const body = $("#srcBody");
    if (!body || !srcView.pair) return;
    clearEl(body);
    body.classList.add("pdiff-host");
    body.appendChild(el("div", { className: "pdiff-scroll" }, [buildLemmaDiffPanel(srcView.pair, srcView.swapped)]));
  }

  // ---------- Line diff engine (pure) ----------
  // Myers O(ND) on interned line ids over [a0, a1) x [b0, b1). Returns ops
  // ({t:"=",a,b} | {t:"-",a} | {t:"+",b}) or null when D exceeds maxD.
  function ldMyers(a, b, a0, a1, b0, b1, maxD) {
    const head = [], tail = [];
    while (a0 < a1 && b0 < b1 && a[a0] === b[b0]) head.push({ t: "=", a: a0++, b: b0++ });
    while (a0 < a1 && b0 < b1 && a[a1 - 1] === b[b1 - 1]) tail.push({ t: "=", a: --a1, b: --b1 });
    tail.reverse();
    const N = a1 - a0, M = b1 - b0;
    const mid = [];
    if (!N || !M) {
      for (let i = a0; i < a1; i++) mid.push({ t: "-", a: i });
      for (let j = b0; j < b1; j++) mid.push({ t: "+", b: j });
    } else {
      const MAX = N + M, off = MAX + 1;
      const v = new Int32Array(2 * MAX + 3);
      const trace = [];
      let D = -1;
      const lim = Math.min(MAX, maxD);
      outer: for (let d = 0; d <= lim; d++) {
        trace.push(v.slice(off - d - 1, off + d + 2));
        for (let k = -d; k <= d; k += 2) {
          let x = (k === -d || (k !== d && v[off + k - 1] < v[off + k + 1])) ? v[off + k + 1] : v[off + k - 1] + 1;
          let y = x - k;
          while (x < N && y < M && a[a0 + x] === b[b0 + y]) { x++; y++; }
          v[off + k] = x;
          if (x >= N && y >= M) { D = d; break outer; }
        }
      }
      if (D < 0) return null;
      const rev = [];
      let x = N, y = M;
      for (let d = D; d >= 0; d--) {
        const snap = trace[d];
        const at = (k) => snap[k + d + 1];
        const k = x - y;
        const pk = (k === -d || (k !== d && at(k - 1) < at(k + 1))) ? k + 1 : k - 1;
        const px = at(pk), py = px - pk;
        while (x > px && y > py) { rev.push({ t: "=", a: a0 + x - 1, b: b0 + y - 1 }); x--; y--; }
        if (d > 0) rev.push(x === px ? { t: "+", b: b0 + y - 1 } : { t: "-", a: a0 + x - 1 });
        x = px; y = py;
      }
      for (let i = rev.length - 1; i >= 0; i--) mid.push(rev[i]);
    }
    return head.concat(mid, tail);
  }

  // Patience fallback for large windows: anchor on lines unique to both sides
  // (longest increasing run), recurse between anchors, and give small gaps to Myers.
  function ldPatience(a, b, a0, a1, b0, b1, depth) {
    const out = [];
    const push = (arr) => { for (const x of arr) out.push(x); };
    while (a0 < a1 && b0 < b1 && a[a0] === b[b0]) out.push({ t: "=", a: a0++, b: b0++ });
    const tail = [];
    while (a0 < a1 && b0 < b1 && a[a1 - 1] === b[b1 - 1]) tail.push({ t: "=", a: --a1, b: --b1 });
    tail.reverse();
    const N = a1 - a0, M = b1 - b0;
    const plain = () => { for (let i = a0; i < a1; i++) out.push({ t: "-", a: i }); for (let j = b0; j < b1; j++) out.push({ t: "+", b: j }); };
    if (!N || !M) plain();
    else if (N * M <= 250000 || depth > 12) {
      const m = ldMyers(a, b, a0, a1, b0, b1, 500);
      if (m) push(m); else plain();
    } else {
      const ca = new Map(), cb = new Map();
      for (let i = a0; i < a1; i++) { const e = ca.get(a[i]); if (e) e.n++; else ca.set(a[i], { n: 1, i }); }
      for (let j = b0; j < b1; j++) { const e = cb.get(b[j]); if (e) e.n++; else cb.set(b[j], { n: 1, j }); }
      const cand = [];
      for (const [key, e] of ca) { const f = cb.get(key); if (e.n === 1 && f && f.n === 1) cand.push([e.i, f.j]); }
      cand.sort((p, q) => p[0] - q[0]);
      // Longest increasing subsequence on the B positions.
      const tails = [], prev = new Array(cand.length).fill(-1);
      cand.forEach(([, j], idx) => {
        let lo = 0, hi = tails.length;
        while (lo < hi) { const mid = (lo + hi) >> 1; if (cand[tails[mid]][1] < j) lo = mid + 1; else hi = mid; }
        if (lo > 0) prev[idx] = tails[lo - 1];
        tails[lo] = idx;
      });
      const lis = [];
      for (let t = tails.length ? tails[tails.length - 1] : -1; t >= 0; t = prev[t]) lis.push(cand[t]);
      lis.reverse();
      if (!lis.length) plain();
      else {
        let pi = a0, pj = b0;
        for (const [i, j] of lis) {
          push(ldPatience(a, b, pi, i, pj, j, depth + 1));
          out.push({ t: "=", a: i, b: j });
          pi = i + 1; pj = j + 1;
        }
        push(ldPatience(a, b, pi, a1, pj, b1, depth + 1));
      }
    }
    push(tail);
    return out;
  }

  const LD_TRIVIAL = /^(?:[\s()[\]{}⟨⟩,.:;|·•=<>_-]*|by|end|where|do|then|else|done|rfl|simp|trivial|exact rfl|sorry|norm_num|ring|omega|linarith|constructor|intro|intros|assumption)$/;

  function ldTokens(s) {
    return String(s).match(/\s+|[\p{L}\p{N}_'.!?₀-₉]+|./gu) || [];
  }

  // Word-level diff of two lines: [[changed, text], ...] for each side plus a
  // similarity in [0, 1] (shared non-space tokens).
  function ldWordDiff(lineA, lineB) {
    const ta = ldTokens(lineA), tb = ldTokens(lineB);
    const ids = new Map();
    const id = (s) => { let v = ids.get(s); if (v == null) { v = ids.size; ids.set(s, v); } return v; };
    const ia = ta.map(id), ib = tb.map(id);
    const ops = ldMyers(ia, ib, 0, ia.length, 0, ib.length, 400);
    if (!ops) return { sim: 0, a: [[true, lineA]], b: [[true, lineB]] };
    const segA = [], segB = [];
    const add = (seg, changed, txt) => { const last = seg[seg.length - 1]; if (last && last[0] === changed) last[1] += txt; else seg.push([changed, txt]); };
    let same = 0;
    for (const op of ops) {
      if (op.t === "=") { add(segA, false, ta[op.a]); add(segB, false, tb[op.b]); if (/\S/.test(ta[op.a])) same++; }
      else if (op.t === "-") add(segA, /\S/.test(ta[op.a]), ta[op.a]);
      else add(segB, /\S/.test(tb[op.b]), tb[op.b]);
    }
    const solid = (t) => t.filter((x) => /\S/.test(x)).length;
    const denom = solid(ta) + solid(tb);
    return { sim: denom ? (2 * same) / denom : 1, a: segA, b: segB };
  }

  // Line diff with moved blocks. Returns { ops, stats, fallback } where each op
  // is one of: "=" (a, b) | "-" (a) | "+" (b) | "m-" (a, to, block) | "m+" (b, from, block).
  // Modified "-"/"+" lines in the same hunk carry `segs` for word highlights.
  function diffLinesWithMoves(linesA, linesB, opts) {
    const o = opts || {};
    const A = (linesA || []).map((s) => String(s));
    const B = (linesB || []).map((s) => String(s));
    const squash = (s) => s.replace(/\s+/g, " ").trim();
    const norm = o.ignoreWhitespace ? squash : (s) => s.replace(/\s+$/, "");
    const ids = new Map();
    const intern = (s) => { const k = norm(s); let v = ids.get(k); if (v == null) { v = ids.size; ids.set(k, v); } return v; };
    const a = A.map(intern), b = B.map(intern);
    const cap = Number(o.maxLines) || LD_MAX_LINES;
    let fallback = A.length > cap || B.length > cap;
    let ops = fallback ? null : ldMyers(a, b, 0, a.length, 0, b.length, Number(o.maxD) || 1200);
    if (!ops) { fallback = true; ops = ldPatience(a, b, 0, a.length, 0, b.length, 0); }

    // Hunk ids: consecutive non-equal ops share one.
    let hunk = -1, inHunk = false;
    for (const op of ops) {
      if (op.t === "=") { inHunk = false; continue; }
      if (!inHunk) { hunk++; inHunk = true; }
      op.h = hunk;
    }

    // Moved blocks: removed lines whose text reappears as added lines in a
    // different hunk. Runs of two or more lines qualify; a single line must be
    // long enough not to be boilerplate.
    const minLen = Number(o.minMoveChars) || 16;
    const addsByKey = new Map();
    ops.forEach((op, i) => {
      if (op.t !== "+") return;
      const k = squash(B[op.b]);
      if (!k || LD_TRIVIAL.test(k)) return;
      if (!addsByKey.has(k)) addsByKey.set(k, []);
      addsByKey.get(k).push(i);
    });
    const used = new Set();
    const partner = new Map(); // op index of "-" -> op index of "+"
    let lastDel = -1, lastAdd = -1;
    ops.forEach((op, i) => {
      if (op.t !== "-") return;
      const k = squash(A[op.a]);
      const cands = addsByKey.get(k);
      if (!cands) return;
      const free = cands.filter((j) => !used.has(j) && ops[j].h !== op.h);
      if (!free.length) return;
      // Prefer continuing the previous pair's block.
      let pick = free[0];
      if (lastDel >= 0 && ops[lastDel].a === op.a - 1) {
        const want = ops[lastAdd].b + 1;
        const cont = free.find((j) => ops[j].b === want);
        if (cont != null) pick = cont;
      }
      used.add(pick);
      partner.set(i, pick);
      lastDel = i; lastAdd = pick;
    });
    // Group pairs into blocks of consecutive lines on both sides.
    const pairs = Array.from(partner.entries()).sort((p, q) => ops[p[0]].a - ops[q[0]].a);
    const blocks = [];
    for (const [di, ai] of pairs) {
      const cur = blocks[blocks.length - 1];
      const prev = cur && cur[cur.length - 1];
      if (prev && ops[prev[0]].a === ops[di].a - 1 && ops[prev[1]].b === ops[ai].b - 1) cur.push([di, ai]);
      else blocks.push([[di, ai]]);
    }
    let blockId = 0, movedLines = 0;
    for (const blk of blocks) {
      if (blk.length < 2 && squash(A[ops[blk[0][0]].a]).length < minLen) continue;
      for (const [di, ai] of blk) {
        const d = ops[di], ad = ops[ai];
        d.t = "m-"; d.to = ad.b; d.block = blockId;
        ad.t = "m+"; ad.from = d.a; ad.block = blockId;
        movedLines++;
      }
      blockId++;
    }

    // Word highlights for modified lines: pair remaining "-" and "+" in order
    // within each hunk when they are similar enough.
    const byHunk = new Map();
    ops.forEach((op) => {
      if (op.t !== "-" && op.t !== "+") return;
      if (!byHunk.has(op.h)) byHunk.set(op.h, { del: [], add: [] });
      byHunk.get(op.h)[op.t === "-" ? "del" : "add"].push(op);
    });
    let modified = 0;
    for (const { del, add } of byHunk.values()) {
      const n = Math.min(del.length, add.length);
      for (let i = 0; i < n; i++) {
        const w = ldWordDiff(A[del[i].a], B[add[i].b]);
        if (w.sim < 0.35) continue;
        del[i].segs = w.a; add[i].segs = w.b;
        del[i].pair = add[i].b; add[i].pair = del[i].a;
        modified++;
      }
    }
    const count = (t) => ops.reduce((s, op) => s + (op.t === t ? 1 : 0), 0);
    return {
      ops, fallback,
      stats: { equal: count("="), removed: count("-"), added: count("+"), moved: movedLines, movedBlocks: blockId, modified, hunks: hunk + 1 }
    };
  }

  // ---------- Line diff rendering ----------
  function ldSplitLines(text) {
    const lines = String(text == null ? "" : text).replace(/\r\n?/g, "\n").split("\n");
    if (lines.length > 1 && lines[lines.length - 1] === "") lines.pop();
    return lines;
  }

  function ldTokenizeRange(lines, from, to) {
    const st = { depth: 0, expectName: false };
    for (let i = 0; i < from - 1; i++) tokenizeLeanLine(lines[i], st);
    const out = [];
    for (let ln = from; ln <= to; ln++) out.push(tokenizeLeanLine(lines[ln - 1], st));
    return out;
  }

  function ldFlash(node) {
    if (!node) return;
    try { node.scrollIntoView({ block: "center", behavior: "auto" }); } catch (_) { node.scrollIntoView(); }
    node.classList.remove("flash");
    void node.offsetWidth;
    node.classList.add("flash");
    clearTimeout(node._flashT);
    node._flashT = setTimeout(() => node.classList.remove("flash"), 1400);
  }

  function pdiffJumpHunk(dir) {
    const hs = srcView.ldHunks || [];
    const status = $("#srcStatus");
    if (!hs.length) { flashStatus(status, "No changes in this window"); return; }
    let i = pdiffState.hunk;
    i = i < 0 ? (dir > 0 ? 0 : hs.length - 1) : (i + dir + hs.length) % hs.length;
    pdiffState.hunk = i;
    ldFlash(hs[i]);
    flashStatus(status, "Change " + (i + 1) + " of " + hs.length, null, 3000);
  }

  function pdiffSourceFallback(body) {
    const missing = srcView.specs.map((s, i) => (srcView.errors[i] ? { s, err: srcView.errors[i] } : null)).filter(Boolean);
    const links = missing.map(({ s }) => {
      const alt = safeHref(s.fallbackUrl);
      return alt ? el("a", { className: "btn sm", href: alt, target: "_blank", rel: "noopener noreferrer", textContent: (s.fallbackLabel || "Open documentation ↗").replace(/ ↗$/, "") + " for " + s.label + " ↗" }) : null;
    });
    const card = el("div", { className: "ld-unavail" }, [
      el("h4", { textContent: "No line diff for this pair" }),
      ...missing.map(({ s, err }) => el("p", null, [
        el("strong", { textContent: "Side " + s.label + " " }),
        el("span", { className: "mono", title: s.title, textContent: shortName(s.title) }),
        ": " + sourceErrorMessage(s, err)
      ])),
      srcView.pair ? el("p", { className: "pd-trunc", textContent: "The lemma diff needs no source files and is shown alongside." }) : null,
      el("div", { className: "cir-ins-acts" }, links.concat([
        el("button", { type: "button", className: "btn sm", textContent: "Side-by-side", onclick: () => pdiffSetView("side") }),
        srcView.pair ? el("button", { type: "button", className: "btn sm", textContent: "Lemma diff", onclick: () => pdiffSetTab("lemmas") }) : null
      ]))
    ]);
    body.appendChild(el("div", { className: "pdiff-scroll" }, [
      el("div", { className: "ld-fallback" + (srcView.pair ? " with-lemmas" : "") }, [
        card,
        srcView.pair ? buildLemmaDiffPanel(srcView.pair, srcView.swapped, { compact: true }) : null
      ])
    ]));
  }

  function pdiffRenderSourceDiff() {
    const body = $("#srcBody");
    if (!body || srcView.mode !== "compare") return;
    clearEl(body);
    body.classList.add("pdiff-host");
    srcView.ldHunks = [];
    const [sa, sb] = srcView.specs;
    const [ta, tb] = srcView.texts;
    const [ea, eb] = srcView.errors || [];
    if ((ta == null && !ea) || (tb == null && !eb)) {
      body.appendChild(el("div", { className: "src-loading" }, [el("div", { className: "spinner" }), el("span", { textContent: "Loading both files…" })]));
      return;
    }
    if (ea || eb) { pdiffSourceFallback(body); return; }
    $$("#srcCtxSeg button").forEach((b) => b.classList.toggle("active", b.dataset.ctx === srcView.ctx));
    const la = ldSplitLines(ta), lb = ldSplitLines(tb);
    const ba = sliceBounds(sa, la.length), bb = sliceBounds(sb, lb.length);
    const res = diffLinesWithMoves(la.slice(ba.from - 1, ba.to), lb.slice(bb.from - 1, bb.to), { ignoreWhitespace: pdiffState.ignoreWs });
    const offA = ba.from - 1, offB = bb.from - 1;
    const tokA = ldTokenizeRange(la, ba.from, ba.to), tokB = ldTokenizeRange(lb, bb.from, bb.to);
    const split = srcView.view === "split";
    const code = el("div", { className: "ld-code " + (split ? "split" : "unified"), role: "table", "aria-label": "Line diff of A against B" });

    const cls = (op) => ({ "=": "eq", "-": "del", "+": "add", "m-": "mv mv-from", "m+": "mv mv-to" })[op.t];
    const glyph = (op) => ({ "=": " ", "-": "−", "+": "+", "m-": "⇄", "m+": "⇄" })[op.t];
    const word = (op) => ({ "=": "unchanged", "-": "removed", "+": "added", "m-": "moved", "m+": "moved" })[op.t];
    const text = (op, side) => {
      if (op.segs) return el("span", { className: "ld-txt" }, op.segs.map(([chg, t]) => (chg ? el("mark", { className: "ld-w", textContent: t }) : document.createTextNode(t))));
      const toks = side === "b" ? tokB[op.b] : tokA[op.a];
      return el("span", { className: "ld-txt" }, [renderLeanTokens(toks || [], (side === "b" ? sb : sa).links)]);
    };
    const mvTag = (op) => {
      if (op.t === "m-") {
        const ln = op.to + offB + 1;
        return el("button", { type: "button", className: "ld-mv-tag", title: "Jump to where this line appears in B", textContent: "⇄ moved to line " + ln, onclick: () => ldFlash(code.querySelector('[data-b="' + ln + '"]')) });
      }
      if (op.t === "m+") {
        const ln = op.from + offA + 1;
        return el("button", { type: "button", className: "ld-mv-tag", title: "Jump to where this line was in A", textContent: "⇄ moved from line " + ln, onclick: () => ldFlash(code.querySelector('[data-a="' + ln + '"]')) });
      }
      return null;
    };
    const lnA = (op) => (op.a != null ? op.a + offA + 1 : null);
    const lnB = (op) => (op.b != null ? op.b + offB + 1 : null);
    const urow = (op) => el("div", { className: "ld-row " + cls(op), role: "row", "data-a": op.t === "+" || op.t === "m+" ? null : lnA(op), "data-b": op.t === "-" || op.t === "m-" ? null : lnB(op) }, [
      el("span", { className: "ld-ln", textContent: lnA(op) == null ? "" : String(lnA(op)) }),
      el("span", { className: "ld-ln", textContent: lnB(op) == null ? "" : String(lnB(op)) }),
      el("span", { className: "ld-g", role: "img", "aria-label": word(op), textContent: glyph(op) }),
      text(op, op.t === "+" || op.t === "m+" ? "b" : "a"),
      mvTag(op)
    ]);
    const scell = (op, side) => {
      if (!op) return el("div", { className: "ld-cell empty", "aria-hidden": "true" });
      const ln = side === "a" ? lnA(op) : lnB(op);
      return el("div", { className: "ld-cell " + cls(op), role: "cell", "data-a": side === "a" ? ln : null, "data-b": side === "b" ? ln : null }, [
        el("span", { className: "ld-ln", textContent: String(ln) }),
        el("span", { className: "ld-g", role: "img", "aria-label": word(op), textContent: glyph(op) }),
        text(op, side),
        mvTag(op)
      ]);
    };

    // Display list: ops, with long unchanged runs folded when asked.
    const ops = res.ops;
    const items = [];
    for (let i = 0; i < ops.length;) {
      if (ops[i].t !== "=") { items.push(ops[i]); i++; continue; }
      let j = i;
      while (j < ops.length && ops[j].t === "=") j++;
      const keepHead = i === 0 ? 0 : LD_FOLD_CTX;
      const keepTail = j === ops.length ? 0 : LD_FOLD_CTX;
      const key = "f" + i;
      if (pdiffState.hideSame && j - i > keepHead + keepTail + 1 && !pdiffState.expanded.has(key) && res.stats.hunks > 0) {
        for (let k = i; k < i + keepHead; k++) items.push(ops[k]);
        items.push({ fold: key, n: j - i - keepHead - keepTail });
        for (let k = j - keepTail; k < j; k++) items.push(ops[k]);
      } else {
        for (let k = i; k < j; k++) items.push(ops[k]);
      }
      i = j;
    }
    const foldRow = (it) => el("button", {
      type: "button", className: "ld-fold", textContent: "Show " + plural(it.n, "unchanged line"),
      onclick: () => { pdiffState.expanded.add(it.fold); pdiffRenderSourceDiff(); }
    });
    if (!split) {
      let prevChange = false;
      for (const it of items) {
        if (it.fold) { code.appendChild(foldRow(it)); prevChange = false; continue; }
        const row = urow(it);
        const change = it.t !== "=";
        if (change && !prevChange) { row.classList.add("ld-hunk"); srcView.ldHunks.push(row); }
        prevChange = change;
        code.appendChild(row);
      }
    } else {
      let L = [], R = [];
      // Within a hunk: moved lines get rows of their own (blank opposite), and
      // plain removed/added lines are zipped so a modified line sits beside
      // its new version.
      const flush = () => {
        const moved = (xs) => xs.filter((x) => x.t === "m-" || x.t === "m+");
        const plain = (xs) => xs.filter((x) => x.t === "-" || x.t === "+");
        const pl = plain(L), pr = plain(R);
        const rowsOut = moved(L).map((x) => [x, null]);
        for (let k = 0; k < Math.max(pl.length, pr.length); k++) rowsOut.push([pl[k], pr[k]]);
        moved(R).forEach((x) => rowsOut.push([null, x]));
        rowsOut.forEach(([l, r], k) => {
          const row = el("div", { className: "ld-srow", role: "row" }, [scell(l, "a"), scell(r, "b")]);
          if (k === 0) { row.classList.add("ld-hunk"); srcView.ldHunks.push(row); }
          code.appendChild(row);
        });
        L = []; R = [];
      };
      for (const it of items) {
        if (it.fold) { flush(); code.appendChild(foldRow(it)); continue; }
        if (it.t === "=") { flush(); code.appendChild(el("div", { className: "ld-srow", role: "row" }, [scell(it, "a"), scell(it, "b")])); continue; }
        if (it.t === "-" || it.t === "m-") L.push(it); else R.push(it);
      }
      flush();
    }
    const s = res.stats;
    const stat = (k, g, n, w) => el("span", { className: "pdb-chip " + k + (n ? "" : " zero") }, [el("span", { className: "pdb-g", "aria-hidden": "true", textContent: g }), fmtInt(n) + " " + w]);
    const summary = el("div", { className: "ld-summary" }, [
      el("span", { className: "ld-range", textContent: "A lines " + ba.from + "–" + ba.to + " · B lines " + bb.from + "–" + bb.to }),
      stat("del", "−", s.removed, "removed"),
      stat("add", "+", s.added, "added"),
      stat("mv", "⇄", s.moved, "moved"),
      stat("eq", "=", s.equal, "unchanged"),
      !s.hunks ? el("span", { className: "ld-note", textContent: "The two windows are identical" + (pdiffState.ignoreWs ? " up to whitespace." : ".") }) : null,
      res.fallback ? el("span", { className: "ld-note", textContent: "Large window: a faster line matching was used, so some changes may be grouped coarsely." }) : null
    ]);
    body.appendChild(el("section", { className: "src-pane ld-pane" }, [summary, el("div", { className: "src-scroll ld-scroll" }, [code])]));
  }

  // #selftest=1 pass for the diff view. Fixtures only: no network.
  async function runV25DiffSelfTest(assert) {
    const tick = (ms) => new Promise((r) => setTimeout(r, ms || 0));
    const saved = Object.assign({}, pdiffState, { expanded: new Set() });
    const savedCtx = srcView.ctx;
    const esc = (target) => (target || document).dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true, cancelable: true }));
    const count = (ops, t) => ops.filter((op) => op.t === t).length;

    // 1. diffLinesWithMoves on a synthetic fixture: two lines moved up, one
    // line removed, one added, one modified in place.
    const fxA = [
      "theorem demo (x : Nat) : x = x := by",
      "  have m1 : x + 0 = x := Nat.add_zero x",
      "  have m2 : 0 + x = x := Nat.zero_add x",
      "  have m3 : x * 1 = x := Nat.mul_one x",
      "  have h1 : 0 ≤ x := Nat.zero_le x",
      "  have h2 : x ≤ x := Nat.le_refl x",
      "  have gone : x ≤ x + 1 := Nat.le_succ x",
      "  exact rfl"
    ];
    const fxB = [
      "theorem demo (x : Nat) : x = x := by",
      "  have h1 : 0 ≤ x := Nat.zero_le x",
      "  have h2 : x ≤ x := Nat.le_refl x",
      "  have m1 : x + 0 = x := Nat.add_zero x",
      "  have m2 : 0 + x = x := Nat.zero_add x",
      "  have m3 : x * 1 = x := Nat.mul_one x",
      "  have fresh : x ≤ 2 * x := Nat.le_mul_of_pos_left x two_pos",
      "  exact rfl"
    ];
    const r1 = diffLinesWithMoves(fxA, fxB);
    const mvFrom = r1.ops.filter((op) => op.t === "m-");
    const mvTo = r1.ops.filter((op) => op.t === "m+");
    assert(count(r1.ops, "=") === 5 && count(r1.ops, "-") === 1 && count(r1.ops, "+") === 1 && mvFrom.length === 2 && mvTo.length === 2 &&
      r1.stats.movedBlocks === 1 && mvFrom[0].a === 4 && mvFrom[0].to === 1 && mvTo[1].b === 2 && mvTo[1].from === 5 && !r1.fallback,
      "line diff classifies unchanged, removed, added and a moved block of two lines");
    const del = r1.ops.find((op) => op.t === "-"), add = r1.ops.find((op) => op.t === "+");
    assert(del && add && del.segs && add.segs && del.segs.some(([c, t]) => c && /gone/.test(t)) && add.segs.some(([c, t]) => c && /fresh/.test(t)) && del.segs.some(([c, t]) => !c && /have/.test(t)),
      "modified lines carry word-level highlights for the changed tokens only");
    const ws1 = diffLinesWithMoves(["  foo  bar", "baz"], ["foo bar", "baz"], { ignoreWhitespace: true });
    const ws2 = diffLinesWithMoves(["  foo  bar", "baz"], ["foo bar", "baz"]);
    assert(count(ws1.ops, "=") === 2 && count(ws2.ops, "-") === 1 && count(ws2.ops, "+") === 1 && count(ws2.ops, "m-") === 0,
      "ignore whitespace merges reindented lines; otherwise they show as a modified pair, not a move");
    const big = Array.from({ length: 3000 }, (_, i) => "line " + i);
    const bigB = big.slice(); bigB[1500] = "line 1500 changed";
    const r2 = diffLinesWithMoves(big, bigB);
    assert(r2.fallback && count(r2.ops, "=") === 2999 && count(r2.ops, "-") === 1 && count(r2.ops, "+") === 1, "files over 2,500 lines use the fast fallback and stay exact on a single edit");

    // Synthetic pair covering every lemma diff kind.
    const L = (name, role, origin, extra) => Object.assign({ name, short: shortName(name), decl_id: name.length * 1000 + name.charCodeAt(name.length - 1), role, origin, fan_in: 3 }, extra || {});
    const fxPair = {
      jaccard: 0.25, band: "variant",
      thm_a: { name: "Demo.alpha", origin: "project", value_nodes: 10, ev_size: 4 },
      thm_b: { name: "Demo.beta", origin: "project", value_nodes: 12, ev_size: 4 },
      proof_diff: {
        counts: { a_total: 7, b_total: 8, a_ev: 4, b_ev: 5, shared: 7, removed: 2, added: 2, moved_role: 2, moved_role_v: 0, moved_helper: 1, a_proof_only: 2, b_proof_only: 2, type_shared: 3, type_diff: 1, type_a_only: 1, type_b_only: 0 },
        removed: [L("Demo.onlyA_one", "value", "project"), L("Nat.succ_le_of_lt", "value", "lean4")],
        added: [L("Demo.onlyB_lemma", "both", "project", { decl_id: 77 }), L("Demo.onlyB_real", "value", "project")],
        moved_role: [
          { name: "Demo.onlyB_lemma", short: "onlyB_lemma", decl_id: 77, role_a: "type", role_b: "both", origin: "project", fan_in: 4 },
          { name: "Mathlib.shiftDemo", short: "shiftDemo", decl_id: 88, role_a: "both", role_b: "type", origin: "mathlib4", fan_in: 9 }
        ],
        moved_helper: [{ a: L("Demo.A.helper", "value", "project"), b: L("Demo.B.helper", "value", "project"), reason: "same_sig" }],
        shared: [L("Demo.common", "value", "project"), L("Mathlib.common_lemma", "value", "mathlib4")],
        type_only: { n_type_shared: 3, n_type_a_only: 1, n_type_b_only: 0, a_only: [], b_only: [] },
        truncated: { removed: 0, added: 0, shared: 5, moved_role: 0, moved_helper: 0 }
      }
    };

    // 2. Lemma diff: offline, filters, layout, swap, Esc.
    pdiffState.view = "unified";
    pdiffState.projectOnly = false;
    await openProofDiff(fxPair, { specs: [{ url: "", title: "Demo.alpha" }, { url: "", title: "Demo.beta" }] });
    const drawer = srcView.root;
    const rowsOf = (k) => $$(".pdiff-panel .pd-row" + (k ? "." + k : ""), drawer).length;
    const chipN = (k) => ((drawer.querySelector('.pd-chip[data-k="' + k + '"] .pd-chip-n') || {}).textContent || "");
    const chip = (k) => drawer.querySelector('.pd-chip[data-k="' + k + '"]');
    assert(!drawer.hidden && !$("#srcTabs").classList.contains("hidden") && drawer.querySelector('#srcTabs button[data-tab="lemmas"].active') && $("#srcViewSeg").classList.contains("hidden") && $("#srcDrawerTitle").textContent === "Compare proofs",
      "View diff opens the drawer on the lemma diff tab");
    assert(rowsOf("del") === 2 && rowsOf("add") === 1 && rowsOf("mv") === 3 && rowsOf("eq") === 0 && drawer.querySelector(".pd-shared-btn") &&
      chipN("removed") === "2" && chipN("added") === "1" && chipN("moved") === "3" && chipN("shared") === "7" && chipN("all") === "13",
      "lemma diff buckets are disjoint: a role shift is listed once, under Role differs, and All is their sum");
    assert(/Lean core/.test((drawer.querySelector(".pd-row.del .pd-pill.origin.core") || {}).textContent || "") && pdiffOriginLabel({ origin: "mathlib4", name: "And.right" }) === "Lean core" && pdiffOriginLabel({ origin: "mathlib4", name: "Nat.Prime" }) === "Mathlib",
      "Lean core constants carry a Lean core badge, not Mathlib");
    assert($$(".pd-row .pd-qual", drawer).some((q) => /^Demo\.onlyA_one$/.test(q.textContent)) && !$$(".pd-row .pd-names", drawer).some((q) => /^onlyA_one ?Demo/.test(q.textContent)),
      "lemma names read in qualified order (namespace prefix, then leaf)");
    assert(drawer.querySelector(".src-foot.hidden") && /role in A → role in B/.test((drawer.querySelector(".pd-legend") || {}).textContent || "") && /Used only in the statement/.test((drawer.querySelector(".pd-foot") || {}).textContent || ""),
      "lemma diff hides the live-fetch note, explains the role arrow and words the statement footnote plainly");
    assert(/statement → both/.test((drawer.querySelector(".pd-row.mv .pd-pill.shift") || {}).textContent || "") && /same signature/.test((drawer.querySelector(".pd-row.mv .pd-pill.reason") || {}).textContent || "") &&
      /\+ 5 more shared lemmas/.test(drawer.textContent) && drawer.querySelector(".pd-row.del .pd-g").textContent === "−",
      "rows show role shifts, relocation reasons, glyphs and the truncation note");
    chip("shared").click();
    assert(rowsOf("eq") === 2 && rowsOf("del") === 0 && chip("shared").getAttribute("aria-pressed") === "true", "Shared chip shows only shared lemmas");
    chip("moved").click();
    assert(rowsOf("mv") === 3 && rowsOf() === 3, "Moved chip shows every role shift and relocated helper");
    chip("all").click();
    drawer.querySelector('.pd-viewseg button[data-k="split"]').click();
    assert(drawer.querySelector(".pd-list.split .pd-split-hd") && $$(".pd-srow", drawer).length >= 2 && $$(".pd-cols .pd-col", drawer).length === 2, "split layout aligns moved lemmas and lists A-only and B-only side by side");
    drawer.querySelector('.pd-viewseg button[data-k="unified"]').click();
    $("#srcSwapBtn").click();
    assert(chipN("removed") === "1" && chipN("added") === "2" && /onlyA_one/.test((drawer.querySelector(".pd-row.add") || {}).textContent || "") && /onlyB_real/.test((drawer.querySelector(".pd-row.del") || {}).textContent || "") && /B: Demo\.alpha/.test($("#srcDrawerPath").textContent),
      "Swap A ↔ B trades Only in A and Only in B");
    $("#srcSwapBtn").click();
    const q = drawer.querySelector(".pd-q");
    q.focus();
    q.value = "helper";
    q.dispatchEvent(new Event("input", { bubbles: true }));
    await tick(0);
    assert(document.activeElement === q && drawer.querySelector(".pd-q") === q && rowsOf() === 1 && rowsOf("mv") === 1 && chipN("all") === "1", "text filter narrows rows while keeping focus");
    esc(q);
    assert(!drawer.hidden && q.value === "" && rowsOf() === 8, "Esc in a filled filter clears it without closing the drawer");
    const proj = drawer.querySelector(".pd-proj");
    proj.click();
    assert(rowsOf("del") === 1 && rowsOf("add") === 1 && rowsOf("mv") === 2 && chipN("all") === "5", "Project only hides Mathlib and Lean core lemmas");
    proj.click();
    assert(!UI_SLOP_WORDING.test(drawer.textContent || ""), "lemma diff copy reads plainly");
    esc();
    assert(drawer.hidden, "Esc closes the diff drawer");

    // 3. Line diff inside the compare drawer.
    const specA = { url: "https://github.com/example-owner/example-repo/blob/main/A.lean#L1", title: "Demo.alpha", label: "A", _fixtureText: fxA.concat(Array.from({ length: 12 }, (_, i) => "-- note " + i)).join("\n") + "\n" };
    const specB = { url: "https://github.com/example-owner/example-repo/blob/main/B.lean#L1", title: "Demo.beta", label: "B", _fixtureText: fxB.concat(Array.from({ length: 12 }, (_, i) => "-- note " + i)).join("\n") + "\n" };
    await openSourceCompare(specA, specB, { pair: fxPair });
    assert($$(".src-pane", drawer).length === 2 && !$("#srcViewSeg").classList.contains("hidden") && drawer.querySelector('#srcViewSeg button[data-view="side"].active'), "Compare side-by-side keeps two panes and offers the line diff layouts");
    srcView.ctx = "full";
    drawer.querySelector('#srcViewSeg button[data-view="unified"]').click();
    const uRows = (k) => $$(".ld-code.unified .ld-row." + k, drawer).length;
    assert(uRows("del") === 1 && uRows("add") === 1 && uRows("mv") === 4 && uRows("eq") === 7 && drawer.querySelector(".ld-fold") && /Show 10 unchanged lines/.test(drawer.querySelector(".ld-fold").textContent),
      "unified line diff marks − + ⇄ = rows and folds the long unchanged tail");
    const tags = $$(".ld-mv-tag", drawer).map((b) => b.textContent);
    assert(tags.includes("⇄ moved to line 2") && tags.includes("⇄ moved from line 6") && $$(".ld-w", drawer).length >= 2, "moved lines name their counterpart line; modified lines highlight changed words");
    const toTag = $$(".ld-mv-tag", drawer).find((b) => b.textContent === "⇄ moved to line 2");
    toTag.click();
    assert(drawer.querySelector('.ld-row[data-b="2"]').classList.contains("flash"), "clicking a moved tag jumps to its counterpart");
    drawer.querySelector(".ld-fold").click();
    assert(!drawer.querySelector(".ld-fold") && uRows("eq") === 17, "Show unchanged lines expands the fold");
    $("#srcNextHunk").click();
    const s1 = $("#srcStatus").textContent;
    drawer.querySelector(".src-close").focus();
    drawer.dispatchEvent(new KeyboardEvent("keydown", { key: "n", bubbles: true, cancelable: true }));
    const s2 = $("#srcStatus").textContent;
    assert(/^Change 1 of \d+$/.test(s1) && /^Change 2 of \d+$/.test(s2) && srcView.ldHunks.length >= 2, "Next change and the n key step through hunks");
    $("#srcHideSame").click();
    $("#srcIgnoreWs").click();
    assert(pdiffState.ignoreWs && !pdiffState.hideSame && uRows("eq") === 17 && !drawer.querySelector(".ld-fold"), "whitespace and unchanged-line options re-render the diff");
    $("#srcIgnoreWs").click();
    $("#srcHideSame").click();
    drawer.querySelector('#srcViewSeg button[data-view="split"]').click();
    const modRow = $$(".ld-srow", drawer).find((r) => r.querySelector(".ld-cell.del") && r.querySelector(".ld-cell.add"));
    assert(modRow && /gone/.test(modRow.textContent) && /fresh/.test(modRow.textContent) && $$(".ld-cell.mv", drawer).length === 4, "split line diff pairs the modified line across columns");
    $("#srcSwapBtn").click();
    assert($$(".ld-cell.mv", drawer).length === 4 && /fresh/.test((drawer.querySelector(".ld-cell.del") || {}).textContent || ""), "swap flips the line diff");
    drawer.querySelector('#srcTabs button[data-tab="lemmas"]').click();
    assert(drawer.querySelector(".pdiff-panel") && $("#srcCtxSeg").classList.contains("hidden"), "tabs switch between the line diff and the lemma diff");
    drawer.querySelector('#srcTabs button[data-tab="source"]').click();
    assert(drawer.querySelector(".ld-code.split"), "returning to Lean source keeps the chosen layout");
    esc();
    srcView.ctx = savedCtx;

    // 4. One side outside the pinned repository: explain, link docs, keep the lemma diff.
    await openSourceCompare(specA, { url: "", title: "Mathlib.foo", label: "B", fallbackUrl: pdiffDocsUrl("Mathlib.foo"), fallbackLabel: "Mathlib docs ↗" }, { pair: fxPair, view: "unified" });
    const un = drawer.querySelector(".ld-unavail");
    assert(un && /Side B/.test(un.textContent) && un.querySelector('a[href^="https://leanprover-community.github.io/mathlib4_docs/"]') && drawer.querySelector(".ld-fallback .pdiff-panel .pd-row"),
      "line diff explains a missing side, links its docs and keeps the lemma diff beside it");
    esc();

    // 5. Real pair cards on the Edge map.
    const m = state.manifest || {};
    const a = m.assets || {};
    if (a.atlas) {
      const aliens = (await fetchJson(a.atlas)).alien_twins || {};
      const pool = atlasTwinPool(aliens);
      const withDiff = pool.filter((x) => x.p.proof_diff).length;
      await renderAtlasView("");
      const cards = $$("#twinsGridHost .twin-card");
      const bars = $$("#twinsGridHost .twin-card .pdiff-bar");
      const btns = $$("#twinsGridHost .twin-card .pdiff-open");
      assert(cards.length > 0 && bars.length === withDiff && btns.length === withDiff && bars[0].querySelectorAll(".pdb-chip").length === 4,
        "pair cards show the − + ⇄ = bar and a View diff button (" + bars.length + " of " + cards.length + ")");
      if (btns.length) {
        const before = state.loadedFiles.size;
        btns[0].click();
        await tick(0);
        assert(!drawer.hidden && drawer.querySelector(".pdiff-panel") && $$(".pd-row", drawer).length + $$(".pd-shared-btn", drawer).length > 0 && state.loadedFiles.size === before,
          "View diff on a real pair opens the lemma diff without loading anything");
        esc();
        const chipBtn = bars[0].querySelector('button.pdb-chip[data-k="added"]');
        chipBtn.click();
        await tick(0);
        assert(!drawer.hidden && pdiffState.filter === "added" && drawer.querySelector('.pd-chip[data-k="added"].active'), "clicking a bar count opens the diff filtered to that kind");
        esc();
      }
      // #item Compare / Twins tab lists every pool, oriented on this declaration.
      const probe = pool.find((x) => x.p.proof_diff && x.p.thm_b.origin === "project");
      if (probe) {
        const name = probe.p.thm_b.name;
        const expect = pool.filter((x) => x.p.thm_a.name === name || x.p.thm_b.name === name).length;
        state.route = { tab: "item", sub: name, arg: "" };
        state.item.name = name;
        state.item.view = "twins";
        await renderItemView(name);
        const host = $(".item-twins");
        const subs = host ? $$(".map-sub", host).map((s) => s.textContent) : [];
        const rows = host ? $$(".tray-row", host).filter((r) => r.querySelector(".pdiff-bar")) : [];
        assert(subs.includes("Paired proofs of the same statement") && !subs.includes("Same statement, different proof") && rows.length === expect,
          "Compare / Twins lists paired proofs from every pool with a diff bar (" + rows.length + ")");
        const vb = host && host.querySelector(".pdiff-open");
        if (vb) {
          vb.click();
          await tick(0);
          assert(!drawer.hidden && srcView.specs[0].title === name && (drawer.querySelector(".pd-side .pd-side-name") || {}).title === name, "the item page diff puts this declaration on side A");
          esc();
        }
        state.item.view = "summary";
      }
    }

    // 6. Light theme: the four kinds stay distinct.
    const prevTheme = state.theme;
    applyTheme("light", false);
    await openProofDiff(fxPair, { specs: [{ url: "", title: "Demo.alpha" }, { url: "", title: "Demo.beta" }] });
    const gc = (sel, prop) => { const n = drawer.querySelector(sel); return n ? getComputedStyle(n)[prop] : ""; };
    const cols = [".pd-row.del .pd-g", ".pd-row.add .pd-g", ".pd-row.mv .pd-g"].map((s) => gc(s, "color"));
    const bg = (getComputedStyle(drawer).backgroundColor.match(/\d+/g) || [0]).map(Number);
    assert(new Set(cols).size === 3 && cols.every(Boolean) && bg[0] > 200 && bg[1] > 200,
      "light theme keeps removed, added and moved visually distinct");
    assert(document.documentElement.scrollWidth <= window.innerWidth + 1, "diff drawer adds no horizontal page overflow");
    esc();
    applyTheme(prevTheme, false);
    Object.assign(pdiffState, saved);
  }

  // ==========================================================================
  // VIEW 7: PORTABILITY ISLANDS (`portability_gems.json`)
  // ==========================================================================
  function computePortabilityIslands(doc) {
    const targets = Array.isArray(doc.targets) ? doc.targets : [];
    const ov = doc.overlap || {};
    const mat = ov.project_decls_matrix;
    const n = targets.length;
    const hasMat = Array.isArray(mat) && mat.length === n;
    const visited = new Set();
    const islands = [];
    for (let i = 0; i < n; i++) {
      if (visited.has(i)) continue;
      const comp = [];
      const q = [i];
      visited.add(i);
      while (q.length) {
        const u = q.shift();
        comp.push(u);
        if (hasMat) {
          for (let v = 0; v < n; v++) {
            if (!visited.has(v) && v !== u && Number(mat[u][v]) > 0) {
              visited.add(v);
              q.push(v);
            }
          }
        }
      }
      comp.sort((a, b) => ((targets[b].cone && targets[b].cone.project_decls) || 0) - ((targets[a].cone && targets[a].cone.project_decls) || 0));
      const lead = targets[comp[0]];
      const slug = shortName(lead.name);
      islands.push({
        slug,
        indices: comp,
        targets: comp.map((idx) => targets[idx]),
        maxProj: Math.max(...comp.map((idx) => (targets[idx].cone && targets[idx].cone.project_decls) || 0)),
        tier: (lead.contamination && lead.contamination.tier) || "scoped"
      });
    }
    return islands;
  }

  async function renderPortabilityView() {
    const main = $("#appMain");
    clearEl(main);
    const assetPath = state.manifest && state.manifest.assets && state.manifest.assets.portability;
    if (!assetPath) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No island data" }),
        el("p", { textContent: "This build does not include the portability analysis." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })]));
    try {
      const doc = await fetchJson(assetPath);
      renderPortabilityBody(doc);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Could not load the islands" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  function renderPortabilityBody(doc) {
    const main = $("#appMain");
    clearEl(main);
    const targets = Array.isArray(doc.targets) ? doc.targets : [];
    const islands = computePortabilityIslands(doc);
    const ov = doc.overlap || {};
    const us = ov.union_summary || {};

    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Islands" }),
      trustBadge("tool"),
      el("p", { className: "page-lede", textContent: plural(targets.length, "classical result") + ", grouped by the project code they rely on. The " + plural(islands.length, "group") + " share no project declarations with one another, so each could be lifted out on its own; together they use " + fmtInt(us.union_project_decls || 0) + " project declarations." })
    ]));

    // Tier of a group: one tier, or "mixed" when its results disagree.
    const tierOf = (tg) => (tg.contamination && tg.contamination.tier) || "scoped";
    function islandTierPill(isl) {
      const tiers = Array.from(new Set(isl.targets.map(tierOf)));
      if (tiers.length <= 1) return el("span", { className: "pill " + statusPillClass(tiers[0] || isl.tier), textContent: tiers[0] || isl.tier });
      const counts = tiers.map((tr) => isl.targets.filter((tg) => tierOf(tg) === tr).length + " " + tr).join(", ");
      return el("span", { className: "pill amber", title: "Results in this group have different tiers: " + counts, textContent: "mixed" });
    }
    // Project declarations the group uses together. Exact for one or two
    // results; for larger groups it is exact when every other group is
    // exact, since groups share nothing and the total union is known.
    const tNamesAll = ov.target_names || targets.map((tg) => tg.name);
    const pMatAll = ov.project_decls_matrix;
    const pairUnion = (isl) => {
      if (!Array.isArray(pMatAll)) return null;
      const ix = isl.targets.map((tg) => tNamesAll.indexOf(tg.name));
      if (ix.some((i) => i < 0 || !pMatAll[i])) return null;
      if (ix.length === 1) return Number(pMatAll[ix[0]][ix[0]]) || null;
      if (ix.length === 2) return Number(pMatAll[ix[0]][ix[0]]) + Number(pMatAll[ix[1]][ix[1]]) - Number(pMatAll[ix[0]][ix[1]]);
      return null;
    };
    const unionOf = new Map(islands.map((isl) => [isl, pairUnion(isl)]));
    const unknown = islands.filter((isl) => unionOf.get(isl) == null);
    if (unknown.length === 1 && Number(us.union_project_decls) > 0) {
      const rest = islands.filter((isl) => isl !== unknown[0]).reduce((s, isl) => s + unionOf.get(isl), 0);
      const u = Number(us.union_project_decls) - rest;
      if (u >= unknown[0].maxProj) unionOf.set(unknown[0], u);
    }
    function islandSizeText(isl) {
      const u = unionOf.get(isl);
      if (isl.targets.length === 1) return plural(isl.maxProj, "project declaration");
      return u != null ? fmtInt(u) + " project declarations together (largest result " + fmtInt(isl.maxProj) + ")" : "up to " + plural(isl.maxProj, "project declaration") + " per result";
    }

    // Island cards toggle in place; only the results table below changes.
    const cards = islands.map((isl) => el("button", {
      type: "button",
      className: "island-card",
      "data-island": isl.slug,
      onclick: () => {
        state.portability.island = state.portability.island === isl.slug ? "" : isl.slug;
        update();
      }
    }, [
      el("div", { className: "ic-top" }, [
        el("span", { className: "ic-name", title: isl.slug }, [identWbr(isl.slug)]),
        islandTierPill(isl)
      ]),
      el("div", { className: "ic-sub", textContent: plural(isl.targets.length, "result") + " · " + islandSizeText(isl) }),
      el("div", { className: "ic-members" }, isl.targets.flatMap((t, i) => (i ? [" · "] : []).concat([el("span", { title: t.name }, [identWbr(shortName(t.name))])])))
    ]));
    // Pick a column count that leaves no empty slots in the last row.
    const nIsl = cards.length;
    const islCols = nIsl <= 4 ? nIsl : ([4, 3, 2].find((k) => nIsl % k === 0) || 0);
    main.appendChild(el("div", { className: "island-grid", "data-cols": islCols ? String(islCols) : null }, cards));
    main.appendChild(el("p", { className: "quiet-note island-tier-legend", id: "islandTierLegend" }, [
      el("b", { textContent: "Tiers: " }),
      "standalone-ready means standard axioms only, no sorry and a small statement footprint in the project; scoped means equally sound, but the statement pulls in a large project record, three or more project folders, or 500+ project declarations; coupled means non-standard axioms, sorry, opaque project declarations or a very large cross-part cone; mixed means the results in a group differ."
    ]));

    const titleEl = el("h2");
    const clearBtn = filterClearButton(() => { state.portability.island = ""; update(); });
    main.appendChild(el("div", { className: "section-hdr" }, [titleEl, clearBtn]));

    const prefsOf = (t) => ((t.boundary && t.boundary.top_external_prefixes) || []).slice(0, 4).map((p) => p.prefix + " (" + p.distinct_decls + ")").join(", ");
    const numOr = (v) => { const n = Number(v); return v != null && Number.isFinite(n) ? n : null; };
    const cols = [
      { key: "name", label: "Result", get: (t) => shortName(t.name) },
      { key: "tier", label: "Tier", get: (t) => (t.contamination || {}).tier || null },
      { key: "project", label: "Project deps", num: true, get: (t) => numOr((t.cone || {}).project_decls) },
      { key: "spec", label: "Statement deps", num: true, get: (t) => numOr((t.cone || {}).spec_cone_project_decls) },
      { key: "mathlib", label: "Main Mathlib dependencies", get: (t) => prefsOf(t) || null },
      { key: "diagram", label: "Diagram", sortable: false }
    ];
    const sort = tableSort("islands", { key: "", dir: "desc" });
    const tbody = el("tbody");
    main.appendChild(el("div", { className: "table-wrap", style: { marginBottom: "18px" } }, [
      el("table", { className: "data-table", id: "islandTable" }, [sortableHead(cols, sort, () => update()), tbody])
    ]));

    function update() {
      const activeIsland = islands.find((i) => i.slug === state.portability.island);
      if (!activeIsland) state.portability.island = "";
      cards.forEach((c) => {
        const on = c.getAttribute("data-island") === state.portability.island;
        c.classList.toggle("active", on);
        c.setAttribute("aria-pressed", on ? "true" : "false");
      });
      titleEl.textContent = activeIsland ? ("Island: " + activeIsland.slug) : "All results";
      clearBtn.hidden = !activeIsland;
      const shownTargets = sortRowsBy(activeIsland ? activeIsland.targets : targets, cols, sort);
      clearEl(tbody);
      shownTargets.forEach((t) => {
        const cone = t.cone || {};
        const cont = t.contamination || {};
        const prefs = prefsOf(t);
        const cir = findAnyCircuitForSymbol(t.name);
        tbody.appendChild(el("tr", null, [
          el("td", null, [
            el("code", null, [identWbr(t.name)]),
            t.module ? el("div", { className: "cir-ins-note mono" }, [identWbr(t.module)]) : null
          ]),
          el("td", null, [el("span", { className: "pill " + statusPillClass(cont.tier), textContent: cont.tier || "—" })]),
          el("td", { className: "num", textContent: cone.project_decls != null ? fmtInt(cone.project_decls) : "—" }),
          el("td", { className: "num", textContent: cone.spec_cone_project_decls != null ? fmtInt(cone.spec_cone_project_decls) : "—" }),
          el("td", { className: "mono", style: { fontSize: "11px" }, textContent: prefs || "—" }),
          el("td", null, [
            cir ? el("button", {
              type: "button", className: "btn sm", textContent: "Diagram ›",
              onclick: () => navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name))
            }) : el("span", { className: "cir-ins-note", textContent: "—" })
          ])
        ]));
      });
    }
    update();

    // Pairwise Overlap Matrix
    const pMat = ov.project_decls_matrix;
    const jMat = ov.project_jaccard_matrix;
    const tNames = ov.target_names || targets.map((t) => t.name);
    if (Array.isArray(pMat) && pMat.length) {
      main.appendChild(el("div", { className: "section-hdr" }, [
        el("h2", { textContent: "Overlap between results" }),
        el("span", { className: "sub", textContent: "Shared project declarations, with the Jaccard index underneath" })
      ]));
      const tbl = el("table", { className: "overlap-table" }, [
        el("thead", null, [el("tr", null, [
          el("th", { textContent: "Target" }),
          ...tNames.map((nm) => el("th", { className: "col-h", title: nm }, [el("span", { className: "col-h-txt", textContent: shortName(nm) })]))
        ])]),
        el("tbody", null, pMat.map((row, r) => el("tr", null, [
          el("th", { title: tNames[r] }, [el("span", { className: "row-h-txt", textContent: shortName(tNames[r]) })]),
          ...row.map((val, c) => {
            const v = Number(val) || 0;
            const jac = (jMat && jMat[r] && jMat[r][c] != null) ? Number(jMat[r][c]) : null;
            const cls = r === c ? "hm-self" : (v === 0 ? "hm-0" : (jac >= 0.7 ? "hm-hi" : (jac >= 0.2 ? "hm-mid" : "hm-lo")));
            return el("td", { className: cls }, [
              fmtInt(v),
              jac != null ? el("span", { className: "jacc", textContent: jac.toFixed(2) }) : null
            ]);
          })
        ])))
      ]);
      main.appendChild(el("div", { className: "table-wrap" }, [tbl]));
    }
  }

  // ==========================================================================
  // VIEW 8: BENCHMARKS (`xrepo_benchmark.json` + optional `trim_report.json`)
  // ==========================================================================
  async function renderBenchmarksView() {
    const main = $("#appMain");
    clearEl(main);
    const assets = (state.manifest && state.manifest.assets) || {};
    if (!assets.benchmark && !assets.trim_report) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No benchmark data" }),
        el("p", { textContent: "This build does not include benchmark results." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })]));
    try {
      const [bench, trim] = await Promise.all([
        assets.benchmark ? fetchJson(assets.benchmark).catch(() => null) : Promise.resolve(null),
        assets.trim_report ? fetchJson(assets.trim_report).catch(() => null) : Promise.resolve(null)
      ]);
      renderBenchmarksBody(bench, trim);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Could not load benchmarks" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  // A sortable table whose body re-renders in place when a header is clicked.
  function simpleSortableTable(id, cols, rows, dflt, rowFor, opts) {
    const sort = tableSort(id, dflt);
    const tbody = el("tbody");
    const fill = () => { clearEl(tbody); sortRowsBy(rows, cols, sort).forEach((r) => tbody.appendChild(rowFor(r))); };
    const table = el("table", { className: "data-table" + (opts && opts.className ? " " + opts.className : ""), id: (opts && opts.tableId) || null }, [sortableHead(cols, sort, fill), tbody]);
    fill();
    return table;
  }

  // Benchmark text uses Markdown-style `code` spans; render them through the
  // escaping inline renderer.
  function benchInline(tag, text, attrs) {
    const node = el(tag, attrs || null);
    node.innerHTML = renderInlineSafe(String(text == null ? "" : text), "benchmarks");
    return node;
  }
  // "step4_clones_and_k1n_duplicates" -> "Clones and same-statement duplicates".
  function benchStepLabel(id) {
    const t = String(id || "").replace(/^step\d+[a-z]?_/i, "").replace(/_/g, " ").replace(/\bk1n\b/g, "same-statement").replace(/\b1node\b/g, "single-node").replace(/\bdecls\b/g, "declarations").trim();
    return t ? t.charAt(0).toUpperCase() + t.slice(1) : "";
  }

  function renderBenchmarksBody(bench, trim) {
    const main = $("#appMain");
    clearEl(main);
    const numOr = (v) => { const n = Number(v); return v != null && v !== "" && Number.isFinite(n) ? n : null; };

    if (bench && Array.isArray(bench.repos)) {
      const repos = bench.repos;
      const totalMod = repos.reduce((s, r) => s + (Number(r.modules) || 0), 0);
      const totalLoc = repos.reduce((s, r) => s + (Number(r.lines_wc) || 0), 0);
      const passCnt = repos.filter((r) => r.overall_status === "PASS").length;

      const isDemoRepo = (r) => /tiny[_ -]?demo/i.test(String((r && r.repo) || ""));
      const demoRepos = repos.filter(isDemoRepo);
      const realRepos = repos.filter((r) => !isDemoRepo(r));
      main.appendChild(el("header", { className: "page-head" }, [
        el("h1", { textContent: "Benchmarks" }),
        trustBadge("tool"),
        el("p", { className: "page-lede", textContent: "The same analysis run on " + plural(realRepos.length, "benchmark Lean 4 repository", "benchmark Lean 4 repositories") + (demoRepos.length ? " (plus the synthetic tiny demo)" : "") + ", to check that it is not tuned to a single project." + (bench.leanre_commit ? " Tool version " + bench.leanre_commit + "." : "") })
      ]));

      main.appendChild(el("section", { className: "kpi-strip" }, [
        { label: "Repositories", val: fmtInt(realRepos.length), sub: fmtInt(passCnt) + " of " + fmtInt(repos.length) + " runs pass" + (demoRepos.length ? " (incl. the tiny demo)" : "") },
        { label: "Modules", val: fmtInt(totalMod), sub: plural(totalLoc, "line") }
      ].map((k) => el("div", { className: "kpi-card" }, [
        el("div", { className: "kpi-val", textContent: k.val }),
        el("div", { className: "kpi-label", textContent: k.label }),
        el("div", { className: "kpi-sub", textContent: k.sub })
      ]))));

      const STATUS_RANK = { PASS: 0, PARTIAL: 1, WARN: 1, FAIL: 2 };
      const repoCols = [
        { key: "repo", label: "Repository", get: (r) => r.repo || null },
        { key: "root", label: "Root module", get: (r) => r.hub || r.root_module || null },
        { key: "modules", label: "Modules", num: true, get: (r) => numOr(r.modules) },
        { key: "lines", label: "Lines", num: true, get: (r) => numOr(r.lines_wc) },
        { key: "decls", label: "Declarations", num: true, get: (r) => numOr((r.decls_source || {}).total) },
        { key: "sorry", label: "Sorry", num: true, get: (r) => Number((r.decls_source || {}).sorry_hits) || 0 },
        { key: "misfiled", label: "Misfiled %", num: true, get: (r) => numOr((r.flirt_tier1 || {}).misfiles_pct) },
        { key: "runtime", label: "Runtime (s)", num: true, get: (r) => numOr(r.total_runtime_s) },
        { key: "status", label: "Status", get: (r) => { const s = String(r.overall_status || "").toUpperCase(); return STATUS_RANK[s] != null ? STATUS_RANK[s] : (s ? s : null); } }
      ];
      main.appendChild(el("div", { className: "table-wrap", style: { marginBottom: "18px" } }, [
        simpleSortableTable("bench-repos", repoCols, repos, { key: "", dir: "desc" }, (r) => {
          const ds = r.decls_source || {};
          const f1 = r.flirt_tier1 || {};
          return el("tr", null, [
            el("td", null, [
              el("strong", { textContent: r.repo, style: { color: "var(--text-hi)" } }),
              el("div", { className: "cir-ins-note mono", textContent: r.lean_toolchain || "" })
            ]),
            el("td", null, [el("code", null, [identWbr(r.hub || r.root_module || "—")])]),
            el("td", { className: "num", textContent: r.modules != null ? fmtInt(r.modules) : "—" }),
            el("td", { className: "num", textContent: r.lines_wc != null ? fmtInt(r.lines_wc) : "—" }),
            el("td", { className: "num", textContent: ds.total != null ? fmtInt(ds.total) : "—" }),
            el("td", { className: "num", textContent: fmtInt(ds.sorry_hits || 0) }),
            el("td", { className: "num", textContent: f1.misfiles_pct != null ? Number(f1.misfiles_pct).toFixed(2) : "—" }),
            el("td", { className: "num", textContent: r.total_runtime_s != null ? Number(r.total_runtime_s).toFixed(2) : "—" }),
            el("td", null, [el("span", { className: "pill " + statusPillClass(r.overall_status), textContent: r.overall_status || "—" })])
          ]);
        }, { tableId: "benchReposTable" })
      ]));

      // The tool's own regression checks are a development log; the page
      // keeps one line pointing at the repository's verification notes.
      const issues = Array.isArray(bench.xrepo_issue_verification) ? bench.xrepo_issue_verification : [];
      if (issues.length) {
        const passN = issues.filter((x) => String(x.status || "").toUpperCase() === "PASS").length;
        main.appendChild(el("p", { className: "quiet-note bench-selfchecks", id: "benchSelfChecks" }, [
          "Tool self-checks: " + fmtInt(passN) + " of " + fmtInt(issues.length) + " pass. ",
          el("a", { href: "https://github.com/bohemian-miser/leanre/tree/main/verify", target: "_blank", rel: "noopener noreferrer", textContent: "Test and verification notes in the repository ↗" })
        ]));
      }
    }

    if (trim) {
      const steps = (trim.c8_waterfall && trim.c8_waterfall.steps) || trim.steps || [];
      if (steps.length) {
        const removedOf = (st) => (st.removed && (st.removed.decls || st.removed.live_decls || st.removed.modules)) || 0;
        const afterOf = (st) => (st.after && (st.after.live_decls || st.after.decls || st.after.modules)) || 0;
        const unitOf = (o) => (o && (o.decls != null || o.live_decls != null) ? "declarations" : (o && o.modules != null ? "modules" : ""));
        const units = new Set(steps.map((st) => unitOf(st.removed)).filter(Boolean));
        const unit = units.size === 1 ? Array.from(units)[0] : "";
        main.appendChild(el("div", { className: "section-hdr" }, [
          el("h2", { textContent: "Trimming unused declarations" }),
          el("span", { className: "sub", textContent: "How much of the repository each step removes, in order" })
        ]));
        main.appendChild(el("div", { className: "table-wrap" }, [
          simpleSortableTable("bench-trim", [
            { key: "order", label: "#", num: true, firstDir: "asc", get: (st) => steps.indexOf(st) + 1 },
            { key: "step", label: "Step", get: (st) => st.step_id || null },
            { key: "label", label: "Description", get: (st) => st.label || null },
            { key: "removed", label: unit ? "Removed (" + unit + ")" : "Removed", num: true, get: (st) => removedOf(st) },
            { key: "after", label: "Remaining", num: true, get: (st) => afterOf(st) }
          ], steps, { key: "order", dir: "asc" }, (st) => el("tr", null, [
            el("td", { className: "num", textContent: String(steps.indexOf(st) + 1) }),
            el("td", { title: st.step_id || null, textContent: benchStepLabel(st.step_id) || "—" }),
            benchInline("td", String(st.label || "—")
              .replace(/\bvalue_nodes\s*==\s*1\b/g, "single-node proof")
              .replace(/\bidentical-k1n duplicate\b/gi, "duplicate-signature")
              .replace(/\balpha-clone\b/gi, "exact body-clone")
              .replace(/\s*\(4[ab]\)/g, "")),
            el("td", { className: "num", textContent: fmtInt(removedOf(st)) + (!unit && unitOf(st.removed) === "modules" ? " modules" : "") }),
            el("td", { className: "num", textContent: fmtInt(afterOf(st)) })
          ]))
        ]));
      }
    }
  }

  // ==========================================================================
  // VIEW 9: SEARCH (prefix-indexed data files, `/` hotkey)
  // ==========================================================================
  function getSearchShardNames() {
    const shards = state.manifest && state.manifest.search && state.manifest.search.shards;
    if (Array.isArray(shards)) return shards;
    if (shards && typeof shards === "object") return Object.keys(shards);
    return [];
  }

  function hasSearchShard(pfx) {
    const shards = state.manifest && state.manifest.search && state.manifest.search.shards;
    if (!shards) return false;
    if (Array.isArray(shards)) return shards.includes(pfx);
    if (typeof shards === "object") return Object.prototype.hasOwnProperty.call(shards, pfx);
    return false;
  }

  function searchShardPrefixesForQuery(query) {
    const m = state.manifest;
    const sMeta = (m && m.search) || {};
    const plen = Number(sMeta.shard_prefix_len) || 2;
    const raw = String(query || "").trim();
    const out = new Set();

    const probe = (token) => {
      const alnum = String(token || "").toLowerCase().replace(/[^a-z0-9]/g, "");
      if (!alnum) {
        if (hasSearchShard("_")) out.add("_");
        return;
      }
      // Longest-prefix check (supports optional 3-char sub-sharding + standard 2-char)
      for (let len = Math.min(3, alnum.length); len >= plen; len--) {
        const cand = alnum.slice(0, len);
        if (hasSearchShard(cand)) {
          out.add(cand);
          return;
        }
      }
      if (alnum.length < plen && hasSearchShard("_")) out.add("_");
    };

    // Primary: leaf_prefix2 (leaf = part after final '.')
    const leaf = raw.includes(".") ? raw.slice(raw.lastIndexOf(".") + 1) : raw;
    probe(leaf);
    // Secondary: if user typed a qualified name, also probe full string in case exporter used full-name buckets
    if (raw.includes(".")) probe(raw);
    return Array.from(out);
  }

  function resolveModuleName(rawMod, shardModPrefixes) {
    if (rawMod == null) return "";
    const dict = (Array.isArray(shardModPrefixes) && shardModPrefixes.length)
      ? shardModPrefixes
      : ((state.manifest && state.manifest.search && Array.isArray(state.manifest.search.mod_prefixes)) ? state.manifest.search.mod_prefixes : null);
    if (typeof rawMod === "number" && dict && dict[rawMod] != null) return String(dict[rawMod]);
    if (Array.isArray(rawMod) && rawMod.length >= 2 && dict && dict[rawMod[0]] != null) {
      return String(dict[rawMod[0]]) + (rawMod[1] ? "." + String(rawMod[1]) : "");
    }
    const s = String(rawMod);
    if (dict) {
      const m = s.match(/^(\d+):(.*)$/);
      if (m && dict[Number(m[1])] != null) {
        return String(dict[Number(m[1])]) + (m[2] ? "." + m[2] : "");
      }
    }
    return s;
  }

  async function loadSearchShard(prefix) {
    const sMeta = state.manifest && state.manifest.search;
    if (!sMeta || !sMeta.shard_template || !prefix || !hasSearchShard(prefix)) return { rows: [], modPrefixes: null };
    if (state.searchShards.has(prefix)) return state.searchShards.get(prefix);
    const path = String(sMeta.shard_template).replace("{prefix}", prefix);
    try {
      const data = await fetchJson(path);
      const rows = Array.isArray(data) ? data : (Array.isArray(data.entries) ? data.entries : []);
      const modPrefixes = (!Array.isArray(data) && Array.isArray(data.mod_prefixes)) ? data.mod_prefixes : null;
      const packed = { rows, modPrefixes };
      state.searchShards.set(prefix, packed);
      return packed;
    } catch (_) {
      const empty = { rows: [], modPrefixes: null };
      state.searchShards.set(prefix, empty);
      return empty;
    }
  }

  function normalizeSearchEntry(row, modPrefixes) {
    if (Array.isArray(row)) {
      return {
        name: String(row[0] || ""),
        kind: String(row[1] || "decl"),
        dom: Number(row[2] || 0),
        live: row[3] == null ? 1 : Number(row[3]),
        mod: resolveModuleName(row[4], modPrefixes),
        line: row[5] != null ? Number(row[5]) : null,
        circuitPath: row[6] || null,
        bpId: row[7] || null
      };
    }
    return {
      name: String(row.name || ""),
      kind: String(row.kind || "decl"),
      dom: Number(row.dom || 0),
      live: row.live == null ? 1 : Number(row.live),
      mod: resolveModuleName(row.mod != null ? row.mod : (row.mod_id != null ? row.mod_id : row.module), modPrefixes),
      line: row.line != null ? Number(row.line) : null,
      circuitPath: row.circuit_path || null,
      bpId: row.bp_id || null
    };
  }

  function localManifestMatches(qLower) {
    const m = state.manifest || {};
    const out = [];
    for (const f of (m.findings || [])) {
      if (((f.slug || "") + " " + (f.title || "") + " " + (f.summary || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "finding", name: plainTextFromTex(f.title || f.slug), sub: "findings/" + f.slug + ".md", route: "#findings/" + encodeURIComponent(f.slug) });
      }
    }
    for (const d of (m.dossiers || [])) {
      if (((d.slug || "") + " " + (d.title || "") + " " + (d.category || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "dossier", name: plainTextFromTex(d.title || d.slug), sub: "analysis/" + d.slug + ".md", route: "#dossiers/" + encodeURIComponent(d.slug) });
      }
    }
    for (const b of (m.blueprints || [])) {
      if (((b.id || "") + " " + (b.title || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "blueprint", name: b.title || b.id, sub: fmtInt(b.node_count) + " nodes", route: "#blueprints/" + encodeURIComponent(b.id) });
      }
    }
    const cir = m.circuits || {};
    for (const cb of (cir.bundles || [])) {
      if (((cb.name || "") + " " + (cb.short || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "circuit", name: cb.name, sub: "Structure diagram" + (cb.badge ? " · " + cb.badge : ""), route: "#circuit/bundle/" + encodeURIComponent(cb.short || cb.name) });
      }
    }
    for (const ct of (cir.theorems || [])) {
      if (((ct.name || "") + " " + (ct.short || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "circuit", name: ct.name, sub: "Theorem diagram", route: "#circuit/theorem/" + encodeURIComponent(ct.short || ct.name) });
      }
    }
    return out;
  }

  const SEARCH_TYPE_LABEL = { circuit: "diagram", finding: "finding", dossier: "dossier", blueprint: "blueprint" };

  let searchDebounce = null;
  let searchHashT = null;
  // Keep the typed query in the address bar (without adding history entries).
  function syncSearchHash() {
    if (state.selftestRunning || !state.route || state.route.tab !== "search") return;
    const q = (state.search.q || "").trim();
    const target = q ? "#search/" + encodeURIComponent(q) : "#search";
    if (window.location.hash === target) return;
    try { window.history.replaceState(null, "", target); } catch (_) { /* ignore */ }
  }

  // Arrow keys move through results; Enter opens the highlighted one.
  function moveSearchSelection(step) {
    const rows = $$("#searchResultsBox .search-result-row");
    if (!rows.length) return null;
    const cur = rows.findIndex((r) => r.classList.contains("kb-active"));
    const next = cur < 0 ? (step > 0 ? 0 : rows.length - 1) : Math.max(0, Math.min(rows.length - 1, cur + step));
    rows.forEach((r, i) => {
      r.classList.toggle("kb-active", i === next);
      if (i === next) r.setAttribute("aria-current", "true"); else r.removeAttribute("aria-current");
    });
    const row = rows[next];
    if (row.scrollIntoView) row.scrollIntoView({ block: "nearest" });
    const name = row.querySelector(".sr-name");
    announce("Result " + (next + 1) + " of " + rows.length + ": " + (name ? name.textContent : ""));
    return row;
  }

  function openSearchSelection() {
    const row = $("#searchResultsBox .search-result-row.kb-active") || $("#searchResultsBox .search-result-row");
    const link = row && row.querySelector(".sr-acts a[href^='#']");
    if (link) { link.click(); return true; }
    return false;
  }

  function renderSearchView(initialQ) {
    const main = $("#appMain");
    clearEl(main);
    if (initialQ) state.search.q = initialQ;

    const sMeta = (state.manifest && state.manifest.search) || {};
    const inputEl = el("input", {
      type: "search",
      id: "globalSearchInput",
      className: "input search-big-input",
      placeholder: "Search declarations, findings and dossiers…",
      "aria-label": "Search",
      "aria-describedby": "searchKbHint",
      value: state.search.q,
      autocomplete: "off",
      spellcheck: "false",
      oninput: (ev) => {
        state.search.q = ev.target.value;
        clearTimeout(searchDebounce);
        searchDebounce = setTimeout(runSearchQuery, 120);
        clearTimeout(searchHashT);
        searchHashT = setTimeout(syncSearchHash, 250);
      },
      onkeydown: (ev) => {
        if (ev.key === "ArrowDown" || ev.key === "ArrowUp") {
          ev.preventDefault();
          moveSearchSelection(ev.key === "ArrowDown" ? 1 : -1);
        } else if (ev.key === "Enter" && !ev.isComposing) {
          clearTimeout(searchDebounce);
          if (openSearchSelection()) ev.preventDefault();
        }
      }
    });

    const scopeSeg = el("div", { className: "seg", style: { marginTop: "10px" } }, [
      ["all", "All"], ["decl", "Declarations"], ["circuit", "Diagrams"], ["doc", "Findings & dossiers"], ["blueprint", "Blueprints"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.search.scope === k ? "active" : "", textContent: lbl,
      onclick: () => { state.search.scope = k; renderSearchView(); }
    })));

    main.appendChild(el("section", { className: "search-hero" }, [
      el("h1", { textContent: "Search" }),
      trustBadge("tool"),
      el("p", { className: "page-lede", textContent: (sMeta.total_entries
        ? "Searching " + fmtInt(sMeta.total_entries) + " indexed declarations" + (((state.manifest || {}).stats || {}).total_decls > sMeta.total_entries ? " (of " + fmtInt(state.manifest.stats.total_decls) + " in total)" : "")
        : "Searching declarations") + ", plus findings, dossiers, blueprints and diagrams." }),
      xrefsBaseUrl() ? el("p", { className: "search-xrefs-link" }, [el("a", { href: "#xrefs", textContent: "Search all " + fmtInt(((state.manifest || {}).stats || {}).total_decls || 0) + " declaration names in Cross-refs ›" })]) : null,
      inputEl,
      el("p", { className: "search-kb-hint", id: "searchKbHint", textContent: "↑ ↓ to move through results, Enter to open, Esc to go back." }),
      scopeSeg
    ]));

    main.appendChild(el("div", { id: "searchResultsBox" }));
    setTimeout(() => { if (document.activeElement !== inputEl) { inputEl.focus(); if (inputEl.value) inputEl.select(); } }, 20);
    syncSearchHash();
    runSearchQuery();
  }

  async function runSearchQuery() {
    const box = $("#searchResultsBox");
    if (!box) return;
    const rawQ = (state.search.q || "").trim();
    const ql = rawQ.toLowerCase();
    clearEl(box);

    if (ql.length < 2) {
      box.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Type at least two characters" }),
        el("p", { textContent: "Search matches declaration names and modules, as well as findings, dossiers, blueprints and diagrams." })
      ]));
      return;
    }

    const localHits = localManifestMatches(ql);
    const shardPrefixes = searchShardPrefixesForQuery(rawQ);

    const shardResults = await Promise.all(shardPrefixes.map((p) => loadSearchShard(p)));
    const seen = new Set();
    const declHits = [];
    for (const packed of shardResults) {
      for (const raw of (packed.rows || [])) {
        const e = normalizeSearchEntry(raw, packed.modPrefixes);
        if (seen.has(e.name)) continue;
        const nl = e.name.toLowerCase();
        const sl = shortName(e.name).toLowerCase();
        if (nl.includes(ql) || sl.includes(ql) || e.mod.toLowerCase().includes(ql)) {
          seen.add(e.name);
          declHits.push(e);
        }
      }
    }
    // Rank exact/prefix matches first, then dom descending
    declHits.sort((a, b) => {
      const as = shortName(a.name).toLowerCase();
      const bs = shortName(b.name).toLowerCase();
      const ap = as === ql ? 0 : (as.startsWith(ql) ? 1 : 2);
      const bp = bs === ql ? 0 : (bs.startsWith(ql) ? 1 : 2);
      return (ap - bp) || (b.dom - a.dom) || a.name.localeCompare(b.name);
    });

    const scope = state.search.scope;
    const showLocal = localHits.filter((h) => {
      if (scope === "all") return true;
      if (scope === "doc") return h.type === "finding" || h.type === "dossier";
      return h.type === scope;
    });
    const showDecls = (scope === "all" || scope === "decl") ? declHits.slice(0, 80) : [];

    if (!showLocal.length && !showDecls.length) {
      box.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No matches for \"" + rawQ + "\"" }),
        el("p", { textContent: "Try a shorter part of the name, or a different spelling." })
      ]));
      return;
    }

    const panel = el("div", { className: "panel search-results", style: { padding: "0" } });
    for (const h of showLocal.slice(0, 40)) {
      panel.appendChild(el("div", { className: "search-result-row" }, [
        el("div", { className: "sr-main" }, [
          el("div", { className: "sr-name", textContent: h.name }),
          el("div", { className: "sr-meta" }, [
            el("span", { className: "sr-type", textContent: SEARCH_TYPE_LABEL[h.type] || h.type }),
            el("span", { textContent: h.sub })
          ])
        ]),
        el("div", { className: "sr-acts" }, [
          el("a", { className: "btn sm", href: h.route, textContent: "Open ›" })
        ])
      ]));
    }

    for (const d of showDecls) {
      const cir = findAnyCircuitForSymbol(d.name, d.circuitPath);
      const ghUrl = d.mod ? buildGithubUrl(d.mod, d.line) : null;
      const acts = el("div", { className: "sr-acts" });
      acts.appendChild(el("a", { className: "btn sm primary", href: "#item/" + encodeURIComponent(d.name), textContent: "Inspect ›" }));
      if (ghUrl && d.line) {
        const peek = makeSrcButton(ghUrl, d.name);
        if (peek) acts.appendChild(peek);
      }
      if (cir) {
        acts.appendChild(el("a", { className: "btn sm", href: circuitHref(cir), textContent: "Diagram ›" }));
      }
      if (d.bpId) {
        acts.appendChild(el("a", { className: "btn sm", href: "#blueprints/" + encodeURIComponent(d.bpId), textContent: "Blueprint ›" }));
      }
      if (ghUrl) {
        acts.appendChild(el("a", { className: "btn sm", href: ghUrl, target: "_blank", rel: "noopener noreferrer", textContent: "Proof file ↗" }));
      }
      panel.appendChild(el("div", { className: "search-result-row" }, [
        el("div", { className: "sr-main" }, [
          el("div", { className: "sr-name", textContent: d.name }),
          el("div", { className: "sr-meta" }, [
            el("span", { className: "sr-type", textContent: d.kind + (d.live ? "" : " · unreachable") }),
            d.dom > 0 ? el("span", { title: "Declarations reachable only through this one (dominator subtree)", textContent: fmtInt(d.dom) + " in subtree" }) : null,
            d.mod ? el("span", { textContent: d.mod + (d.line ? ":" + d.line : "") }) : null
          ])
        ]),
        acts
      ]));
    }
    box.appendChild(panel);
  }

  function xrefsBaseUrl() {
    const p = state.manifest && state.manifest.assets && state.manifest.assets.xrefs;
    if (!p) return "";
    const dir = String(p).replace(/[^/]+$/, "");
    const rel = projectRelPath(dir || "data/xrefs/");
    return rel.endsWith("/") ? rel : rel + "/";
  }

  async function renderXrefsView(initialName, initialCompare) {
    const main = $("#appMain");
    const m = state.manifest || {};
    const baseUrl = xrefsBaseUrl();
    if (!baseUrl || !window.LeanreXrefs) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No cross-reference index" }),
        el("p", { textContent: "This project build does not include a precomputed cross-reference index." })
      ]));
      return;
    }
    let host = $("#xrefsHost");
    if (!host || host.parentNode !== main) {
      clearEl(main);
      host = el("div", { id: "xrefsHost", className: "xrefs-page" });
      main.appendChild(host);
    }
    const outline = state.outline || {};
    const landmarks = (outline.spine || []).slice(0, 6).map((s) => s.name).filter(Boolean);
    await window.LeanreXrefs.renderExplorer(host, {
      baseUrl,
      initialName: initialName || "",
      initialCompare: initialCompare || "",
      repoUrl: m.repo_url || "",
      pinnedCommit: m.pinned_commit || "",
      srcPrefix: m.src_prefix || "",
      landmarks: landmarks.length ? landmarks : undefined,
      buildGithubUrl,
      onNavigateXref: (n, cmp) => {
        const tail = n ? "/" + encodeURIComponent(n) : "";
        const qs = cmp ? "?cmp=" + encodeURIComponent(cmp) : "";
        const h = "#xrefs" + tail + qs;
        try { window.history.replaceState(null, "", h); } catch (_) { window.location.hash = h; }
        state.route = parseHash();
        updateCrumbs(state.route);
      },
      onNavigateItem: (n) => navigate("#item/" + encodeURIComponent(n)),
      onPeekSource: (mod, line, title) => {
        const url = buildGithubUrl(mod, line);
        if (url) openSourcePeek({ url, title: title || mod, line });
      }
    });
  }

  // ==========================================================================
  // DISPATCH & SELF-TEST RUNNER
  // ==========================================================================
  // Dismissible note at the top of the page for a route that fell back.
  function showRouteNotice(text) {
    const main = $("#appMain");
    if (!main) return;
    const old = $("#routeNotice");
    if (old) old.remove();
    const note = el("div", { className: "route-notice", id: "routeNotice", role: "status" }, [
      el("span", { textContent: text }),
      el("button", { type: "button", className: "icon-btn", "aria-label": "Dismiss", title: "Dismiss", textContent: "×", onclick: () => note.remove() })
    ]);
    main.insertBefore(note, main.firstChild);
  }

  async function handleRoute(ev) {
    const keepScroll = Boolean(ev && ev.keepScroll);
    const r = parseHash();
    updateNavHighlight(r.tab);
    closeProjectMenu();
    if (!state.manifest) {
      if (state.registry && state.booted) {
        state.route = r;
        updateCrumbs(r);
        await renderProjectsHome();
        chromeAfterRoute(r);
      }
      return;
    }
    state.route = r;
    closeSourceDrawer();
    fsState.themeStale = false; // this render already uses the current theme
    exitFullscreen();
    if (state.rail.mobileOpen) { state.rail.mobileOpen = false; applyRailVisibility(); }
    updateCrumbs(r);
    renderRail();
    document.body.classList.toggle("route-projects", r.tab === "projects");
    if (!keepScroll) window.scrollTo(0, 0);

    switch (r.tab) {
      case "overview": renderOverview(); break;
      case "circuit": await renderCircuitView(r.sub, r.arg); break;
      case "findings": await renderFindingsView(r.sub); break;
      case "dossiers": await renderDossiersView(r.sub, r.arg); break;
      case "blueprints": await renderBlueprintsView(r.sub); break;
      case "flirt": await renderFlirtView(); break;
      case "atlas": await renderAtlasView(r.sub); break;
      case "xrefs": await renderXrefsView([r.sub, r.arg].filter(Boolean).join("/"), r.cmp); break;
      case "portability": await renderPortabilityView(); break;
      case "benchmarks": await renderBenchmarksView(); break;
      case "search": renderSearchView(r.sub); break;
      case "item": await renderItemView([r.sub, r.arg].filter(Boolean).join("/")); break;
      case "projects": await renderProjectsHome(); break;
      case "experiments": await renderExperimentsView(); break;
      default: renderOverview(); break;
    }
    if (r.unknownTab) showRouteNotice("There is no page called “" + r.unknownTab + "”, so this is the overview.");
    else if (state.missingProject) showRouteNotice("No proof called “" + state.missingProject + "” is in this gallery, so this shows " + ((state.manifest && (state.manifest.title || state.manifest.repo_name)) || "the default proof") + ".");
    state.missingProject = "";
    chromeAfterRoute(r);

    if (r.selftest && !state.selftestRunning) {
      state.selftestRunning = true;
      await runSiteSelfTest();
    }
  }

  const FORBIDDEN_WORDING = /RH is proved|RH is proven|proves RH\b|RH has been proved|Riemann Hypothesis is proved/i;
  // Implementation vocabulary that must never leak into visible UI copy.
  const UI_SLOP_WORDING = /zero-cdn|lazy[- ]?fetch|lazy static|lazy-loaded|\bshards?\b|pre-rendered|leanre\.site|epistemic scope|genome atlas|hi-c|alien-proof|\bflirt\b|brainstorm|two-arm|personas|youtuber|guardrail|scratch telemetry|cli friction|tromp binder|licence|neighbour|colour|labelled|behaviour|analyse|\bcentre\b/i;

  // Visible chrome + view text, excluding authored Markdown bodies and data rows.
  function visibleUiText() {
    const parts = [document.title];
    const hdr = $(".topbar");
    if (hdr) parts.push(hdr.innerText || hdr.textContent || "");
    const ftr = $(".site-footer");
    if (ftr) parts.push(ftr.innerText || ftr.textContent || "");
    const main = $("#appMain");
    if (main) {
      const clone = main.cloneNode(true);
      clone.querySelectorAll(".md-body, .data-table tbody, .search-results, .twin-side-name, .twin-side-meta, .cir-chips-wrap, .doc-list, .dom-tree, .showcase-chips, .findings-cards, .island-grid, .bp-head, .bp-inspector, .overlap-table, .cir-inspector, .atlas-readout, .quiet-note, .tray-row, .map2d-detail, .item-head, .nb-strip, .item-body, .proj-card-tag, .proj-card h3, .exp-list, .lens-box, .lx-tbl tbody, .lx-list, .lx-suggest, .lx-ego, .lx-trail, .lx-name, .lx-full, .lx-mod, select").forEach((n) => n.remove());
      parts.push(clone.textContent || "");
      $$("input[placeholder]", main).forEach((i) => parts.push(i.getAttribute("placeholder") || ""));
    }
    return parts.join("\n");
  }

  // v2.4 clusters/benchmarks/dossiers self-test (owned by the docs pass).
  async function runV24DocsSelfTest(assert) {
    const m = state.manifest || {};
    const assets = m.assets || {};
    const savedUrl = window.location.href;
    const slopFree = (label) => {
      const hit = visibleUiText().match(UI_SLOP_WORDING);
      assert(!hit, "no implementation jargon on " + label + " (v2.4)" + (hit ? " (" + hit[0] + ")" : ""));
    };

    // Markdown: evidence tags get one shared tooltip map; spelling and "≠" polish.
    const md = el("div");
    md.innerHTML = renderMarkdownBlockSafe("> **Scope:** kernel acceptance != refereeing [K], `[L]`, `x != y`.\n\nThe Catalogue was realised.", "findings");
    polishDocText(md);
    const tags = Array.from(md.querySelectorAll("abbr.ev-tag"));
    assert(tags.length === 2 && tags.every((a) => a.getAttribute("title") === EV_TAG_MEANING[a.textContent.charAt(1)]) && Object.keys(EV_TAG_MEANING).join("") === "KLSM",
      "evidence tags [K]/[L]/[S]/[M] render as <abbr> with tooltips from one map");
    const quote = (md.querySelector("blockquote") || {}).textContent || "";
    assert(/acceptance ≠ refereeing/.test(quote) && md.querySelector("code").textContent === "x != y" && /The Catalog was realized\./.test(md.textContent),
      "documents show ≠ and US spelling in prose; code stays as written");
    assert(inferDossierCategory({ slug: "dom1000_x" }) === "Subtrees ≥ 1,000 declarations" && inferDossierCategory({ category: "dom >= 1,000 closures" }) === "Subtrees ≥ 1,000 declarations",
      "dossier group names read in plain words");
    const tb = trustBadge("tool").title + " " + trustBadge("notes").title;
    assert(!m.source_only || !/kernel/i.test(tb), "trust badge tooltips do not mention a kernel export on source-only pages");
    assert(clusterToken("pillar_theta") === "Part A (Theta)" && clusterToken("cross domain misplaced") === "Unexpected folder" && clusterToken("isolated_ns_outlier") === "Namespace mismatch" &&
      clusterToken("algebra_rings_poly+padic_local_fields") === "Algebra & rings + p-adic local fields" && clusterIdLabel("BP007") === "Cluster 7",
      "cluster tokens read as words");

    // Clusters (kernel build): badge, column names, readable IDs, separated identifiers.
    if (assets.cluster_labels) {
      state.flirt.q = ""; state.flirt.status = "all"; state.flirt.severity = "all"; state.flirt.page = 0;
      await renderFlirtView();
      const badge = $("#appMain .page-head .trust-badge");
      const heads = $$("#flirtTable thead th").map((th) => th.textContent).join("|");
      assert(badge && badge.textContent === "Clusters computed by leanre · topic labels heuristic", "Clusters badge says what is computed and what is heuristic");
      assert(/Inferred topic/.test(heads) && !/blind/i.test(heads + ($(".page-lede") || {}).textContent), "Clusters uses \"Inferred topic\" wording");
      const idCells = $$("#flirtTbody tr td:first-child .fl-id");
      assert(idCells.length && idCells.every((c) => /^Cluster \d+$/.test(c.textContent) && c.title), "cluster IDs read as \"Cluster N\" with the original ID as a tooltip");
      const rowsText = $$("#flirtTbody tr td:nth-child(4) .pill").map((p) => p.textContent).join(" ");
      assert(!/_/.test(rowsText), "cluster match pills read as words");
      const multi = $$("#flirtTbody .fl-reps").find((r) => r.children.length > 1);
      let apart = true;
      if (multi) {
        const a = multi.children[0].getBoundingClientRect();
        const b = multi.children[1].getBoundingClientRect();
        apart = getComputedStyle(multi).display === "flex" && (b.left >= a.right + 4 || b.top >= a.bottom - 1);
      }
      assert(apart, "identifier names in a Clusters folder cell never run together");
      slopFree("clusters");
    } else if (assets.flirt_tier1) {
      await renderFlirtView();
      const sig = $$("#tier1MisfileTable tbody td:nth-child(3), #tier1MisfileTable tbody td:nth-child(4)").map((td) => td.textContent).join(" ");
      assert(!/_/.test(sig), "misfile topics and signals read as words");
      slopFree("clusters (source scan)");
    }

    // Benchmarks: inline code, collapsed self-checks, readable step names.
    if (assets.benchmark || assets.trim_report) {
      await renderBenchmarksView();
      const det = $("#benchSelfChecks");
      if (det) {
        assert(/^Tool self-checks: \d+ of \d+ pass\./.test(det.textContent) && !det.querySelector("table") && det.querySelector("a[href*='github.com']"), "tool self-check log is one line linking the repository's verification notes");
      }
      assert(!/\btiny[_ ]demo\b.*other Lean 4/i.test(($(".page-lede") || {}).textContent || ""), "benchmark count leaves out the synthetic tiny demo");
      const benchText = $$("#appMain .data-table tbody").map((t) => t.textContent).join(" ");
      assert(!/`/.test(benchText), "Benchmarks shows inline code spans, not raw backticks");
      const stepCells = $$("#appMain .data-table tbody tr td:nth-child(2)").filter((td) => td.title && /^step\d/.test(td.title));
      assert(stepCells.every((td) => !/^step\d|_|\bk1n\b|\b1node\b/.test(td.textContent)), "trim steps read as words with the step ID as a tooltip");
      slopFree("benchmarks");
    }

    // Islands: no orphan slots, badges flush right.
    if (assets.portability) {
      state.portability.island = "";
      await renderPortabilityView();
      const grid = $("#appMain .island-grid");
      const cards = $$("#appMain .island-card");
      const cols = Number(grid && grid.getAttribute("data-cols")) || 0;
      assert(grid && (!cols || cards.length % cols === 0), "island grid leaves no empty slots in its last row");
      const flush = cards.every((c) => {
        const top = c.querySelector(".ic-top").getBoundingClientRect();
        const pill = c.querySelector(".ic-top .pill").getBoundingClientRect();
        return Math.abs(top.right - pill.right) <= 2;
      });
      assert(flush, "island badges are right-aligned");
    }

    // Dossiers: plain group names; no duplicate "Review notes" label by the badge.
    const dossiers = m.dossiers || [];
    if (dossiers.length) {
      const rn = dossiers.find((d) => /^review notes?$/i.test(inferDossierCategory(d)));
      const dom = dossiers.find((d) => /^Subtrees ≥/.test(inferDossierCategory(d)));
      await renderDossiersView((rn || dom || dossiers[0]).slug);
      const opts = $$("#dossierCatSel option").map((o) => o.textContent).join("|");
      assert(!/>=|closures/.test(opts + $$(".doc-cat-hdr").map((h) => h.textContent).join("|")), "dossier group names avoid shorthand like \"dom >=\"");
      const meta = ($(".doc-article-meta") || {}).textContent || "";
      assert(!rn || !/Review notes?Review note/i.test(meta.replace(/\s+/g, "")), "dossier meta row does not repeat \"Review notes\" next to the badge");
      const body = $("#dossierMdBody");
      const prose = body ? Array.from(body.querySelectorAll("p, li, blockquote, td, h1, h2, h3")).filter((n) => !n.closest("pre")).map((n) => {
        const c = n.cloneNode(true); c.querySelectorAll("code").forEach((x) => x.remove()); return c.textContent;
      }).join(" ") : "";
      assert(!/\bCatalogue\b|\brealised\b|\s!=\s/.test(prose), "dossier prose uses US spelling and ≠");
      slopFree("dossiers");
    }
    try { window.history.replaceState(null, "", savedUrl); } catch (_) { /* ignore */ }
  }

  // v2.3 tables/inputs/documents self-test (owned by the tables pass).
  async function runV23TablesSelfTest(assert) {
    const m = state.manifest || {};
    const assets = m.assets || {};
    const tick = () => new Promise((r) => setTimeout(r, 0));
    const savedUrl = window.location.href;
    const typeInto = (inp, text) => {
      inp.focus();
      inp.value = text;
      inp.setSelectionRange(text.length, text.length);
      inp.dispatchEvent(new Event("input", { bubbles: true }));
    };
    const keepsFocus = (sel, text) => {
      const inp = $(sel);
      if (!inp) return false;
      typeInto(inp, text);
      return document.activeElement === inp && inp.isConnected && $(sel) === inp && inp.value === text;
    };
    const keyOn = (node, key) => node.dispatchEvent(new KeyboardEvent("keydown", { key, bubbles: true }));

    // Sorting helper: blank values sort last in both directions.
    const cols = [{ key: "v", label: "V", num: true }];
    const rows = [{ v: 3 }, { v: null }, { v: "—" }, { v: 1 }, { v: 2 }];
    const asc = sortRowsBy(rows, cols, { key: "v", dir: "asc" }).map((r) => r.v);
    const desc = sortRowsBy(rows, cols, { key: "v", dir: "desc" }).map((r) => r.v);
    assert(asc.slice(0, 3).join(",") === "1,2,3" && desc.slice(0, 3).join(",") === "3,2,1" && isBlankSortValue(asc[3]) && isBlankSortValue(desc[4]),
      "shared table sort keeps blank values last in both directions");
    const sortState = { key: "", dir: "desc" };
    let sorted = 0;
    const head = sortableHead([{ key: "a", label: "A" }, { key: "b", label: "B", num: true }, { key: "c", label: "C", sortable: false }], sortState, () => { sorted++; });
    const thB = head.querySelector('th[data-sort-key="b"]');
    const idle = head.querySelector('th[data-sort-key="a"] .sort-ind');
    thB.click();
    const first = thB.getAttribute("aria-sort");
    keyOn(thB, "Enter");
    const second = thB.getAttribute("aria-sort");
    keyOn(thB, " ");
    assert(first === "descending" && second === "ascending" && thB.getAttribute("aria-sort") === "descending" && sorted === 3 &&
      thB.getAttribute("tabindex") === "0" && idle.textContent === "⇅" && thB.querySelector(".sort-ind").textContent === "▼" &&
      !head.querySelectorAll("th")[2].hasAttribute("tabindex"),
      "sortable headers toggle ▲/▼ with click, Enter and Space and set aria-sort");

    // Markdown headings get ids; in-document links stay inside the article.
    const md = el("div", { className: "md-body" });
    md.innerHTML = renderMarkdownBlockSafe("# Intro\n\n## Same name\n\ntext\n\n## Same name\n\n> ### Quoted `code` head\n\nSee [jump](#same-name), [quoted](#quoted-code-head) and [route](#item/Foo.bar).", "findings");
    const ids = Array.from(md.querySelectorAll("h1, h2, h3")).map((h) => h.id).join(",");
    const jump = md.querySelector('a[data-doc-anchor="same-name"]');
    const route = Array.from(md.querySelectorAll("a")).find((a) => a.textContent === "route");
    assert(ids === "h-intro,h-same-name,h-same-name-1,h-quoted-code-head" && jump && route && !route.hasAttribute("data-doc-anchor") && route.getAttribute("href") === "#item/Foo.bar",
      "Markdown headings get unique h-<slug> ids and app links stay routes");
    const rw = rewriteDocHref("other_note.md#Some-Section", "findings");
    assert(rw && rw.href === "#findings/other_note?sec=some-section", "links to another document keep their section");
    document.body.appendChild(md);
    const hashBefore = window.location.hash;
    wireDocAnchors(md, "#findings/selftest-doc");
    jump.click();
    await tick();
    assert(jump.getAttribute("href") === "#findings/selftest-doc?sec=same-name" && !/^#same-name/.test(window.location.hash) && window.location.hash !== "#overview" &&
      (window.location.hash === hashBefore || window.location.hash === "#findings/selftest-doc?sec=same-name"),
      "in-document links scroll within the article instead of changing page");
    md.remove();
    try { window.history.replaceState(null, "", savedUrl); } catch (_) { /* ignore */ }

    // Clusters: the filter input stays mounted while typing; headers sort.
    if (assets.cluster_labels) {
      state.flirt.q = ""; state.flirt.status = "all"; state.flirt.severity = "all"; state.flirt.page = 0;
      await renderFlirtView();
      const before = $$("#flirtTbody tr").length;
      assert(keepsFocus("#flirtSearchInput", "a") && keepsFocus("#flirtSearchInput", "zzqx_no_match"), "typing in the Clusters filter keeps focus, cursor and the same input");
      const countTxt = ($("#flirtCount") || {}).textContent || "";
      const clr = $("#appMain .toolbar-row .filter-clear");
      assert(/^Showing 0 of /.test(countTxt) && clr && !clr.hidden, "Clusters shows a filtered count and a Clear button");
      clr.click();
      assert(state.flirt.q === "" && $("#flirtSearchInput").value === "" && $$("#flirtTbody tr").length === before && clr.hidden, "Clear resets the Clusters filters in place");
      const th = $('#flirtTable th[data-sort-key="live_decls"]');
      th.click();
      const nums = $$("#flirtTbody tr td.num > div:first-child").map((d) => Number(d.textContent.replace(/[^\d]/g, "")));
      assert(th.getAttribute("aria-sort") === "descending" && nums.every((v, i) => i === 0 || nums[i - 1] >= v) && $$("#flirtTable th.sortable").length === 5,
        "Clusters table sorts by every column");
      checkSlopSafe("clusters v2.3");
    } else if (assets.flirt_tier1) {
      await renderFlirtView();
      assert($$("#appMain .data-table th.sortable").length >= 1, "source-only Clusters tables have sortable headers");
    }

    // Blueprints: the filter input stays mounted; row clicks update the inspector in place.
    if ((m.blueprints || []).length) {
      state.bpQ = ""; state.bpStatus = "all"; state.bpPage = 0;
      await renderBlueprintsView("");
      const inp = $("#bpNodeSearch");
      assert(keepsFocus("#bpNodeSearch", "e") && keepsFocus("#bpNodeSearch", ""), "typing in the Blueprints filter keeps focus and the same input");
      const th = $('.bp-table th[data-sort-key="dom"]');
      const dir0 = th && th.getAttribute("aria-sort");
      if (th) th.click();
      assert(th && th.getAttribute("aria-sort") && th.getAttribute("aria-sort") !== dir0 && $$(".bp-table th[aria-sort]").length === 1, "Blueprints headers flip sort direction with aria-sort");
      const rowsNow = $$(".bp-table tbody tr.clickable");
      if (rowsNow.length > 1) {
        rowsNow[1].click();
        assert(rowsNow[1].classList.contains("selected") && rowsNow[1].isConnected && !rowsNow[0].classList.contains("selected") && $("#bpNodeSearch") === inp,
          "selecting a Blueprints row updates the inspector without rebuilding the table");
      }
      state.bpSort = { key: "dom", dir: "desc" };
    }

    // Findings: filter box, Prev/Next, sidebar scroll kept between chapters.
    const fl = m.findings || [];
    if (fl.length) {
      await renderFindingsView(fl[fl.length - 1].slug);
      const list = $("#findingListEl");
      assert(fl.length < 2 || !!$(".doc-article-wrap .doc-prevnext a.doc-pn.prev"), "findings end with Previous / Next links");
      if (fl.length > 6) assert(keepsFocus("#findingSearchInput", "a") && keepsFocus("#findingSearchInput", ""), "Findings has a filter box that keeps focus");
      if (list && list.scrollHeight > list.clientHeight + 20 && fl.length > 2) {
        list.scrollTop = list.scrollHeight;
        const top0 = list.scrollTop;
        await renderFindingsView(fl[fl.length - 2].slug);
        const list2 = $("#findingListEl");
        assert(list2 !== list && list2.scrollTop > 0 && Math.abs(list2.scrollTop - top0) < list2.clientHeight, "the findings list keeps its scroll position when switching chapters");
      }
      const body = $("#findingMdBody");
      const hs = body ? body.querySelectorAll("h1, h2, h3, h4") : [];
      assert(Array.from(hs).every((h) => /^h-/.test(h.id)), "rendered findings headings carry anchor ids");
      state.findingQ = "";
    }

    // Dossiers: Clear button and Prev/Next.
    const ds = m.dossiers || [];
    if (ds.length) {
      state.dossierQ = ""; state.dossierCat = "all"; state.dossierMode = "analysis";
      await renderDossiersView(ds[0].slug, "");
      assert(keepsFocus("#dossierSearchInput", "zzqx_no_match"), "typing in the Dossiers filter keeps focus");
      const meta = $(".doc-sidebar .doc-filter-meta");
      const clr = meta && meta.querySelector(".filter-clear");
      assert(meta && !meta.hidden && /^Showing 0 of/.test(meta.textContent) && clr && !clr.hidden, "Dossiers shows a filtered count and a Clear button");
      clr.click();
      assert(state.dossierQ === "" && $$("#dossierListEl .doc-item").length >= 1 && meta.hidden, "Clear resets the Dossiers filter");
      assert(ds.length < 2 || !!$(".doc-article-wrap .doc-prevnext a.doc-pn.next"), "dossiers end with Previous / Next links");
    }

    // Islands and Benchmarks: every table sorts.
    if (assets.portability) {
      state.portability.island = "";
      await renderPortabilityView();
      const th = $('#islandTable th[data-sort-key="project"]');
      const n0 = $$("#islandTable tbody tr").length;
      if (th) th.click();
      const card = $(".island-card");
      if (card) card.click();
      assert(th && th.getAttribute("aria-sort") === "descending" && (!card || (card.isConnected && card.classList.contains("active") && $$("#islandTable tbody tr").length <= n0)),
        "Islands table sorts and island cards filter it in place");
      if (card) card.click();
    }
    if (assets.benchmark || assets.trim_report) {
      await renderBenchmarksView();
      const tables = $$("#appMain .data-table");
      const allSortable = tables.length > 0 && tables.every((t) => t.querySelectorAll("th.sortable").length > 0);
      const th = $('#benchReposTable th[data-sort-key="sorry"]');
      if (th) th.click();
      assert(allSortable && (!th || th.getAttribute("aria-sort") === "descending"), "every Benchmarks table has sortable headers");
    }

    // Comparison table on the projects page: keyboard sort and the current proof highlighted.
    if (state.registry && state.registry.comparison) {
      await renderProjectsHome();
      for (let i = 0; i < 60 && !$(".cmp-table tbody tr"); i++) await new Promise((r) => setTimeout(r, 50));
      const th = $('.cmp-table th[data-sort-key="decls"]');
      if (th) { th.focus(); keyOn(th, "Enter"); }
      const cur = state.manifest ? currentProjectSlug() : "";
      const curRow = $(".cmp-table tr.cmp-current");
      assert(th && th.getAttribute("aria-sort") === "descending" && document.activeElement === th && (!cur || !$$(".cmp-table tbody tr").some((tr) => tr.querySelector("a")) || !!curRow || !projectList().some((p) => p.slug === cur)),
        "comparison table sorts from the keyboard and marks the current proof");
    }

    state.tableSorts = {};
    try { window.history.replaceState(null, "", savedUrl); } catch (_) { /* ignore */ }

    function checkSlopSafe(label) {
      const txt = visibleUiText();
      const hit = txt.match(UI_SLOP_WORDING);
      assert(!hit, "no implementation jargon on " + label + (hit ? " (" + hit[0] + ")" : ""));
    }
  }

  async function runSourceViewerSelfTest(assert) {
    const blob = "https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L12-L14";
    const p = githubBlobToRaw(blob);
    assert(p && p.raw === "https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean" && p.line === 12 && p.lineEnd === 14,
      "githubBlobToRaw converts pinned blob URLs with line ranges");
    const bad = [
      "https://evil.example/leanprover-community/x/blob/main/a.lean",
      "http://github.com/a/b/blob/main/a.lean",
      "https://github.com.evil.example/a/b/blob/main/a.lean",
      "https://github.com/a/b/blob/main/../../x.lean",
      "https://github.com/a/b/blob/main/%2e%2e/x.lean",
      "https://github.com/a/b/tree/main/a.lean",
      "https://user@github.com/a/b/blob/main/a.lean",
      "javascript:alert(1)//github.com/a/b/blob/main/a.lean",
      "https://github.com/a/b/blob/main/a.lean?raw=1"
    ];
    assert(bad.every((u) => githubBlobToRaw(u) === null), "githubBlobToRaw rejects non-GitHub, traversal and malformed URLs");

    const st = { depth: 0, expectName: false };
    const toks = tokenizeLeanLine("theorem foo (h : x = 1) : True := by simp -- note", st);
    const clsOf = (txt) => (toks.find((t) => t[1] === txt) || [])[0];
    assert(clsOf("theorem") === "tok-kw" && clsOf("foo") === "tok-name" && clsOf("by") === "tok-tac" && clsOf("simp") === "tok-tac" && clsOf("1") === "tok-num" && clsOf("-- note") === "tok-com",
      "Lean tokenizer classifies keywords, names, tactics, numbers and comments");
    const st2 = { depth: 0, expectName: false };
    tokenizeLeanLine("/- open /- nested -/ still", st2);
    const t2 = tokenizeLeanLine("comment -/ def bar := \"s\" sorry", st2);
    assert(st2.depth === 0 && t2[0][0] === "tok-com" && t2.some((t) => t[0] === "tok-str") && t2.some((t) => t[0] === "tok-sorry"),
      "Lean tokenizer tracks nested block comments, strings and sorry across lines");

    const fixture = [
      "import Mathlib",
      "",
      "/-- A doc comment with <img src=x onerror=alert(1)> inside. -/",
      "theorem demo_target (n : Nat) : n + 0 = n := by",
      "  simp",
      "",
      "def <script>alert(2)</script> := 0"
    ].join("\n");
    const ok = await openSourcePeek({ url: "https://github.com/example-owner/example-repo/blob/0123456789abcdef0123456789abcdef01234567/Demo/Basic.lean#L4", title: "demo_target", _fixtureText: fixture });
    const drawer = $("#srcDrawer");
    const hl = drawer && drawer.querySelector(".src-line.hl");
    assert(ok && drawer && !drawer.hidden && hl && hl.dataset.line === "4" && !!drawer.querySelector(".src-line .tok-kw"),
      "source viewer renders a fixture with the target line highlighted");
    assert(drawer && !drawer.querySelector("img, script, [onerror]") && /onerror=alert/.test(drawer.textContent || ""),
      "source viewer renders file text as inert text (no HTML injection)");
    const gh = $("#srcGhBtn");
    assert(gh && gh.getAttribute("href") === "https://github.com/example-owner/example-repo/blob/0123456789abcdef0123456789abcdef01234567/Demo/Basic.lean#L4",
      "source viewer links to the pinned GitHub line");
    srcView.ctx = "full";
    rerenderSourcePanes();
    assert(drawer.querySelectorAll(".src-line").length === 7, "full-file context shows every line");
    srcView.ctx = "15";
    closeSourceDrawer();
    assert(drawer.hidden, "source viewer closes cleanly");

    await openSourceCompare(
      { url: "https://github.com/example-owner/example-repo/blob/main/A.lean#L1", title: "A", label: "A", _fixtureText: "theorem a : True := trivial" },
      { url: "", title: "Mathlib.foo", label: "B", fallbackUrl: "https://leanprover-community.github.io/mathlib4_docs/find/?pattern=foo#doc", fallbackLabel: "Mathlib docs ↗" }
    );
    assert(drawer.querySelectorAll(".src-pane").length === 2 && !!drawer.querySelector('.src-pane[data-pane="1"] .src-error') && !!drawer.querySelector('.src-pane[data-pane="0"] .src-line'),
      "side-by-side viewer renders one pane and a graceful error card for the other");
    closeSourceDrawer();

    const md = el("div");
    md.innerHTML = renderMarkdownBlockSafe("See [Main.lean:12](" + blob + ") and [docs](https://example.org/x).", "findings");
    const n = decorateLeanLinks(md);
    assert(n === 1 && md.querySelectorAll(".src-peek-btn").length === 1, "Markdown .lean links gain exactly one inline preview button");
  }

  async function runSiteSelfTest() {
    const checks = [];
    const assert = (cond, msg) => { checks.push({ ok: Boolean(cond), msg }); };

    // Record any request that leaves this origin while the self-test runs.
    const externalRequests = [];
    const origFetch = window.fetch;
    window.fetch = function (input, init) {
      try {
        const u = new URL(typeof input === "string" ? input : (input && input.url) || "", window.location.href);
        if (u.origin !== window.location.origin) externalRequests.push(u.href);
      } catch (_) { /* ignore */ }
      return origFetch.apply(this, arguments);
    };
    const slopHits = [];
    const checkSlop = (label) => {
      const txt = visibleUiText();
      const mm = txt.match(UI_SLOP_WORDING);
      if (mm) slopHits.push(label + ": \"" + mm[0] + "\"");
    };

    try {
    // 1. Manifest & initial load invariant
    const m = state.manifest;
    assert(m && m.schema === "leanre.site_manifest/1", "manifest schema is leanre.site_manifest/1");
    assert(state.loadedFiles.size <= 3, "initial load fetches at most 3 files (got " + state.loadedFiles.size + ")");
    assert(!$("#netBadge") && !$("#tab-search"), "header has no transfer badge and no duplicate search tab");

    // 2. XSS sanitizer checks (Markdown & SVG)
    const xssMd = renderMarkdownBlockSafe('<img src=x onerror=alert(1)> [bad](javascript:alert(1)) <script>alert(2)</script>', "findings");
    const mdDiv = el("div");
    mdDiv.innerHTML = xssMd;
    assert(
      !mdDiv.querySelector("script, img, [onerror], a"),
      "markdown renderer blocks raw HTML, onerror, and javascript: links"
    );
    const vDiv = el("div");
    vDiv.innerHTML = renderMarkdownBlockSafe("<details>\n<summary>Verify locally &amp; pinned anchors</summary>\n\n```bash\npython3 -c \"import sqlite3\"\n```\n\n- keep this anchor\n</details>", "findings", "findings/example.md");
    assert(!/sqlite3|python3/.test(vDiv.textContent) && /keep this anchor/.test(vDiv.textContent) && Array.from(vDiv.querySelectorAll("a")).some((a) => a.getAttribute("href") === verifyLocallyHref("findings/example.md") && /^https:\/\/github\.com\/bohemian-miser\/leanre[/#]/.test(a.getAttribute("href"))) && /Verify locally & pinned/.test(vDiv.querySelector("summary").textContent),
      "\"Verify locally\" blocks hide local commands behind a link to the repository");
    const tmpDiv = el("div");
    mountSafeSvg(tmpDiv, '<svg xmlns="http://www.w3.org/2000/svg" width="100" height="40"><script>window.__xss=1</script><rect onclick="alert(1)" width="20" height="20"/></svg>');
    assert(!tmpDiv.querySelector("script") && !tmpDiv.querySelector("[onclick]"), "SVG DOMParser sanitizer strips <script> and on* handlers");

    // 3. Overview check
    renderOverview();
    const ovTxt = $("#appMain").textContent || "";
    assert(ovTxt.length > 60 && !/\[object Object\]/.test(ovTxt) && !FORBIDDEN_WORDING.test(ovTxt), "overview renders cleanly without [object Object] or forbidden wording");
    assert(!!$(".hero h1") && $$(".hero h1").length === 1 && !!$(".hero-note"), "overview hero has one title and a quiet scope note");
    checkSlop("overview");

    // 4. Diagrams (macro + dark/light + structure/theorem if present)
    if (m.circuits && m.circuits.macro) {
      updateNavHighlight("circuit");
      assert($$("#mainNav .nav-tab.active").length === 1 && !!$("#tab-circuit.active"), "exactly one nav tab is highlighted on Diagrams");
      await renderCircuitView("macro", "");
      assert(!!$("#cirStage svg"), "repository diagram mounts sanitized SVG");
      checkSlop("diagrams");
      applyTheme("light", true);
      assert(document.documentElement.getAttribute("data-theme") === "light", "light theme toggle works");
      applyTheme("dark", true);
      if (m.circuits.bundles && m.circuits.bundles.length) {
        await renderCircuitView("bundle", m.circuits.bundles[0].short || m.circuits.bundles[0].name);
        assert(!!$("#cirStage svg"), "structure diagram renders SVG");
      }
      if (m.circuits.theorems && m.circuits.theorems.length) {
        await renderCircuitView("theorem", m.circuits.theorems[0].short || m.circuits.theorems[0].name);
        assert(!!$("#cirStage svg"), "theorem diagram renders SVG");
      }
      updateNavHighlight("overview");
    }

    // 5. Remaining views (gracefully handle empty or populated)
    await renderFindingsView("");
    assert(($("#appMain").textContent || "").length > 20, "findings view renders");
    checkSlop("findings");
    await renderDossiersView("", "");
    assert(($("#appMain").textContent || "").length > 20, "dossiers view renders");
    checkSlop("dossiers");
    await renderBlueprintsView("");
    assert(($("#appMain").textContent || "").length > 20, "blueprints view renders");
    checkSlop("blueprints");
    await renderFlirtView();
    assert(($("#appMain").textContent || "").length > 20, "clusters view renders");
    checkSlop("clusters");
    if (m.assets && m.assets.atlas) {
      await renderAtlasView();
      const atlasTxt = $("#appMain").textContent || "";
      assert(!!$("#hicCanvas") && !!$("#syntenyCanvas") && !/\[object Object\]/.test(atlasTxt), "edge map renders both canvases cleanly");
      checkSlop("edge map");
    } else {
      const aTab = $("#tab-atlas");
      assert(!aTab || aTab.classList.contains("hidden") || !!(m.assets && (m.assets.module_matrix || m.assets.embedding_2d)), "edge map tab hides cleanly when its data is absent");
    }
    await renderPortabilityView();
    assert(($("#appMain").textContent || "").length > 20, "islands view renders");
    checkSlop("islands");
    await renderBenchmarksView();
    assert(($("#appMain").textContent || "").length > 20, "benchmarks view renders");
    checkSlop("benchmarks");

    // 6. Search index test
    const shardNames = getSearchShardNames();
    const firstShard = shardNames.find((s) => s !== "_" && s.length >= 2) || shardNames[0] || "ma";
    renderSearchView(firstShard);
    await runSearchQuery();
    assert(!!$("#globalSearchInput"), "search view renders and runs a query");
    checkSlop("search");

    // 7. Projects, outline rail, breadcrumbs, lenses, inspector, experiments
    const reg = parseRegistry({ schema: "leanre.projects_registry/1", projects: [
      { slug: "good-one", path: "p/good-one", title: "Good" },
      { slug: "bad", path: "p/../../etc" },
      { slug: "../evil", path: "p/x" },
      { slug: "root-one", path: "." }
    ] });
    assert(reg && reg.projects.length === 2 && reg.projects[0]._base === "p/good-one/" && reg.projects[1]._base === "",
      "projects registry parser keeps safe entries and rejects traversal");
    if (state.registry) {
      await renderProjectsHome();
      assert($$(".proj-card").length >= 1 && !!$(".add-proof"), "projects home lists proofs and explains how to add one");
      if (state.registry.comparison) {
        for (let i = 0; i < 40 && !$(".cmp-table"); i++) await new Promise((r) => setTimeout(r, 50));
        const th = $(".cmp-table th.sortable:nth-child(2)");
        if (th) th.click();
        assert($$(".cmp-table tbody tr").length >= 1 && $(".cmp-table th[aria-sort]"), "projects home shows a sortable comparison table");
      }
      checkSlop("projects");
      assert(!!$("#projBtn") && !$("#projMenu").querySelector("script"), "project switcher is present");
    }
    renderRail();
    const railModesNow = railModes();
    if (railModesNow.length) {
      assert(!$("#outlineRail").hidden && $$("#outlineRail .rail-row").length > 0, "outline rail lists the proof spine");
    }
    updateCrumbs({ tab: "findings", sub: (m.findings && m.findings[0] && m.findings[0].slug) || "" });
    assert($$("#crumbBar .crumb").length >= 2 || !(m.findings || []).length, "breadcrumb bar shows the path to the current page");
    const linkFrag = renderLeanTokens(tokenizeLeanLine("exact foo_bar h", { depth: 0, expectName: false }), new Map([["foo_bar", "Ns.foo_bar"]]));
    const linkHost = el("div", null, [linkFrag]);
    const symA = linkHost.querySelector("a.src-sym");
    assert(symA && symA.getAttribute("href") === "#item/Ns.foo_bar" && linkHost.querySelectorAll("a").length === 1, "source viewer links only verified symbol names");

    const lenses = overviewLenses();
    renderOverview();
    if (lenses.some(([k]) => k === "diagram")) {
      state.overviewLens = "diagram";
      await renderOverviewLens($("#lensBody"), el("div"));
      assert(!!$("#lensBody .lens-box svg"), "overview diagram lens mounts the repository map");
      state.overviewLens = "spine";
    }

    const probeName = (((state.outline && state.outline.spine) || [])[0] || {}).name
      || ((m.overview_pillars || []).find((p) => p.decl) || {}).decl
      || ((m.circuits && m.circuits.theorems && m.circuits.theorems[0]) || {}).name || "";
    if (probeName) {
      state.route = { tab: "item", sub: probeName, arg: "" };
      state.item.view = "summary";
      await renderItemView(probeName);
      assert(!!$(".item-title") && ($(".item-title").textContent || "").length > 0 && !!$(".item-tabs"), "declaration inspector renders for " + shortName(probeName));
      checkSlop("item");
    }

    if (m.assets && m.assets.atlas) {
      await renderAtlasView("");
      const cv = $("#hicCanvas");
      if (cv) {
        const rc = cv.getBoundingClientRect();
        cv.dispatchEvent(new MouseEvent("click", { bubbles: true, clientX: rc.left + rc.width * 0.3, clientY: rc.top + rc.height * 0.3 }));
        assert(!$("#hicTray").hidden && $$("#hicTray .tray-row").length > 0, "clicking the contact map opens a tray of declarations and edges");
      }
    } else if (m.assets && m.assets.module_matrix) {
      await renderAtlasView("");
      assert(!!$("#moduleMatrixCanvas"), "source-only projects show the module matrix");
    }
    if (m.assets && m.assets.embedding_2d) {
      if (!$("#map2dSection")) await renderAtlasView("map");
      let canvas = null;
      for (let i = 0; i < 60 && !canvas; i++) { canvas = $("#map2dSection .map2d-canvas"); if (!canvas) await new Promise((r) => setTimeout(r, 50)); }
      assert(!!canvas, "2D map renders");
      if (canvas) {
        const rc = canvas.getBoundingClientRect();
        let hit = false;
        for (let gy = 0.1; gy < 0.95 && !hit; gy += 0.05) {
          for (let gx = 0.1; gx < 0.95 && !hit; gx += 0.05) {
            const pe = { bubbles: true, clientX: rc.left + rc.width * gx, clientY: rc.top + rc.height * gy, button: 0, pointerId: 7 };
            canvas.dispatchEvent(new PointerEvent("pointerdown", pe));
            canvas.dispatchEvent(new PointerEvent("pointerup", pe));
            hit = !!$("#map2dSection .map2d-detail .cir-ins-title");
          }
        }
        assert(hit, "clicking a 2D map dot shows its details and neighbors");
      }
    }
    renderExperimentsView();
    assert(!$("#tab-experiments") && !!$("#appMain .empty-card a[href='#atlas']"), "old experiments route shows a short pointer instead of the study");
    const hiddenActive = $$("#mainNav .nav-tab.active.hidden").length;
    assert(hiddenActive === 0, "no hidden tab is highlighted");

    // 7b. Math typography, 2D map controls, light canvases, favicon
    assert(plainTextFromTex("$\\operatorname{Re}(s) > 1/2$ except at $s=1$") === "Re(s) > 1/2 except at s=1" && plainTextFromTex("costs $5 and $10") === "costs $5 and $10" && plainTextFromTex("$\\mathrm{Ш}^1$ over $\\mathbb{Q}$") === "Ш¹ over ℚ",
      "TeX is converted to plain text without touching prices");
    const texSpan = renderTexSafe("x^{2} + \\chi_{1}");
    assert(texSpan.querySelector("sup") && texSpan.querySelector("sub") && /χ/.test(texSpan.textContent) && !texSpan.querySelector("script"), "TeX renders to DOM with sup/sub elements");
    const mdMath = el("div");
    mdMath.innerHTML = renderMarkdownBlockSafe("Here $\\operatorname{Re}(s) > \\tfrac{1}{2}$ holds.", "findings");
    assert(/Re\(s\) > 1\/2/.test(mdMath.textContent) && !mdMath.textContent.includes("$") && mdMath.querySelector(".math-inline"), "long inline math in Markdown renders");
    const mdTex = el("div");
    mdTex.innerHTML = renderMarkdownBlockSafe([
      "1. Display math inside a list item",
      "   $$\\left|\\frac{\\Phi^{(k)}(\\sigma)}{k!}\\right| \\le \\int_0^\\infty \\overline{\\chi'}\\,\\binom{2n}{n} + \\frac ab \\cdot \\sum_{\\substack{i\\ge1\\\\ i\\notin\\Phi}} \\widehat G$$",
      "",
      "| set | note |",
      "|---|---|",
      "| $T_0 = S \\cup \\{v : |x|_v \\ne 1\\}$ | ok |",
      "",
      "$$\\begin{cases} a & \\psi=0, \\\\ b & \\psi\\ne0 \\end{cases}$$"
    ].join("\n"), "findings");
    assert(!/\$|\\[a-zA-Z]|frac|infty|overline|binom|substack|widehat|cdot/.test(mdTex.textContent) && mdTex.querySelector("li .math-display .tx-frac") && mdTex.querySelector(".tx-stack") &&
      mdTex.querySelectorAll("tbody td").length === 2 && mdTex.querySelector("tbody td .math-inline") && mdTex.querySelector(".tx-cases-t .tx-tr + .tx-tr"),
      "TeX renderer handles fractions, limits, accents, stacked subscripts, cases, and display math in lists and table cells");
    renderOverview();
    assert(!!$(".trust-line .trust-badge.tool"), "overview marks tool output with a trust badge");
    if ((m.findings || []).length) {
      await renderFindingsView("");
      assert(!!$(".doc-article-meta .trust-badge"), "findings carry a provenance badge");
    }
    if (m.circuits && m.circuits.macro) {
      await renderCircuitView("macro", "");
      assert(!!$(".circuit-shell .fs-btn") && $("#cirStageWrap").dataset.touchGestures === "1", "diagram viewer has full screen and touch gestures");
    }
    const fav = document.querySelector('link[rel="icon"]');
    assert(fav && /^data:image\/svg\+xml/.test(fav.getAttribute("href") || ""), "favicon is inline (no extra request)");
    if (m.assets && m.assets.atlas) {
      applyTheme("light", false);
      await renderAtlasView("");
      const hc = $("#hicCanvas");
      const px = hc && hc.getContext("2d").getImageData(2, 2, 1, 1).data;
      assert(px && px[0] > 200 && px[1] > 200, "contact map paints a light background in the light theme");
      applyTheme("dark", false);
      const hicCard = hc && hc.closest(".atlas-card");
      const hfs = hicCard && hicCard.querySelector(".fs-btn");
      if (hfs) {
        hfs.click();
        const on = hicCard.classList.contains("fs-on");
        document.dispatchEvent(new KeyboardEvent("keydown", { key: "Escape" }));
        await new Promise((r) => setTimeout(r, 60));
        assert(on && !hicCard.classList.contains("fs-on"), "contact map opens full screen and Esc closes it");
      }
    }
    if (m.assets && m.assets.embedding_2d) {
      const host2 = $("#map2dSection") || (await renderAtlasView("map"), $("#map2dSection"));
      for (let i = 0; i < 60 && !(host2 && host2._map2d); i++) await new Promise((r) => setTimeout(r, 50));
      const api = host2 && host2._map2d;
      if (api) {
        api.resetView();
        const target = api.pts.slice().sort((x, y) => y.dom - x.dom)[0];
        api.runFind(target.short);
        assert(api.state.sel === target.i && api.state.zoom >= 5.9, "2D map search jumps to and zooms on a declaration");
        const zoomTxt = ($("#map2dSection .map-zoom") || {}).textContent || "";
        assert(/×$/.test(zoomTxt) && parseFloat(zoomTxt) >= 5.9, "2D map shows the zoom level");
        const pill = $("#map2dSection .map-pill");
        if (pill) {
          pill.click();
          await new Promise((r) => setTimeout(r, 280));
          assert(api.state.hidden.size === 1 && $("#map2dSection .map-pill.off"), "legend pills hide a group when clicked");
          $("#map2dSection .map-pill.off").click();
          await new Promise((r) => setTimeout(r, 280));
        }
        api.resetView();
        assert(Math.abs(api.state.zoom - 1) < 0.01, "2D map reset returns to the whole map");
        assert(api.canvas.dataset.touchGestures === "1" && getComputedStyle(api.canvas).touchAction === "none", "2D map has pinch, pan and tap gestures");
        const dimsBefore = { W: api.dims.W, H: api.dims.H };
        const rectBefore = api.canvas.getBoundingClientRect();
        api.fsBtn.click();
        await new Promise((r) => setTimeout(r, 120));
        // On a phone the map already spans the width, so full screen grows it taller instead.
        const rectFs = api.canvas.getBoundingClientRect();
        const fsOn = host2.classList.contains("fs-on") && (api.dims.W !== dimsBefore.W || api.dims.H !== dimsBefore.H) &&
          (rectFs.height > rectBefore.height || Math.max(rectFs.width, rectFs.height) >= Math.max(rectBefore.width, rectBefore.height));
        api.fsBtn.click();
        await new Promise((r) => setTimeout(r, 120));
        assert(fsOn && !host2.classList.contains("fs-on") && api.dims.W === dimsBefore.W && api.dims.H === dimsBefore.H, "2D map opens and closes full screen, resizing the canvas");
        const numMode = api.modes.find((mm) => mm.type === "num");
        if (numMode && api.modes.length > 1) {
          const prevColor = api.state.color;
          api.state.color = numMode.key;
          await mountMap2d(host2);
          assert(!!host2.querySelector(".map-colorbar"), "continuous color-by shows a gradient color bar (" + numMode.label + ")");
          const chip = Array.from(host2.querySelectorAll(".map-chip")).find((b) => b.textContent !== "All");
          if (chip) { chip.click(); assert(host2._map2d.state.focusKey !== "all", "focus filters dim the other points"); host2.querySelector(".map-chip").click(); }
          api.state.color = prevColor;
          await mountMap2d(host2);
        }
        assert(/Theta & local matching|Galois/.test(($("#map2dSection .map-legend") || {}).textContent || "") || !(m.repo_name === "riemann-hypothesis"), "2D map legend uses plain part names");
      }
    }

    // 8. Live source viewer (fixture only; no network)
    await runSourceViewerSelfTest(assert);

    // 9. v2.3 passes
    await runV23AtlasSelfTest(assert);

    await runV23TablesSelfTest(assert);

    await runV23ChromeSelfTest(assert);

    await runV24AtlasSelfTest(assert);

    await runV24DocsSelfTest(assert);

    await runV24OverviewSelfTest(assert);

    await runV25DiffSelfTest(assert);

    if (m.assets && m.assets.xrefs && window.LeanreXrefs) {
      await window.LeanreXrefs.runSelfTest(assert, { baseUrl: xrefsBaseUrl() });
      await renderXrefsView("");
      assert(!!$("#xrefsHost") && ($("#xrefsHost").textContent || "").length > 20, "cross-references view renders");
      checkSlop("xrefs");
    } else if (window.LeanreXrefs) {
      await window.LeanreXrefs.runSelfTest(assert, {});
    }

    assert(slopHits.length === 0, "no implementation jargon in visible UI text" + (slopHits.length ? " (" + slopHits.join("; ") + ")" : ""));
    assert(externalRequests.length === 0, "no external network requests during self-test" + (externalRequests.length ? " (" + externalRequests.slice(0, 3).join(", ") + ")" : ""));
    } catch (err) {
      assert(false, "self-test threw: " + String((err && err.message) || err));
    } finally {
      window.fetch = origFetch;
    }

    // Return to overview with pass/fail banner, and put the route, breadcrumbs
    // and nav highlight back on the active view.
    restoreRouteChrome();
    renderOverview();
    const failed = checks.filter((c) => !c.ok);
    const result = {
      pass: failed.length === 0,
      passed: checks.length - failed.length,
      failed: failed.length,
      total: checks.length,
      loaded_bytes: state.loadedBytes,
      loaded_files: state.loadedFiles.size,
      external_requests: externalRequests.length,
      checks
    };
    window.__LEANRE_SITE_SELFTEST_RESULT = result;
    const banner = el("div", {
      id: "selftestBanner",
      className: "selftest-banner" + (result.pass ? "" : " fail"),
      textContent: (result.pass ? "SELFTEST PASS" : "SELFTEST FAIL") + " — " + result.passed + "/" + result.total + " checks (" + formatBytes(result.loaded_bytes) + ", " + result.loaded_files + " files)" + (failed.length ? " | FAIL: " + failed.map((f) => f.msg).join("; ") : "")
    });
    const main = $("#appMain");
    if (main) main.prepend(banner);
    return result;
  }

  window.__LEANRE_SITE_SELFTEST = runSiteSelfTest;
  window.leanreSource = { githubBlobToRaw, openSourcePeek, openSourceCompare, close: closeSourceDrawer };

  // ---------- v2.4 overview, projects, chrome ----------
  // Canvas draw calls remember their arguments so a theme switch in full screen
  // can repaint them in place.
  atlasDrawHicCanvas = themeAwareDraw(atlasDrawHicCanvas);
  atlasDrawSyntenyCanvas = themeAwareDraw(atlasDrawSyntenyCanvas);
  drawModuleMatrix = themeAwareDraw(drawModuleMatrix);

  // Put the route, breadcrumbs and nav highlight back on the view in the URL.
  function restoreRouteChrome() {
    const r = parseHash();
    state.route = r;
    updateNavHighlight(r.tab);
    updateCrumbs(r);
    document.body.classList.toggle("route-projects", r.tab === "projects");
  }

  // Wide tables: a right-edge fade and a small "Scroll horizontally →" cue,
  // shown only while the table is wider than its box. The scrollable mobile
  // nav gets the same fade.
  function updateScrollCue(wrap) {
    if (!wrap.isConnected) return;
    const over = wrap.scrollWidth > wrap.clientWidth + 1;
    const atEnd = wrap.scrollLeft + wrap.clientWidth >= wrap.scrollWidth - 2;
    wrap.classList.toggle("tw-overflow", over);
    wrap.classList.toggle("tw-more", over && !atEnd);
    if (over && (!wrap._twCue || wrap._twCue.parentNode !== wrap)) {
      wrap._twCue = wrap._twCue || el("div", { className: "tw-cue", "aria-hidden": "true", textContent: "Scroll horizontally →" });
      wrap.insertBefore(wrap._twCue, wrap.firstChild);
    }
    if (wrap._twCue) wrap._twCue.hidden = !over;
  }
  function updateNavCue() {
    const nav = $("#mainNav");
    if (!nav) return;
    const over = nav.scrollWidth > nav.clientWidth + 1;
    nav.classList.toggle("nav-more", over && nav.scrollLeft + nav.clientWidth < nav.scrollWidth - 2);
  }
  const scrollCues = { mo: null, ro: null };
  function watchScrollCues() {
    if (scrollCues.mo || !window.MutationObserver) return;
    const ro = window.ResizeObserver ? new ResizeObserver((entries) => {
      for (const e of entries) {
        if (e.target.id === "mainNav") { updateNavCue(); continue; }
        const w = (e.target.classList.contains("table-wrap") || e.target.classList.contains("md-table-wrap")) ? e.target : e.target.closest(".table-wrap, .md-table-wrap");
        if (w) updateScrollCue(w);
      }
    }) : null;
    scrollCues.ro = ro;
    const scan = () => {
      $$(".table-wrap, .md-table-wrap").forEach((w) => {
        if (!w._twWired) {
          w._twWired = true;
          w.addEventListener("scroll", () => updateScrollCue(w), { passive: true });
          if (ro) ro.observe(w);
        }
        const t = w.querySelector("table");
        if (t && ro && w._twTable !== t) { w._twTable = t; ro.observe(t); }
        updateScrollCue(w);
      });
      updateNavCue();
    };
    let queued = false;
    const schedule = () => {
      if (queued) return;
      queued = true;
      requestAnimationFrame(() => { queued = false; scan(); });
    };
    scrollCues.mo = new MutationObserver(schedule);
    scrollCues.mo.observe(document.body, { childList: true, subtree: true });
    window.addEventListener("resize", schedule);
    const nav = $("#mainNav");
    if (nav) {
      nav.addEventListener("scroll", updateNavCue, { passive: true });
      if (ro) ro.observe(nav);
    }
    schedule();
  }

  // v2.4 overview/projects/chrome self-test (owned by the overview pass).
  async function runV24OverviewSelfTest(assert) {
    const m = state.manifest || {};
    const st = m.stats || {};
    const tick = (ms) => new Promise((r) => setTimeout(r, ms || 0));
    const frames = () => new Promise((r) => requestAnimationFrame(() => requestAnimationFrame(r)));

    // Shared helpers and labels.
    assert(licenseLabel("None (no license)") === "None" && licenseLabel("Apache-2.0") === "Apache-2.0", "license badges read \"None\", not \"None (no license)\"");
    const blob = "https://github.com/example-owner/example-repo/blob/0123456789abcdef0123456789abcdef01234567/Demo/Basic.lean#L2";
    const pk1 = makeSrcButton(blob, "x"), pk2 = makeSrcButton(blob, "x", { className: "btn sm", text: "Show source inline" }), pk3 = makeSrcButton(blob, "x", { className: "btn sm", text: "Source" });
    assert(pk1 && pk1.textContent === "Peek" && pk2.textContent === "Peek source" && pk3.textContent === "Peek source", "source preview buttons read \"Peek\" or \"Peek source\" everywhere");

    // Overview copy.
    renderOverview();
    const hero = $(".hero");
    const heroTxt = hero ? hero.textContent : "";
    const kpiTxt = ($(".kpi-strip") || {}).textContent || "";
    const kpiLabels = $$(".kpi-strip .kpi-label").map((n) => n.textContent);
    assert(!/\b1 (modules|files|lines|structures|theorems|declarations|diagrams|findings|dossiers)\b/i.test(heroTxt + " " + kpiTxt) && !/\b1Diagrams\b/.test(kpiTxt), "overview counts use singular forms for 1");
    if (m.source_only) {
      const h1 = ($(".hero h1") || {}).textContent || "";
      assert(!/depend on one another|hypotheses are actually used/.test(heroTxt) && /module import/.test(heroTxt), "source-only overview describes modules and imports, not declaration dependencies");
      assert(!m.title || /leanre/i.test(m.title) || h1.includes(m.title), "source-only overview title uses the project title (" + h1 + ")");
      assert(kpiLabels.includes("Module import edges") && !kpiLabels.includes("Dependency edges"), "source-only KPI reads \"Module import edges\"");
    }
    const nl = m.provenance && m.provenance.notes_layer;
    if (nl && nl.enabled === false) assert(!/review notes, written separately/.test(heroTxt), "overview omits the review-notes sentence when there are no review notes");
    const kT = Number(st.kernel_total_decls) || 0;
    if (kT && st.total_decls && kT !== Number(st.total_decls)) {
      assert(kpiTxt.includes("of " + fmtInt(kT) + " kernel declarations (" + fmtInt(st.total_decls) + " in source)"), "reachable count names kernel and source totals when they differ");
    }
    const cir = m.circuits || {};
    if (cir.macro && !(cir.bundles || []).length && !(cir.theorems || []).length) {
      assert(/Module map/.test(kpiTxt) && !/0 structures/.test(kpiTxt), "Diagrams card reads \"Module map\" when only the module map exists");
    }
    assert(!$$(".dom-row").some((r) => /diagram for Macro/.test(r.getAttribute("title") || "")), "spine rows never say \"Open the diagram for Macro\"");
    if (pillarsCountModules(m)) {
      state.overviewLens = "spine";
      renderOverview();
      const lede = ($("#lensBody .section-lede") || {}).textContent || "";
      assert(/counts the modules/.test(lede), "spine lede counts modules when the bars count modules");
    }

    // Diagrams on projects without structures or theorems.
    if (cir.macro && !(cir.bundles || []).length && !(cir.theorems || []).length) {
      await renderCircuitView("macro", "");
      const segTxt = $$(".circuit-shell .seg button").map((b) => b.textContent).join("|");
      const note = ($("#cirChipsWrap") || {}).textContent || "";
      assert(!/\(0\)/.test(segTxt) && (!m.source_only || note === "Source-only scan: module import map only."), "Diagrams hides empty tabs and explains a module-map-only scan");
    }

    // Topbar: the repo pill is hidden while the project switcher shows.
    const sw = $("#projSwitch"), pill = $("#brandRepo");
    if (sw && pill && !sw.classList.contains("hidden")) assert(getComputedStyle(pill).display === "none", "topbar shows the project name once (switcher, not the repo pill)");

    // Comparison table: short headers, footnote, fits at desktop width.
    if (state.registry && state.registry.comparison) {
      await renderProjectsHome();
      for (let i = 0; i < 60 && !$(".cmp-table"); i++) await tick(50);
      const tbl = $(".cmp-table");
      if (tbl) {
        const ths = $$("th", tbl);
        const decTh = ths.find((t) => /Source decls/.test(t.textContent));
        assert(decTh && /kernel auxiliaries/.test(decTh.getAttribute("title") || "") && ths.every((t) => t.textContent.replace(/[⇅▲▼]/g, "").trim().length <= 13), "comparison table uses short headers with full names in tooltips");
        assert(!/\(no license\)/.test(tbl.textContent), "comparison table license reads \"None\"");
        const rows = $$("tbody tr", tbl);
        const rhRow = rows.find((r) => /Riemann/.test(r.textContent));
        if (rhRow && $(".cmp-footnote")) assert(/0\.0%\*/.test(rhRow.textContent) && /^\* All [\d,]+ RH files are imported from Main/.test($(".cmp-footnote").textContent), "RH orphan share carries a footnote about files with no kernel declarations");
        await frames();
        const wrap = tbl.closest(".table-wrap");
        if (window.innerWidth >= 1400) assert(wrap.scrollWidth <= wrap.clientWidth + 1, "comparison table fits the content width at desktop size (" + wrap.scrollWidth + " ≤ " + wrap.clientWidth + ")");
      }
    }

    // Scroll cue on wide tables (fixture).
    const main = $("#appMain");
    const fixTable = el("table", { style: { width: "900px" } }, [el("tbody", null, [el("tr", null, [el("td", { textContent: "wide" })])])]);
    const fix = el("div", { className: "table-wrap", style: { width: "240px" } }, [fixTable]);
    main.appendChild(fix);
    await frames(); await frames();
    const cueOn = fix.classList.contains("tw-overflow") && fix.classList.contains("tw-more") && fix.querySelector(".tw-cue") && !fix.querySelector(".tw-cue").hidden;
    fixTable.style.width = "120px";
    await tick(60); await frames();
    const cueOff = !fix.classList.contains("tw-overflow") && (!fix.querySelector(".tw-cue") || fix.querySelector(".tw-cue").hidden);
    fix.remove();
    assert(cueOn && cueOff, "wide tables show a scroll cue only while they overflow");

    // Theme switch inside full screen keeps full screen and repaints canvases.
    if (m.assets && (m.assets.atlas || m.assets.module_matrix)) {
      state.route = { tab: "atlas", sub: "", arg: "" };
      await renderAtlasView("");
      const cv = $("#hicCanvas") || $("#moduleMatrixCanvas");
      const card = cv && (cv.closest(".atlas-card") || cv.closest(".fs-target") || cv.parentElement);
      const fsb = card && card.querySelector(".fs-btn");
      if (fsb) {
        fsb.click();
        applyTheme("light", true);
        await frames();
        const px = cv.getContext("2d").getImageData(2, 2, 1, 1).data;
        const kept = card.isConnected && card.classList.contains("fs-on") && document.body.classList.contains("fs-lock");
        applyTheme("dark", true);
        await frames();
        fsState.themeStale = false;
        exitFullscreen();
        await tick(40);
        assert(kept && px[0] > 200 && !card.classList.contains("fs-on"), "switching theme in full screen stays in full screen and repaints the canvas");
      }
    }
  }

  // v2.3 chrome/keyboard/search self-test (owned by the chrome pass).
  async function runV23ChromeSelfTest(assert) {
    const m = state.manifest || {};
    const tick = (ms) => new Promise((r) => setTimeout(r, ms || 0));
    const esc = () => document.dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true, cancelable: true }));

    const tabs = $$("#mainNav .nav-tab");
    assert(tabs.length > 0 && tabs.every((a) => a.tagName === "A" && a.getAttribute("href") === "#" + a.dataset.route), "nav tabs are real links, so they can open in a new tab");
    const main = $("#appMain");
    const ann = $("#srAnnouncer");
    assert(main && !main.hasAttribute("aria-live") && ann && ann.getAttribute("aria-live") === "polite" && ann.classList.contains("sr-only"), "page changes are announced by a small live region, not the whole page");
    const hdr = $(".topbar");
    const th = parseFloat(getComputedStyle(document.documentElement).getPropertyValue("--topbar-h"));
    assert(hdr && Math.abs(th - hdr.getBoundingClientRect().height) <= 1, "sticky offsets follow the header height");

    const st = el("span");
    const b = el("button", { type: "button", textContent: "Copy" });
    flashStatus(st, "Copied lines 1–2", b, 40);
    const shown = st.textContent === "Copied lines 1–2" && b.textContent === "✓ Copied";
    await tick(90);
    assert(shown && st.textContent === "" && b.textContent === "Copy", "copy feedback resets by itself");

    if (m.circuits && m.circuits.macro) {
      await renderCircuitView("macro", "");
      const wrap = $("#cirStageWrap");
      const shell = $(".circuit-shell");
      const rc = wrap.getBoundingClientRect();
      const at = { clientX: rc.left + rc.width / 2, clientY: rc.top + rc.height / 2, deltaY: -100, bubbles: true, cancelable: true };
      const s0 = state.circuit.scale;
      const plain = new WheelEvent("wheel", at);
      wrap.dispatchEvent(plain);
      const passThrough = !plain.defaultPrevented && state.circuit.scale === s0 && !!wrap.querySelector(".cir-zoom-hint.show");
      const withCtrl = new WheelEvent("wheel", Object.assign({ ctrlKey: true }, at));
      wrap.dispatchEvent(withCtrl);
      assert(passThrough && withCtrl.defaultPrevented && state.circuit.scale > s0, "diagram: plain scrolling passes to the page; Ctrl/⌘ + scroll zooms");
      fitCircuitStage();

      const node = $("#cirStage .circuit-node[data-drill='1']") || $("#cirStage .circuit-node");
      if (node) {
        const before = window.location.hash;
        state.circuit.dragMoved = 0;
        node.dispatchEvent(new MouseEvent("click", { bubbles: true, cancelable: true }));
        const hdTxt = () => (($("#cirInspector .cir-ins-hd") || {}).textContent || "");
        const locked = window.location.hash === before && /Selected/.test(hdTxt()) && Boolean(state.circuit.selectedItem);
        const drillOk = node.getAttribute("data-drill") !== "1" || Boolean($("#cirInspector a.cir-drill[href^='#circuit/']"));
        const other = $$("#cirStage .circuit-node").find((n) => n !== node);
        if (other) { other.dispatchEvent(new MouseEvent("mouseenter")); other.dispatchEvent(new MouseEvent("mouseleave")); }
        assert(locked && drillOk && /Selected/.test(hdTxt()), "diagram: a click locks the selection in the inspector, with a link to open its own diagram");

        const fsBtn = shell.querySelector(".fs-btn");
        fsBtn.click();
        const fsOn = shell.classList.contains("fs-on");
        await openSourcePeek({ url: "https://github.com/example-owner/example-repo/blob/0123456789abcdef0123456789abcdef01234567/Demo/Basic.lean#L2", title: "demo_target", _fixtureText: "theorem a : True := trivial\ntheorem b : True := trivial\n" });
        const drawer = $("#srcDrawer");
        const dz = drawer ? Number(getComputedStyle(drawer).zIndex) : 0;
        assert(fsOn && shell.classList.contains("fs-on") && drawer && !drawer.hidden && dz > 900 && shell.contains(drawer), "source opens above a full-screen diagram without leaving full screen");
        esc();
        const s1 = drawer.hidden && drawer.parentNode === document.body && shell.classList.contains("fs-on") && Boolean(state.circuit.selectedItem);
        esc();
        const s2 = !state.circuit.selectedItem && shell.classList.contains("fs-on");
        esc();
        await tick(60);
        const s3 = !shell.classList.contains("fs-on");
        assert(s1 && s2 && s3, "Esc closes one layer at a time: source, then selection, then full screen");
      }
    }

    const shardNames = getSearchShardNames();
    const q = shardNames.find((s) => s !== "_" && s.length >= 2) || "ma";
    renderSearchView(q);
    await runSearchQuery();
    await tick(30);
    const inp = $("#globalSearchInput");
    if (inp && $$("#searchResultsBox .search-result-row").length >= 2) {
      const down = () => inp.dispatchEvent(new KeyboardEvent("keydown", { key: "ArrowDown", bubbles: true, cancelable: true }));
      down(); down();
      const rows = $$("#searchResultsBox .search-result-row");
      assert(rows[1].classList.contains("kb-active") && !rows[0].classList.contains("kb-active") && Boolean(rows[1].querySelector(".sr-acts a[href^='#']")), "search results can be stepped through with the arrow keys and opened with Enter");
    }
    assert(searchReturnTarget() !== "" && !/^#search/.test(searchReturnTarget()), "Esc on search returns to the previous page");
  }

  // ---------- Global Chrome Wiring & Boot ----------
  const chromeState = { lastRoute: "", searchPushed: false };

  function announce(msg) {
    const box = $("#srAnnouncer");
    if (!box) return;
    box.textContent = "";
    requestAnimationFrame(() => { box.textContent = msg; });
  }

  function chromeAfterRoute(r) {
    if (r.tab !== "search") {
      chromeState.lastRoute = window.location.hash && !/selftest/.test(window.location.hash) ? window.location.hash : "#" + r.tab;
      chromeState.searchPushed = false;
    }
    const tab = $("#tab-" + r.tab);
    let label = tab ? tab.textContent.trim() : "";
    if (r.tab === "item") label = "Declaration " + shortName([r.sub, r.arg].filter(Boolean).join("/"));
    else if (r.tab === "search") label = "Search";
    else if (r.tab === "projects") label = "All proofs";
    if (label) announce("Opened " + label);
  }

  function searchReturnTarget() {
    return chromeState.lastRoute || "#overview";
  }

  function openSearch() {
    if (state.route && state.route.tab === "search" && $("#globalSearchInput")) {
      const i = $("#globalSearchInput");
      i.focus();
      i.select();
      return;
    }
    chromeState.searchPushed = true;
    navigate("#search");
  }

  function leaveSearch() {
    if (chromeState.searchPushed && window.history.length > 1) {
      chromeState.searchPushed = false;
      window.history.back();
      return;
    }
    navigate(searchReturnTarget());
  }

  // Close a visible tray (matrix cell details and similar) inside the current
  // full-screen element, or inside the page.
  function closeOpenTray() {
    const scope = fsState.el && document.contains(fsState.el) ? fsState.el : $("#appMain");
    if (!scope) return false;
    const btn = $$("[data-esc-close], .tray-hd .icon-btn", scope).find((x) => x.getClientRects().length > 0);
    if (!btn) return false;
    btn.click();
    return true;
  }

  // One ordered Escape stack: menu → tip → source drawer → mobile outline →
  // tray / selection → full screen → back from search.
  function handleGlobalEscape(ev) {
    if (ev.key !== "Escape" || ev.defaultPrevented) return;
    const t = ev.target && ev.target.nodeType === 1 ? ev.target : null;
    const consume = () => { ev.preventDefault(); ev.stopPropagation(); };
    const menu = $("#projMenu");
    if (menu && !menu.hidden) { closeProjectMenu(); const b = $("#projBtn"); if (b) b.focus(); consume(); return; }
    const tip = $("#circuitTip");
    if (tip && tip.style.display === "block") { tip.style.display = "none"; consume(); return; }
    if (srcView.root && !srcView.root.hidden) { closeSourceDrawer(); consume(); return; }
    // Let a filled-in filter box clear itself first.
    if (t && t.id !== "globalSearchInput" && t.matches("textarea, input:not([type]), input[type='text'], input[type='search']") && t.value) return;
    if (state.rail.mobileOpen) { toggleRail(false); consume(); return; }
    if (closeOpenTray()) { consume(); return; }
    if (state.circuit.selectedItem && $("#cirInspector") && clearCircuitSelection()) { consume(); return; }
    if (fsState.el) { exitFullscreen(); consume(); return; }
    if (state.route && state.route.tab === "search") { consume(); leaveSearch(); }
  }

  // Keep keyboard focus inside the source drawer while it is open.
  function trapDrawerTab(ev) {
    if (ev.key !== "Tab" || !srcView.root || srcView.root.hidden) return;
    const f = $$("button, a[href], input, select, [tabindex]:not([tabindex='-1'])", srcView.root).filter((x) => !x.disabled && x.getClientRects().length > 0);
    if (!f.length) return;
    const first = f[0], last = f[f.length - 1];
    const a = document.activeElement;
    if (!srcView.root.contains(a)) { ev.preventDefault(); first.focus(); }
    else if (ev.shiftKey && a === first) { ev.preventDefault(); last.focus(); }
    else if (!ev.shiftKey && a === last) { ev.preventDefault(); first.focus(); }
  }

  // Sticky offsets (outline rail, diagram shell) follow the real header height,
  // which grows when the header wraps onto two rows.
  function watchTopbarHeight() {
    const hdr = $(".topbar");
    if (!hdr) return;
    const set = () => document.documentElement.style.setProperty("--topbar-h", Math.round(hdr.getBoundingClientRect().height) + "px");
    set();
    if (window.ResizeObserver) new ResizeObserver(set).observe(hdr);
    else window.addEventListener("resize", set);
  }

  function wireGlobalControls() {
    watchTopbarHeight();
    watchScrollCues();
    // Tabs are real links (new tab / copy link work); re-clicking the current tab reloads the view.
    $$("#mainNav .nav-tab").forEach((a) => {
      a.addEventListener("click", (ev) => {
        if (ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
        if (window.location.hash === a.getAttribute("href")) { ev.preventDefault(); handleRoute(); }
      });
    });
    const themeBtn = $("#themeToggleBtn");
    if (themeBtn) {
      themeBtn.addEventListener("click", () => applyTheme(state.theme === "dark" ? "light" : "dark", true));
    }
    const qBtn = $("#quickSearchBtn");
    if (qBtn) {
      qBtn.addEventListener("click", openSearch);
    }
    window.addEventListener("keydown", (ev) => {
      if (ev.key === "/" && !ev.ctrlKey && !ev.metaKey && !ev.altKey && !ev.defaultPrevented) {
        const ae = document.activeElement;
        const tag = (ae && ae.tagName || "").toLowerCase();
        if (tag !== "input" && tag !== "textarea" && tag !== "select" && !(ae && ae.isContentEditable)) {
          ev.preventDefault();
          openSearch();
        }
      }
    });
    window.addEventListener("hashchange", handleRoute);
    const railBtn = $("#railToggleBtn");
    if (railBtn) railBtn.addEventListener("click", () => toggleRail());
    document.addEventListener("click", (ev) => {
      const sw = $("#projSwitch");
      if (sw && !sw.contains(ev.target)) closeProjectMenu();
      if (state.rail.mobileOpen) {
        const rail = $("#outlineRail");
        const btn = $("#railToggleBtn");
        if (rail && !rail.contains(ev.target) && btn && !btn.contains(ev.target)) toggleRail(false);
      }
    });
    document.addEventListener("keydown", handleGlobalEscape);
    document.addEventListener("keydown", trapDrawerTab);
    let resizeT = null;
    window.addEventListener("resize", () => {
      clearTimeout(resizeT);
      resizeT = setTimeout(applyRailVisibility, 120);
    });
  }

  async function boot() {
    initTheme();
    initRailState();
    wireGlobalControls();
    updateNavHighlight(parseHash().tab);
    // projects.json is read only when we know a gallery exists: inside one
    // (?p=<slug>), or when the manifest names a registry.
    const wanted = new URLSearchParams(window.location.search).get("p") || "";
    if (wanted) state.registry = await loadRegistry();
    const entry = wanted && state.registry ? state.registry.projects.find((p) => p.slug === wanted) : null;
    if (entry) state.base = entry._base;
    else if (wanted && state.registry) state.missingProject = wanted;
    try {
      state.manifest = await fetchJson("./manifest.json");
      if (!state.base) state.rootManifest = state.manifest;
      if (!wanted) {
        const hasKey = Object.prototype.hasOwnProperty.call(state.manifest, "registry");
        if (!hasKey || state.manifest.registry) state.registry = await loadRegistry();
      }
      populateChromeFromManifest();
      renderProjectSwitcher();
      state.booted = true;
      await handleRoute();
      // Upgrade the outline once the page is idle (same-origin data only).
      const idle = window.requestIdleCallback || ((fn) => setTimeout(fn, 1200));
      if (state.manifest.assets && state.manifest.assets.outline) {
        idle(() => { ensureOutline().then((o) => { if (o && state.rail.mode === "spine") renderRail(); }); });
      }
    } catch (err) {
      if (!state.registry && !wanted) state.registry = await loadRegistry();
      if (state.registry) {
        // A gallery root without its own project: show the list of proofs.
        state.manifest = null;
        state.booted = true;
        $$("#mainNav .nav-tab").forEach((b) => b.classList.add("hidden"));
        renderProjectSwitcher();
        renderRail();
        await handleRoute();
        return;
      }
      const main = $("#appMain");
      if (main) {
        clearEl(main);
        main.appendChild(el("div", { className: "empty-card" }, [
          el("h3", { textContent: "Could not load the site data" }),
          el("p", { textContent: "This page needs to be served over HTTP (for example `python3 -m http.server`) or from GitHub Pages. Details: " + String(err.message || err) })
        ]));
      }
    }
  }

  document.addEventListener("DOMContentLoaded", boot);
})();
