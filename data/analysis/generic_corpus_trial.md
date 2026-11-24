# Cross-Repository Static Analysis Benchmark (Five External Lean 4 Corpora)

> **Target:** Five non-RH Lean 4 repositories (`examples/tiny_demo`, `PrimeNumberTheoremAnd`, `carleson`, `FLT`, `SpherePacking`; default CLI flags) · **Data:** [`outputs/xrepo_benchmark.json`](../outputs/xrepo_benchmark.json)
> **Scope:** Only `tiny_demo` includes a compiled NDJSON export (`demo.ndjson`), so kernel-DAG subcommands remain unread on the four external source-only corpora; see [the analysis index](README.md) for tags.

## 1. Five-Repository Corpus Summary `[L]`

| Repo (Toolchain) | Mods (before → after) | `wc -l` | Edges | `decls` (`thm/def/ind/ax`) | `sorry` (Mods) | Root / Hub (`dom/reach`) | Misfile Outliers (before → after) | Time (s) | Default CLI Exit |
|---|---:|---:|---:|---|---:|---|---|---:|---|
| `tiny_demo` (`v4.33.1` exp) | `5 -> 5` | `88` | `6` | `11` (`6/4/1/0`) | `0` (`0`) | `Main` (`4/4`) | `0/5` (`0.0%`) | `0.61` | **PASS** (`0` all cmds) |
| `PrimeNumberTheoremAnd` (`v4.35.0`) | `235 -> 234` | `172,295` | `517` | `9,054` (`8,293/740/21/0`) | `205` (`231` total, `20`) | `PrimeNumberTheoremAnd` (`104/104`) | `113 -> 79` (`48.1% -> 33.8%`) | `4.87` | `FAIL -> PASS` (`0` def) |
| `carleson` (`v4.36.0-rc1`) | `128 -> 127` | `50,189` | `332` | `3,103` (`2,599/468/36/0`) | `6` (`2`) | `Carleson` (`125/125`) | `14 -> 2` (`10.9% -> 1.6%`) | `2.48` | `FAIL -> PASS` (`0` def) |
| `FLT` (`v4.35.0`) | `271 -> 265` | `58,362` | `663` | `3,732` (`2,241/1,440/48/3`) | `60` (`20`) | `FLT` (`261/261`, was `34`) | `106 -> 62` (`39.1% -> 23.4%`) | `1.73` | `FAIL -> PASS` (`0` def) |
| `SpherePacking` (`v4.36.0`) | `73 -> 73` | `15,446` | `197` | `1,212` (`947/261/2/2`) | `61` (`19`) | `SpherePacking` (`73/73`) | `8 -> 6` (`11.0% -> 8.2%`) | `1.18` | `FAIL -> PASS` (`0` def) |

- **Scanner & `init` highlights `[L]`:** `init` discovers non-empty headline roots on all 5 repos (`tiny_demo`: `6` qualified `TinyDemo.*`; `PNT+`: `16`; `carleson`: `3`; `FLT`: `1`; `SpherePacking`: `16`). `PNT+` default `scan` reports `205` `sorry` hits + `26` truncated in `1` module; `--max-hits-per-tag 0` captures all `231` (`2.42s`). Also logged: `PNT+` `native_decide=83`, `unsafe=1`; `SpherePacking` `decide +kernel=2`; `FLT` `axiom=3`.
- **Directory & fingerprinting cleanup `[L]`:** `discover_lean_files` skips helper trees (`PNT+` `-1`, `carleson` `-1`, `FLT` `-6`), fixing `FLT` default `--root auto` (`34/271 -> 261/265`). `flirt tier1` sets `kernel_precision_calibration: null` with zero RH calibration output across all 5 repos.

## 2. `examples/tiny_demo` End-to-End Pipeline `[L]`

| Stage / Command | Key Verified Behavior | Metrics / Output | Runtime (s) |
|---|---|---|---:|
| `init`, `scan`, `ndjson`, `forensics` | Consecutive dossier headings (`1..3`), zero RH report keys | `5` mods, `11` decls, `17` TCB, `39` edges | `0.60` |
| `kernel extract` (no `--root`, `--src-dir`) | Auto-reads `examples/tiny_demo/leanre.toml` (`TinyDemo.main_theorem:DEMO`) | `10` live / `7` dead, `76.47%` aligned, `0` oracle fails | `0.19` |
| `trim` isolation (bare vs `--config`) | Bare `--kernel-db` exits `1` refusing RH fallback; `--config` prints `tiny_demo` banner | `5->2` mods, `88->36` lines, `10->7` live, `39->29` vn | `0.14` / `0.13` |
| `bundles` (`--src-root examples/tiny_demo`) | Finds `TinyDemo.ProofBundle` (`2` fields, `1` unread `unusedNote`), no `src/` prefix | Anchor `"Bundles.lean"` (line `10`); keeps `rh_depth` | `0.13` |
| `decompile resolve` / `contract` / `producers` | Exact-case resolution & producers (`mkDemoBundle`), no `src/` prefix | `"Main.lean"` (line `12`), `"Bundles.lean"` (line `14`) | `0.13–0.14` |
| `kernel hygiene` / `kdiff` / `portability` | Hygiene `--cone-depth 2` clean; self-diff `0` regressions; `scoped` cone | `7` audited (`0` hits); `17` unch; `8` proj + `2` ext | `0.13–0.15` |
| `export-site --demo` | Self-contained static HTML with kernel + portability views (`1` `rh_depth` key) | `44,624 B`, `has_kernel=true`, `has_portability=true` | `0.15` |

## 3. Cross-Repository Isolation and Calibration Checks `[L]`/`[M]`

| Check | Component | Status | Verified Behavior & Remaining Notes |
|---|---|---|---|
| Auto-root detection | `leanre/leanre.py` | **PASS** | `scan`/`all` default `--root auto` (`exit 0` across all 5 repos); `--config` wired across subcommands. |
| Helper-directory filtering | `leanre/scanner.py` | **PASS** | Non-lib skip list (`blueprint*`, `scripts`, `examples`) + `lakefile.toml` targets fix `FLT` (`34/271 -> 261/265`). |
| Profile config auto-loading | `leanre/kernel.py` | **PASS** | `kernel extract --src-dir examples/tiny_demo` auto-loads `leanre.toml` (`live=10, dead=7`, no `--root`). |
| Cross-repo path isolation | `leanre/trim.py` | **PASS** | Bare `--kernel-db` refuses RH `data/rh_mirror/src` fallback (`exit 1`); `--config` uses `tiny_demo` banner. |
| Calibration neutrality | `leanre/flirt/tier1.py` | **PASS** | `kernel_precision_calibration: null`, zero RH F1 stdout, misfiles down (`PNT+` `-14.3%`, `FLT` `-15.7%`, `carleson` `-9.4%`). |
| Anchor prefix & depth keys | `bundles`, `decompile`, `export_site` | **PARTIAL** | `"src/"` anchor prefix removed (`Bundles.lean` / `Main.lean`); legacy `"rh_depth"` key still emitted beside `root_depth`. |
| Headline root discovery | `leanre/config.py` | **PASS** | `init` qualifies `TinyDemo.*` (`6` roots) and discovers `16`/`16` headlines on `PNT+`/`SpherePacking` (was `[]`). |
| Report schema neutrality | `forensics`, `kernel`, `scanner` | **PASS** | RH report/reconciliation keys removed; headings consecutive; `decl_counts_by_kind` + `--max-hits-per-tag` truncation logged. |
