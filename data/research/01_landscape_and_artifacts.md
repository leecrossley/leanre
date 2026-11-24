# Upstream Artifacts and Independent Kernel Checkers

Levent Alpöge and Claude released a 175,187-file Lean 4 formalization on Nov 20, 2026 claiming RH and Dirichlet-only GRH. Machine verification checks formal derivability from Lean's axioms (Layer 1), not human mathematical refereeing or Clay Prize consensus (see [epistemic scope](04_verification_and_roadmap.md)).

## 1. Primary Sources & Mirrors

- Announcement and archive: [alpo.ge](https://alpo.ge/) and the four-page [announcement note](https://alpo.ge/remark.pdf) (`245,114` B, SHA-256 `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d`). The original 14-part archive (`alpo.ge/lean.tar.gz.part01`..`part14`) joins to `239,275,554` B (`228.2` MiB), SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. (`alpo.ge` returns HTTP 200 HTML for nonexistent paths such as `part15`; verify the joined SHA-256.)
- Licensing: published with no license file. This repository tracks zero `.lean` files and zero multi-line proof bodies; local reference copies sit in gitignored `research/sources/`.
- Community discussions: [Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis), [Hacker News](https://news.ycombinator.com/item?id=50574968), [Mathstodon](https://mathstodon.xyz/@TaliaRinger/117649440491814636), and the [Lean 4 Dev overview](https://lean4.dev/proofs/riemann-hypothesis-claim).
- Same-day draft: hours after Alpöge's release on Nov 20, 2026, Ravi Vakil announced Alessandro Maria Masullo's ~940-page human-written, non-Lean draft (*The Music of the Primes*). It is unrelated to Alpöge's Lean archive.

| Hub / Mirror | Role |
|---|---|
| [Andrew Sutherland (MIT)](https://math.mit.edu/~drew/grh/) | Primary independent verification ledger and `lean4export` v3.1.0 dumps (`solution.ndjson.zst` `7.7` GB, `challenge.ndjson.zst` `47` MB, logs, `SHA256SUMS`). |
| [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) | Byte-exact mirror (redirected from `Deicyde/riemann-hypothesis`, pinned commit `40e56bab`), `Challenge.lean`, Comparator CI, and security/kernel audit notes. |
| [Infatoshi/rh-verification-receipts](https://github.com/Infatoshi/rh-verification-receipts) | Elliot Arledge's independent full rebuild, separately generated `61.57` GB export, and Rust `nanoda` replay (`1,484,729` constants accepted). |
| [Simon DeDeo replay](https://photos.proofsandreasons.io/wright/alp-replay.json) | Independent source-bound full `leanchecker` replay (`175,187/175,187` modules accepted in `3h 22m 16s`). |
| [rohanarun/alpoge-rh-replay](https://github.com/rohanarun/alpoge-rh-replay) | Distributed module-by-module replay tracker (`90` volunteers, `2,858` work packets, [dashboard](https://rohanarun.github.io/alpoge-rh-replay/)). |
| [jsmorph/rh](https://github.com/jsmorph/rh), [CocoSgt](https://github.com/CocoSgt/riemann-hypothesis-lean), [TomasOrtega](https://github.com/TomasOrtega/RH), [Tomodovodoo](https://github.com/Tomodovodoo/Riemann) | Unmodified source mirrors (`jsmorph/rh` adds a conjectured timeline diagram). |

## 2. Scale, Endpoints & Independent Verification

| Metric | Value | Notes |
|---|---|---|
| Lean / Mathlib pin | `v4.33.1` (`819816b2` / `0df444a3`) | Mathlib is 1 commit over `v4.33.0` (`lean-toolchain` only); `8,322` Mathlib + `378` dep `.olean`s match official cache. |
| Source tree | `175,187` `.lean` files, `1,030,531,854` B | `17,374,215` physical lines (`wc -l`, `0` comments, ~7.6× Mathlib). Every file ends with `\n`; `17,549,402` in `drew2apps` adds 1 empty element per file from `split('\n')`. |
| Source declarations | `1,060,822` keyword decls | `818,755` `theorem`/`lemma` + `242,067` `def`/`abbrev`/`structure`/`class`/`instance`/`inductive`. |
| Compiled environment | `186,200` modules | `2,701,132` constants, `2,084,256` theorems, `15` axioms (all in `Init`). |
| Kernel export (`solution.ndjson`) | `61,570,595,788` B (`7.7` GB `.zst`) | **`1,468,418`** folded records (`con-leche`) == **`1,484,733`** unpacked constants (`nanoda` via `nasqret` on MIT export; Arledge's export has `1,484,729`). |
| Import vs. kernel liveness | `753,261` project edges, `44` BFS layers | All `175,187` files import-reachable from `Main` (`136,003` / `77.6%` `import Mathlib`), but **`28,904` modules contribute `0` kernel decls** (`28,471` unused files, `2.36M` lines). |

| Top-Level Library | Files | Lines (`wc -l`) | Share |
|---|---:|---:|---:|
| `Development` | `141,928` | `12,232,663` | `70.4%` |
| `Formalism` | `18,254` | `3,200,748` | `18.4%` |
| `GroundTheory` (+ `GroundTheoryFields`) | `8,507` | `1,119,138` | `6.4%` |
| `ReciprocityTheory` | `3,845` | `563,016` | `3.2%` |
| `CompanionTheory` | `2,027` | `194,218` | `1.1%` |
| `PositivityTheory` | `449` | `55,130` | `0.3%` |
| `Lemmata` | `167` | `9,232` | `0.05%` |
| `Supplements`, `BuildAid`, `Main`, `Statements` | `10` | `70` | `<0.01%` |

Directory names do not match contents: `Development/AbelianVarietyTheory` holds `99,187` files (`56.6%` of the repo) declaring mostly `_root_.GlobalTheory` (`39,212`), `IndefiniteRowSideFullHecke` (`14,165`), and `GlobalTheory.Mem` (`11,592`).

### Five Headline Theorems & Axiom Footprint

[Main](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4-L12) exports five theorems over Mathlib definitions and four transparent `Prop` wrappers in [Statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Statements.lean#L3-L16) (strictly **Dirichlet $L$-functions**, no Dedekind zeta or higher-rank $L$-functions):

1. [`riemannHypothesis`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4) — Mathlib's `RiemannHypothesis` (`0` project definitions in its `2,448`-def cone).
2. [`riemannZeta_eq_zero_re`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L6) — `RiemannZetaZerosOnLine` (`rfl`-equal to `RiemannHypothesis`).
3. [`LFunction_ne_zero_of_half_lt_re`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L8) — nonvanishing of `DirichletCharacter.LFunction χ s` for `Re s > 1/2` (`χ ≠ 1 ∨ s ≠ 1`).
4. [`LFunction_eq_zero_re`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L10) — critical-strip zeros lie on `Re s = 1/2` for all `χ` (including imprimitive).
5. [`LFunction_eq_zero_re_of_isPrimitive`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L12) — same for primitive `χ`.

All five depend solely on `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`, `Lean.ofReduceBool`, `unsafe`, `opaque`, or custom axioms.

### Independent Verification Matrix (as of 2026-11-21)

| Checker / Replay | Operators | Result | Key Numbers & Notes |
|---|---|---|---|
| Lean `v4.33.1` full build | Sutherland, DeDeo, Arledge, `nasqret` | PASS | `175,187/175,187` modules, `0` errors. |
| `leanchecker` replay | Sutherland, DeDeo | PASS | `175,187/175,187` accepted (DeDeo: `3h 22m 16s`). |
| `nanoda` (Rust) | Sutherland, Arledge, `nasqret` | ACCEPT | Sutherland: `27m 42s`, `84.8` GiB RSS; `nasqret` on MIT export: `1,484,733` constants; Arledge's export: `1,484,729`. |
| `con-leche` `master` (`cd2eceab`) | Sutherland | ACCEPT | `1,468,418` folded records (`--verified`), `3m 15s`, `45.6` GiB RSS. |
| `con-leche --compare` (`5dc36dc1`) | Sutherland, Teżewski, `nasqret` | ACCEPT | All 5 roots justified against `51,692`-record Mathlib `Challenge` (`sha256 bd484ac9…b2b9`). |
| `lean4lean` (`67f63b0c`, v4.33.1) | Sutherland | PASS | `175,182` passed at default fuel; `5` `decide +kernel` modules needed raised fuel — `4/5` ([`DyadicPrimeIntervals.Run1`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run1.lean)..`Run4`) are dead in `solution.ndjson.zst`, while [`ChebyshevPrimeBounds.SmallLoop`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/SmallLoop.lean) is `9/9` live. |
| Bundled v4.36 `con-leche`/`lean4lean` | Sutherland, Deicyde | N/A | Older `con-leche` rejected mutual reflexive inductive `PrincipalizationCertificate` (fixed on `master`); v4.36 `lean4lean` incompatible with v4.33 `Decidable.intro`. |

### Security and build notes

- Six metaprogramming sites exist — `BuildAid/D1..D5`, [`CutCptCopy`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean) (`addDecl`), [`kexactB`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean) (`67` files), [`kcopy`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean), `33` `run_tac` blocks, and 1 `@[positivity]` extension. All output terms are still kernel-checked.
- Lean `v4.33.1` predates `v4.34.1` runtime soundness fixes (`#15241`, `#15289`, `#15288`); independent non-Lean checkers (`nanoda`, `con-leche`) close this class.
- Independent builds matched `.olean` SHA-256 on only `76,968 / 175,187` modules (`51/51` sampled diffs had identical proof terms); Lake also emits `~0.8–1` TB of `.setup.json` unless pruned mid-build.

## 3. Author Roadmap vs. Verified Lean Spine

In the [announcement note](https://alpo.ge/remark.pdf), Alpöge describes the argument as *"a descendant of Stepanov's"* using a length-$\sqrt{X}$ chain of theta lifts between totally definite unitary groups to mimic multiplicity over $\mathbb{Z}$, predicts it *"will be massively simplified, likely immediately,"* and warns in Footnote 4 that parts of his 20-item Oct 6 – Nov 16 timeline paraphrase a Claude summary *"which might make zero sense"* (the Lean code is authoritative).

| Concept in author note | Status in `solution.ndjson.zst` |
|---|---|
| Smoothed ramp sum `Gz(x)` (item 5), localized Landau window | Live (`Gz` is defined in [the ramp sum helper](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/StatementOC.lean#L11-L13); [`Formalism.Gchi`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/StatementOC.lean#L20) is dead code, replaced by 3 guarded live `gChi` defs). |
| Iterated theta-lift chain of length $m \approx \sqrt{X}$, Bost slope, Chowla–Selberg/Minkowski, seesaw/Bessel (items 7–15, 18) | Live across Pillar A (`543,325` decls) and Pillar D (`80,720` decls); see [the whole-proof synthesis](../analysis/SYNTHESIS.md). |
| Iwasawa tower, weak Vandiver `H¹`/`Ш¹` bound, Behrend thick host (items 11, 17, 19) | Live: [`VWin`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L49) unfolds 100% to Mathlib (Pillar C, `92,705` decls); `hostThickExists` has `15` live decls. |
| Sixfold cover of `GL₅` (items 3, 16) | **Not found** (`0` hits; only 2-fold `MetaplecticRepresentation` of `Sp` exists). |
| Global Kuznetsov / relative trace formula (item 16) | **Partial** (`0` Kuznetsov/RTF hits; `24` live `JacquetRallis` unit-matching decls + `1,444` Arthur/simple twisted `TraceFormula` decls). |
| Stepanov auxiliary polynomials (item 1) | **Not found** (`0` hits; `Polynomial.hasseDeriv`'s `47` live callers are deformation / Ax–Sen / Frobenius lift bounds). |

Top-down, all five endpoints reduce via the functional-equation bridge (`58,857` decls, `31` project) to [`allChi`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Supplements/Kernels/MainTheorems.lean#L7) (`1,409,557` decls = `96.0%`), which applies a single modus ponens in [`everyCharacter`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L10) (`everyCharacter_of_row` `982,855` + `galoisLocalGlobalStrong_recParameter` `95,102` + `331,598`-decl shared diamond; see [the proof map](../findings/proof-map.md)). Inside [the literature-assembly module](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L215), `182/195` theorems are independent of `OpenLiteratureStatements` (`152` ignore it, `30` forward into dead ends), `4` directly project a field, and `13/195` transitively depend on it (`14/196` including `everyCharacter_of_row`); all `3` fields are discharged inside the archive (`⟨h, recTExists, h⟩`).

## 4. Community Ecosystem

| Category | Project | Coverage & Limits |
|---|---|---|
| Verification & replay | [Sutherland](https://math.mit.edu/~drew/grh/), [Infatoshi](https://github.com/Infatoshi/rh-verification-receipts), [DeDeo](https://photos.proofsandreasons.io/wright/alp-replay.json), [leanprover-community](https://github.com/leanprover-community/riemann-hypothesis), [rohanarun](https://github.com/rohanarun/alpoge-rh-replay) | Full compilation, `leanchecker`, `nanoda`, `con-leche --compare`, `lean4lean`, sandboxed Comparator CI, crowdsourced replay. |
| Dashboard & math atlas | [nasqret/riemann-rev](https://github.com/nasqret/riemann-rev) ([site](https://nasqret.github.io/riemann-rev/)) | 20-check ledger, 7-step math guide, 14-component / 107-decl HTML atlas, isolated dual-kernel bridge proofs. Graduate number-theory audience. |
| Blueprint & timeline | [jae-63/rh-alpoge-blueprint](https://github.com/jae-63/rh-alpoge-blueprint) | Top-layer `BLUEPRINT.md`, crux-vs-library split, depth≤8 pillar graph. Regex/text parsing only. |
| Import decomposition | [drew2apps/rh-lean-decomposition](https://github.com/drew2apps/rh-lean-decomposition) | File-import dominator tree (`7` components ≥1,000 modules), `23` self-contained folders, `150` import-only shims, `308` duplicate imports. File-level only. |
| Dead-code trimming | [keithadler/rh-trim](https://github.com/keithadler/rh-trim) | Proved text-based trimming breaks builds (~9% safe); full AWS build for `.olean` slicing and Tenet checker benchmarks. |
| Prose & reading guides | [tamnd/riemann](https://github.com/tamnd/riemann), [rithn/riemann-lean-reader](https://github.com/rithn/riemann-lean-reader), [LingYi-Liang](https://github.com/LingYi-Liang/alpoge-riemann-hypothesis-exposition) | Early prose expositions and static text maps. |
| Web source browser | [rgrossharv/riemann](https://github.com/rgrossharv/riemann) | Read-only Monaco viewer, treemap, 44-layer BFS profile. No declaration graph or semantic slicing. |
| General / video | [lean4.dev](https://lean4.dev/proofs/riemann-hypothesis-claim), [harttraveller/riemann](https://github.com/harttraveller/riemann) | 6-min news summary; rough Claude+Manim draft (author warns against reposting). |
