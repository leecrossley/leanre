# Synthesis: Structural Analysis of the RH Formalization

> **Target:** Whole-proof architecture over `175,187` files (`17,374,215` lines, pinned `40e56bab`) and `solution.ndjson.zst` (`5ea74b91…244e`: `1,468,418` folded records / `1,484,733` constants / `114,115,002` edges)
> **Kernel check:** `0` `sorryAx`, `0` `Lean.ofReduceBool`/`Lean.trustCompiler`, axioms `[propext, Classical.choice, Quot.sound]`; `2,570`-def statement closure clean ([tcb_and_contracts.md](tcb_and_contracts.md)). See [the analysis index](README.md) for scope and tags.

---

## 1. The Whole Proof on One Screen (`1,468,414` Live Kernel Declarations) `[L]`

```text
Main.lean (5 headline theorems — 1,468,414 live / 4 dead: Nat.lor, Nat.xor, String.mk, ._proof_1)
│
├── Bridge outside allChi: 58,857 decls (58,826 Mathlib/Lean + 31 project decls)
│   └── Functional-equation reflection (RhOfRight / CritLine / ClaimStrip) using only Mathlib [S]
│
└── allChi : UpperTheory.EveryCharacter  ⟦1,409,557 = 96.0% of live graph⟧
    ("∀ N [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1/2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → LFunction χ s ≠ 0")
    └── everyCharacter  ⟦1,409,556⟧  (modus ponens: everyCharacter_of_row (galoisLocalGlobalStrong_recParameter))
        │
        ├── [Pillar B] galoisLocalGlobalStrong_recParameter : Row0b recT  ⟦95,102 = 6.48%⟧
        │   • Builds odd-rank l-adic Galois reps in étale cohomology (Mathlib Scheme.etaleTopology)
        │     of unitary Shimura towers (geoOne_holds 82,643 / steps_holds 54,486)
        │   • Even ranks via theta lifts to two distinct odd ranks (tLiftK 4,104) + split-line subtraction
        │   • NOTE: Weakened inertia-only AwayB.tame0 (full Frobenius equality only under Tor ∧ mono0)
        │
        ├── everyCharacter_of_row (h : Row0b IsRecT) : EveryCharacter  ⟦982,855 = 66.93%⟧
        │   Packs O := ⟨h, recTExists, h⟩ : OpenLiteratureStatements (all 3 fields proved in-repo!)
        │   │
        │   ├── [Pillar C] vwin_of_row (h) : VWin  ⟦92,705 = 6.31%⟧
        │   │   • Unfolds 100% to Mathlib (0 OPAQUE leaves!): windowed bound on weighted ℤ_l-lengths
        │   │     of Ш¹(G_{E,S_l}, ℚ_l/ℤ_l(-e)) ≤ exp(x^ε / 2) over abelian CM compositum E
        │   │   • Discharged by Kato Euler systems (15,273), Sp(4) pro-modularity (11,275),
        │   │     U(3) Hida-window transfer (6,622), K-theory / Borel bounds (5,046),
        │   │     Taylor–Wiles patching (4,108), Jacquet–Shalika rigidity (3,755), Ferrero–Washington (348)
        │   │
        │   └── every_character_of_literature_of_vWin (O, VWin)  ⟦849,323 = 57.84%⟧
        │       ├── [Pillar A] every_character_of_theta_integrals_local_matching  ⟦543,325 = 37.00%⟧
        │       │   ├── Producer: nonempty_hyps_definite_side_of_closed_bound  ⟦451,610⟧ → HypsAlt (46 fields)
        │       │   │   • StageU.hypotheses_nonempty_of_unramified_exponents_alt  ⟦153,377⟧
        │       │   │   • ontoX_and_lamLow (34,969), open0 (22,768), thetaLift_row_properties_conj (9,399)
        │       │   └── Consumer: every_character_of_green_v_win  ⟦23,523⟧ → TopG → ZeroFreeAll → EveryCharacter
        │       │
        │       ├── [Pillar D] SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt  ⟦80,720 = 5.50%⟧
        │       │   • deep_slim_use (46,110): Arakelov / Moriwaki bigness / Hilbert–Samuel over MRing ι
        │       │   • topCovolG_alt_alt (20,154): covering-geometry / Bergman / Gram height bounds
        │       │
        │       └── Literature / Published bundles & classical libraries  ⟦225,278 residual under dom root⟧
        │           • theta_integrals_agree_and_local_matching_of_literature (14,173 — genuine Mathlib AdeleRing!)
        │           • toroidalForFanKS (7,185), published_results_arithmetic (7,105), hsChain (5,514),
        │             siegel_toroidal_integral_of_literature (5,446), canonicalAlgorithmRules_isCorrect (5,400), …
        │
        └── [Shared Diamond] 110,898 direct dominator children  ⟦331,598 = 22.58%⟧
            • 100% reachable from BOTH everyCharacter_of_row AND galoisLocalGlobalStrong_recParameter!
            • 63.4% project / 36.0% Mathlib; holds 100 of 387 GlobalTheory.Published defs
            • Heavy roots: GSp4Splitting.coreG (3,421), zarhinGeometric (2,519), leibnizOrd (2,398),
              frameEx_of_fin (2,355), deRham_potentiallySemistable (2,251), jacquetRallisUnitMatch (1,957),
              gm_of_bcfl (1,946), frameBound (1,841), rsPole (1,754), dualAbelianScheme (1,363),
              recTExists (595 — depth-zero LLC + GL₁ LCFT; dummy fallback junkEx on ¬GoodCusp), …
```

*Note on the `40,826` shared siblings under `everyCharacter_of_row` (`982,855 - 849,323 - 92,705 - 1 = 40,826`):* classical pillars shared by both `every_character_of_literature_of_vWin` and `vwin_of_row`, including `globalEulerChar_full` (`2,710`), `abelianDeRham` (`2,281`), `harishChandraFinite` (`2,133`), `localConverseGL` (`924`), `gsBaseCase` (`872`), and `poitouTateNormalised_holds` (`502`) `[L]`. (`UpperTheory.Zero.LLC.recTExists`, `595` decls, has `idom = everyCharacter`, placing it in the `331,598`-decl shared diamond because both `everyCharacter_of_row` and Pillar B's `inp_holds` reference it.)

---

## 2. The Single Most Important Answer: Does Layer 2 Have Any Soundness Holes? `[L]`

**No (`0` defects found in `analysis/tcb_and_contracts.md`).** By modus ponens in the Lean 4 kernel (`[S, M]`: *conservation of difficulty* — a weak intermediate `def` cannot rescue a false root), a soundness bug can only live at the root statement types, the `2,570`-definition statement closure, or the kernel/axiom base:

1. **Five headline theorems match `Challenge.lean` bit-for-bit** (`solution[stmt_mask!=0]` has `51,687` decls; `challenge \ solution = {sorryAx, Nat.lor, Nat.xor, String.mk, String.mk._proof_1}`; `solution \ challenge = ∅`). Every `1 / 2` is real division `@HDiv.hDiv ℝ`, zero `ℕ` truncation; `RiemannZetaZerosOnLine = RiemannHypothesis` by `rfl`. Scope is **strictly zeta + Dirichlet `LFunction` over `ℚ`** (no Dedekind/Hecke/Extended RH).
2. **`2,570`-def statement closure (`defcone_mask != 0`):** **`0` project definitions** appear inside `riemannHypothesis`'s `2,448`-def cone (and only `4` transparent wrapper defs from `src/Statements.lean:3-16` plus `4` `Batteries` defs in the 5-root union). Spot-checked `riemannZeta`, `completedRiemannZeta`, and `DirichletCharacter.LFunction` in `mathlib4@0df444a3`.
3. **175,187-file compiler hygiene sweep:** `0` hits of `unsafe`, `implemented_by`, `extern`, `csimp`, `meta`, `no_index`, `skipKernelTC`, `debug.*`, `sorry`/`admit`, `axiom`, `opaque`, `native_decide`, or global `notation`. `autoImplicit = false`, `relaxedAutoImplicit = false`.
4. **The `Formalism.Gchi` junk-value check (`src/Formalism/StatementOC.lean:20`):** Initially suspected of missing a `χ ≠ 1` guard before dividing by `LFunction χ 1`. **It is 100% dead code (`0` kernel decls)!** All **3 live** character observables (`An.gChi`, `GlobalTheoryTheory.gChi`, `Deduction.Gchi`) explicitly guard `if χ = 1` and invoke `LFunction_apply_one_ne_zero` on `χ ≠ 1`.
5. **Anti-vacuity inside Pillar A (`Closed 𝒞 P` & `Loc := Empty`):** `HypsAlt`'s `~25` `Closed` fields let the prover choose a threshold `K`, which would be vacuous if no `Large K` family existed; **the unique existence field `HypsAlt.hEx : MinkDiv → ExS 𝒜 cT` quantifies `∀ K, ∃ Fm` in the non-vacuous order**, discharged unconditionally by `minkowski_bound_rat` + `VWin` (`SupplyChi`). Separately, the follow-up audit (`analysis/deep_followup_audit.md`) traced the `Loc := Empty` / `η = 0` initializer and confirmed `Stage 1` (`bareLayer`) is only the initializer: **`Stage 2` (`withLoc`) populates non-empty `Loc` and maps the congruence defect `etaJ` into Bloch–Kato/Selmer bounds** without assuming `η = 0`.

---

## 3. Seven Structural Findings `[L]`

1. **`28,904` zero-kernel `.lean` files (`2,378,537` lines = `16.50%` of the corpus) are almost all real, unused dead code — NOT export omissions:**
   - Every single file (`175,187 / 175,187`) is transitively imported by `Main.lean`.
   - **`28,471` (`98.50%`, `2,358,861` lines)** are genuine imported modules whose declarations are never referenced by any of the 5 headline proofs (`19,363` inside `Development.AbelianVarietyTheory`, `7,336` signature-set clones, `5,676` wrappers). Only **`19`** (`0.07%`) were `decl_module` alignment gaps (`164` import shims, `11` meta/elab-only, `239` unused private/inline).
2. **`DyadicPrimeIntervals.Run1..4` (4 of the 5 `lean4lean` fuel-timeout files) ARE 100% dead in `solution.ndjson.zst`:**
   - Exact verified cut-point: `Run1..4` → `SmallNaturalNumbersBound` → `PrimesDyadicRS` → `SqfCounts` (`counts_closed`) → called ONLY by dead theorems `CylinderCountFamily.family_bound_all` and `JCount.family_count_all`. `Main` imports them only because those two files also define live data structs (`AllRowsAt`, `CountCylAt`).
   - By contrast, **`ChebyshevPrimeBounds.SmallLoop`** IS `9/9` live (`PI.PC.loop_run._proof_1_1`, `id=571290`, 35.1s in `con-leche`). Across the whole repo, `decide +kernel` appears in `34` files (`124` lines / `151` occurrences): only **`14` files** put `decide +kernel` checks into the live kernel (`table_ok`, `SmallLoop`, factorial ladders `13`/`31`/`141`, `lcmUpto`, Bernoulli `B_4`/`B_6`, etc.).
3. **`GlobalTheory.T.*` is an industrial renaming shell (names ≠ mathematical evidence):**
   - `38,194` of `38,677` `GlobalTheory.T.*` theorems kernel-wide (`14,362` inside Pillar A alone!) have **`value_nodes = 1`**, forwarding directly to internal lemmas under literature-sounding names. Folder names are equally scrambled: `Development/AbelianVarietyTheory` accounts for `99,187` files (`56.6%` of the repo) yet declares `_root_.GlobalTheory` (`39,212`), `IndefiniteRowSideFullHecke` (`14,165`), `GlobalTheory.Mem` (`11,592`).
4. **Substantial dead / phantom assumption bundles left inside the live proof:**
   - `published_results_eigen.siegelEisensteinSimplePole : UnusedSlot72` is literally **`Prop := True` proved by `trivial`**.
   - `OpenImageCondition` in Pillar C is **100% phantom** (`0/62` `*_of_open` wrappers ever project it).
   - `LiteratureCMHypothesis` (`907` live dominated decls incl. `serreTateGoodReduction`, `neronOggShafarevich`, `GaussManinTop.main`!) is **100% unread** (`0/11` fields ever projected — pulled into the export solely to fill a dead struct field!).
   - `OpenLiteratureStatements` (`195` `theorem`s in `EveryCharacterOfLiteratureOfVWin.lean`: `185` single-thm `:=` + `9` record assemblers + `1` top thm): `152` ignore `O`, only `4` directly project a field of `O` (`14` transitively consume any field of `O`), and all `3` fields of `O` are discharged inside `MainConclusion.lean` via `⟨h, recTExists, h⟩`.
   - Multiple earlier-draft top contracts (`Formalism.Gchi`, `plugAll`/`plugWin`, `GlobalTheory.Fc.Hyps`, `Fc.DRS`, `MainTheoremsAll`, `SmallClassNumbers/*`) are **100% dead code**.
5. **What "Published Theorems" really look like:**
   - All `60 + 53 + 71` fields of `UnitaryGroupThirdPlaceHypotheses` and `ThetaLocalInputs` are **proved in-repo** (nothing assumed as an axiom).
   - Key theorems grounded on real Mathlib types include `dualAbelianScheme` (`Scheme`-valued $\mathrm{Pic}^0_{A/S}$ via Čech 1-cocycles `LB` + rigidified additive universal property), `GlobalTheory.EtC` (genuine `Scheme.etaleTopology` étale cohomology), `ThetaIntegralsAgree`/`LocalMatching` (`AdeleRing`/`NumberField`/Haar fundamental domains), `GlobalEulerChar`, `PoitouTateNormalised`, `AbelianDeRham`, `LocalConverseGL`, `FarguesExact`, `Linnik`, `SiegelToroidalIntegral`, `ToroidalForFanKS`, and `SemiAbelianLieSeminegative`.
   - Notable intentional weakenings / proxy fallbacks include **`recTExists`'s `junkEx` fallback** on non-`GoodCusp` wildly-ramified reps (avoided inside `Row0b` via `CharPolOfInert.mixed_of_tame`), **`Row0b.AwayB.tame0`** (inertia-only characteristic polynomial equality outside `Tor ∧ mono0`), and Arakelov/Moriwaki bigness factored over multigraded `MRing ι` + `IsIntersectionFamily` (instantiated via `arithIntersectionSystem_of_poincareLelong_resK`).
6. **`remark.pdf` `[A]` vs actual Lean proof `[L]` reconciliation:**

| Concept mentioned in `remark.pdf` `[A]` | Found in live `solution.ndjson.zst`? `[L]` | Notes |
|---|---|---|
| Chain of `m` lifts with ranks `k + j(t+1)` | **Yes** | `Formalism.BasicNotions.D7` (`ColumnChain`) + `ThetaIntegralsAgree` |
| Mass / Chowla–Selberg / Weyl / Minkowski | **Yes** | `minkowski_bound_rat`, `topCovolSlim2_use_alt_alt` |
| Seesaw + Bessel period & covolume bounds | **Yes** | `besselNVG`, `SelfIntersectionVolumeEstimates` |
| Weakening of Vandiver (`Ш¹` / `H²` bound) | **Yes** | `VWin` (`ExistsPageN.lean:49`), **100% unfolded to Mathlib** |
| Behrend set / thick host construction | **Yes** | `Formalism.FrobeniusOrbits.hostThickExists` (`15` live decls) |
| **Sixfold / Kazhdan–Patterson cover of `GL₅`** | **NOT FOUND (`0` hits)** | Only `2`-fold `MetaplecticRepresentation` of `Sp` exists (`GL5/` = Hermitian class mass) |
| **Global Kuznetsov / relative trace formula** | **PARTIAL (no `Kuznetsov`/`RTF`)** | `24` live `JacquetRallis` unit-matching decls (`GlobalTheory.T.jacquetRallisUnitMatch_all_ranks`, `1,957` dom / `1,956` inner) + `1,444` Arthur/simple twisted `TraceFormula` decls |
| **Stepanov auxiliary-polynomial method** | **NOT FOUND (`0` hits)** | `Polynomial.hasseDeriv`'s `47` live callers (`30` project incl. `._proof_*` auxes, `17` Mathlib) are formal deformation / Ax–Sen / Frobenius lift bounds |

7. **Calibrated Signature-Matching Index (FLIRT) & Contract-Unfolding Lift:**
   - Separating the **16 systematic bulk folder→namespace remappings (`125,598` modules = `71.69%`)** cut Tier 1 alerts from **`117,065` (`66.8%`) → `20,692` (`11.81%`)** (`high` tier `27,832` → **`3,283`**, with **`84.21%`** kernel-verified domain-conflict precision on `extreme_outlier`).
   - Coarse kernel blueprint clustering (`outputs/flirt/clusters.json`) partitions all `1,468,414` live decls into **`141` clusters** (`2,099` edges), collapsing **`42.35%` boilerplate** (`846,496` effective core decls).
   - **100-cluster name-redacted evaluation (`0` identifier leaks across `23,358` tokens):** Adding 1–2-hop kernel contract unfolding slashed blinded `other_mixed` abstentions **`55.0% → 10.0%` (`-45.0 pp`)**, lifted blinded exact agreement on the `54` non-opaque control clusters **`48.1% → 63.0%` (`+14.8 pp`, top-2 `90.7%`)**, and resolved **`38/46` (`82.6%`)** of clusters that were opaque even *with* real names.

---

## 4. Core Dossier Index

| Document | JSON Twin (`outputs/decomp/`) | Focus |
|---|---|---|
| [`analysis/spine_and_diamond.md`](spine_and_diamond.md) | `spine_map.json` (`91` nodes) | `Main` → `allChi` → `everyCharacter`, `58,857` bridge, `331,598` shared diamond |
| [`analysis/pillar_theta.md`](pillar_theta.md) | `pillar_theta.json` (`95` nodes) | Pillar A (`543,325` decls, `37.0%`) — `HypsAlt` producer & consumer |
| [`analysis/pillar_galois.md`](pillar_galois.md) | `pillar_galois.json` (`323` nodes) | Pillar B (`95,102` decls, `6.5%`) — `Row0b`, étale cohomology, `tLiftK`, `recTExists` |
| [`analysis/pillar_window.md`](pillar_window.md) | `pillar_window.json` (`222` nodes) | Pillar C (`92,705` decls, `6.3%`) — `VWin` statement `0` opaque (`76` opaque proof nodes), Kato / `Sp(4)` / `U(3)` / patching |
| [`analysis/pillar_volume_lit.md`](pillar_volume_lit.md) | `pillar_volume_lit.json` (`115` nodes) | Pillar D (`80,720` decls, `5.5%`) & `195` `*_of_literature` theorems |
| [`analysis/tcb_and_contracts.md`](tcb_and_contracts.md) | `tcb_audit.json` | Layer 2 semantic TCB audit, `2,570`-def closure, `Gchi` dead-code proof |
| [`analysis/compute_and_deadcode.md`](compute_and_deadcode.md) | `compute_atlas.json` | All `28,904` zero-kernel files & complete `decide +kernel` inventory |
| [`analysis/deep_followup_audit.md`](deep_followup_audit.md) | *(prose audit)* | `Loc := Empty` / `η`, `ChainTied`/`BundleCondition`/`DefiniteSideCondition`, `remark.pdf` missing mechanisms, `dualAbelianScheme` |
| [`annotations/ai__decomp-phase4.jsonl`](../annotations/ai__decomp-phase4.jsonl) | *(pack `leanre.annot/1`)* | `128` signature-anchored declaration notes (`default_on: false`) |

---

## 5. Honest Caveats & What Remains Unread (`OPAQUE`)

- While the top-level **contracts, Horn edges, existence guards, and TCB closure** are now read and verified, **almost none of the inner proof bodies (`> ~30` lines inside leaf `thm` terms) have been read by a human mathematician**.
- Open questions for specialist review (e.g. for analytic number theorists inspecting candidate lemmas):
  1. Verifying `Base.IsGood` / `D7` / `FamP` step-by-step inside the `37,318`-decl `large_unramified_exponent_bundles_exist_alt` proof body (`StageU`).
  2. Comparing `UnitaryGroupThirdPlaceHypotheses` (all `131` distinct `GlobalTheory.Published.*` statements; `15` unfolded in detail here) one-by-one against standard literature.
  3. Determining whether a simplified Lean 4 version (once the community trims `28,471` unused modules, `38,194` `GlobalTheory.T.*` aliases, and dead bundle fields) drops straight from `17.37M` lines under automated structural diffing.
