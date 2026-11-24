# Top-Level Spine and Shared Diamond of the RH Proof

> **Target:** `Main` → `allChi` → `everyCharacter` (`1,468,414` live decls, `dom_tree = ALL`, pinned `40e56bab`, `solution.ndjson.zst` `5ea74b91…244e`) · **Blueprint:** `91` nodes, `143` edges, `23` Horn clauses
> **Conventions:** Headers are ≤1-line excerpts or English summaries; see [the analysis index](README.md) for tag definitions.

## Reproducing the Blueprint

For local setup, kernel database extraction, and CLI blueprint commands, see [the repository README](../README.md).

## 1. TL;DR

1. **[L]** All five headline theorems funnel through *one* Prop, `UpperTheory.EveryCharacter` (EveryCharacter.lean:13): *for every Dirichlet character χ and every s with Re s > 1/2, L(χ,s) ≠ 0 unless χ = 1 and s = 1* — stated purely with Mathlib objects. `allChi : EveryCharacter` dominates **1,409,557 / 1,468,414 = 96.0 %** of the live kernel graph.
2. **[L]** The remaining **58,857** live decls are **58,826 Mathlib/Lean decls + 31 project decls**; the 31 are exactly the Statement/bridge layer (Main, Statements, MainTheorems, CritLine, RhOfRight, HalfPlane, ClaimStrip, the EveryCharacter def). The bridge from EveryCharacter to RH / strip-GRH is the classical functional-equation reflection using only Mathlib lemmas ([S] standard).
3. **[L]** `everyCharacter` is a single modus ponens: `everyCharacter_of_row : Row0b(IsRecT) → EveryCharacter` applied to `galoisLocalGlobalStrong_recParameter : Row0b(recT)`, where `recT := fun h rc ↦ IsRecT h rc` (an alias). So the *whole* proof reduces to: **(B) Galois representations attached to regular algebraic polarized cuspidal automorphic representations over CM fields satisfying local–global compatibility (`Row0b`) ⟹ (A/C/D) GRH-right-of-1/2 for Dirichlet L-functions.**
4. **[L]** The dominator split under `everyCharacter` (1,409,556): `everyCharacter_of_row` **982,855** (66.9 % of live) · `galoisLocalGlobalStrong_recParameter` **95,102** (6.5 %) · **shared diamond 331,598** (22.6 %) spread over **110,898** dominator children. **Every one** of the 331,598 diamond decls is reachable from *both* branches (exact forward-closure check, §5) — the diamond is a shared lemma library, not a third argument.
5. **[L]** The "literature" layer is *not* an axiom: `OpenLiteratureStatements` (3 fields: `Row`, `RecTExists`, `Row`) is constructed inside `everyCharacter_of_row` as `⟨h, recTExists, h⟩` (MainConclusion.lean:7–8); of the 196 theorems (besides its 3 field projections) that reference `OpenLiteratureStatements`, only **14** transitively use any field of `O` (incl. the two top-level consumers); **182** ignore it and return a proved project theorem.

## 2. Decompiled pseudocode (top of the proof)

Schematic English, one line per declaration; `⟦n⟧` = dominator-subtree size in tree `ALL`; `←` = "proved by".

```text
── Main.lean (5 headline theorems; Statements.lean props use Mathlib only) ──────────────────────────────
[L] riemannHypothesis                   : RiemannHypothesis(Mathlib)            ← rhOfAll                    Main.lean:4
[L] riemannZeta_eq_zero_re              : RiemannZetaZerosOnLine                ← rhOfAll  (same term ⇒ defeq) Main.lean:6
[L] LFunction_ne_zero_of_half_lt_re     : DirichletLNonvanishingRightOfHalf     ← allChi   (body = EveryCharacter body) Main.lean:8
[L] LFunction_eq_zero_re                : DirichletLZerosOnLine (all χ, strip)  ← claimAll.2.1 = Claim.strip allChi   Main.lean:10
[L] LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine        ← critAll                    Main.lean:12
── bridge layer: 31 project decls outside allChi, Mathlib-only reasoning [S] ─────────────────────────────
[L] rhOfAll       ← rh_of_every allChi                                                   MainTheorems.lean:9
[L]   rh_of_every : EveryCharacter → RH  ← χ = trivial mod 1 (L(1,s)=ζ(s)) then rh_of_right  CritLine.lean:29
[L]   rh_of_right : (ζ≠0 on Re>1/2, s≠1) → RH  ← functional equation riemannZeta_one_sub, Γ/cos ≠ 0  RhOfRight.lean:5
[L] critAll       ← critLine allChi : primitive χ, zero in strip ⇒ reflect via completedLFunction_one_sub  CritLine.lean:11
[L] claimAll      ← ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩                       MainTheorems.lean:15
[L]   Claim.strip : HalfPlane → Strip  ← prim_zero (Euler factors ≠0) + prim_reflect (FE)   ClaimStrip.lean:59
[L]   Claim.zeta  : HalfPlane → Zeta   ← strip at N=1 + Gammaℝ zeros                       ClaimStrip.lean:75
── the waist ──────────────────────────────────────────────────────────────────────────────────────────────
[L] allChi : EveryCharacter ⟦1,409,557⟧ ← everyCharacter                                 MainTheorems.lean:7
[L] everyCharacter : EveryCharacter ⟦1,409,556⟧                                           MainConclusion.lean:10
      ← everyCharacter_of_row (galoisLocalGlobalStrong_recParameter)          -- Horn:  Row0b ∧ (Row0b → EC) → EC
[L]   ├─ (B) galoisLocalGlobalStrong_recParameter : Row0b recT ⟦95,102⟧          RowSrc.lean:6   → pillar_galois
[L]   │       recT := fun h rc ↦ IsRecT h rc                                       Development.lean:18 (alias)
[L]   │       ← galoisRepresentations_of_thetaLift ⟦90,962⟧, tLiftK ⟦4,104⟧
[L]   ├─ everyCharacter_of_row (h : Row0b IsRecT) : EveryCharacter ⟦982,855⟧     MainConclusion.lean:7
[L]   │    ← every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)
[L]   │    ├─ every_character_of_literature_of_vWin (O, hV : VWin) ⟦849,323⟧   EveryCharacterOfLiteratureOfVWin.lean:810
[L]   │    │    ← every_character_of_theta_integrals_local_matching
[L]   │    │         (published_results_eigen O) (published_results_first O)
[L]   │    │         (theta_integrals_agree_and_local_matching_of_literature O).1/.2
[L]   │    │         (topCovolSlim2_use_alt_alt …) (local_langlands_gl_recT_exists_of_literature O) hV
[L]   │    │    ├─ (A) every_character_of_theta_integrals_local_matching ⟦543,325⟧  → pillar_theta
[L]   │    │    │      Horn: UnitaryGroupThirdPlaceHypotheses ∧ ThetaLocalInputs ∧ ThetaIntegralsAgree ∧ LocalMatching
[L]   │    │    │            ∧ CovolumeBoundOfX ∧ RecTExists ∧ VWin → EveryCharacter              [inner: OPAQUE here]
[L]   │    │    ├─ (C) topCovolSlim2_use_alt_alt ⟦80,720⟧ : 15 curried premises → CovolumeBoundOfX → pillar_volume_lit
[L]   │    │    ├─ theta_integrals_agree_and_local_matching_of_literature ⟦14,173⟧
[L]   │    │    ├─ toroidalForFanKS ⟦7,185⟧, published_results_arithmetic ⟦7,105⟧, hsChain ⟦5,514⟧,
[L]   │    │    │  siegel_toroidal_integral_of_literature ⟦5,446⟧, canonicalAlgorithmRules_isCorrect ⟦5,400⟧, …
[L]   │    │    └─ (41,274 leaf children; 849,322 dominated below)
[L]   │    ├─ (D) vwin_of_row (Row0b IsRecT) : VWin ⟦92,705⟧                  VwinOfRow.lean:4 → pillar_window
[L]   │    │       ← automorphic_window_of_inputs (OpenImageCondition, BaseChangeIsobaricN, RowT) ⟦92,702⟧
[L]   │    └─ 11,655 further dominator children ⟦40,826⟧ (globalEulerChar_full 2,710, abelianDeRham 2,281,
[L]   │       harishChandraFinite 2,133, …)
[L]   └─ SHARED DIAMOND: 110,898 dominator children ⟦331,598⟧, every decl reachable from BOTH branches (§5)
```

Key headers (exact, ≤1 line):

- [L] `def UpperTheory.EveryCharacter : Prop` := ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1/2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → LFunction χ s ≠ 0 — EveryCharacter.lean:13. **READ** (all deps Mathlib).
- [L] `theorem UpperTheory.FinalTheorems.everyCharacter_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter` — MainConclusion.lean:7.
- [L] `theorem galoisLocalGlobalStrong_recParameter : UpperTheory.GalStar.Row0b recT` — RowSrc.lean:6.

## 3. The bridge layer — the 58,857 decls outside `allChi`

**[L]** `dom_trees.ALL.n_nodes − dom(allChi).subtree_size = 1,468,414 − 1,409,557 = 58,857.`
Composition (`decl_module.method`): 44,937 `unmatched:challenge_library` (Mathlib decls also in the challenge export), 8,057 `unmatched:external_private`, 5,832 `unmatched:library_or_external` — i.e. **58,826 Mathlib/Lean** — plus **31 project decls**:

| module | project decls |
|---|---|
| `Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip` | 6 (`factor_ne_zero`, `prim_zero`, `gamma_ne_zero`, `prim_reflect`, `strip`, `zeta`) |
| `Main` | 5 (headline theorems) |
| `Statements` | 5 (4 Props + `RiemannZetaZerosOnLine._proof_1`) |
| `…CharacterBoxes.HalfPlane` | 4 (`Claim.HalfPlane/Strip/Zeta` + aux) |
| `Formalism.GammaFactorNonvanishing.RhOfRight` | 3 (`rh_of_right` + 2 aux) |
| `Formalism.GammaFactorNonvanishing.CritLine` | 3 (`rh_of_every`, `critLine`, `gammaFactor_ne_zero`) |
| `Supplements.Kernels.MainTheorems` | 3 (`rhOfAll`, `critAll`, `claimAll`) |
| `…CharacterBoxes.EveryCharacter` | 2 (`UpperTheory.EveryCharacter` def + aux) |

**[L]** 58,822 of the 58,857 are also in the forward cone of `allChi` (shared Mathlib, hence dominated by the virtual root, which has 34,106 children); only **35** decls are reachable from the roots *without* going through `allChi`: the 29 bridge project decls (all of the 31 except the `EveryCharacter` def + its aux, which `allChi`'s own type uses) and 6 Mathlib decls only the bridge needs (`riemannZeta_one_sub`, `riemannZeta.eq_1`, `riemannZeta_def_of_ne_zero`, `HurwitzZeta.hurwitzZetaEven_zero`, `RiemannHypothesis` + its aux).
**[S]** Every bridge step is textbook: specialization to the trivial character mod 1, reduction of imprimitive to primitive characters via non-vanishing Euler factors for Re s > 0, and reflection through the (completed) functional equation. Verdict: **real, READ**; no project contract appears in the bridge except `EveryCharacter` itself.

## 4. The waist contracts (what `Row0b` actually asserts)

- [L] **`Row0b (Rc : RecNotion) : Prop`** (WeightsConjBis.lean:69; `Rc` is a section `variable`, so the header `def Row0b : Prop` hides it): ∀ CM number field E, Ω algebraic closure, prime l, ι : Q̄_l ≃+* ℂ, a ≥ 1, π : `CuspSub E a`, χ : `HChar (maximalRealSubfield E)`, `(CG.mk π).IsRegAlg` → `PolarizedPair π χ` → ∃ r : Gal(Ω/E) →* GL_a(Q̄_l), wt : ℤ, HT : (E →+* Q̄_l) → Multiset ℤ, `PropsB Rc π ι r wt HT`.
- [L] **`PropsB`** (WeightsConjBis.lean:54) fields: `cont` (r continuous), `ss` (`IsSSRep r`), `away` (for w ∤ l and every `rc` with `Rc h rc`, each local component σ of π at w gives `AwayB (wdOf h hl ι r) (rc σ)`; `AwayB x y` (WeightsConjBis.lean:26) = three fields: `dim` (equal `lpDim`), `tor` (`Tor y → y.mono0 → x = y`), `tame0` (under `IsQpBig`, `TmW y`, `Sqf y`, `y.mono0`: `x.mono0` and equal `charPol` on all degree-0 Weil elements)). [L] As stated, `AwayB` asks for full equality x = y only under `Tor y ∧ y.mono0`, otherwise only dimension and degree-0 characteristic polynomials — on its face weaker than full local–global compatibility (isomorphism of Frobenius-semisimplified WD representations; see [pillar_galois.md](pillar_galois.md) for `Tor`, `TmW`, `Sqf`), `weights` (HT multiset = infinitesimal character shifted by (a−1)/2), `weights_conj` (complex-conjugation symmetry with weight wt), `above` (crystalline-type conditions at places over l), …
- **[S] shape:** this is the statement "regular algebraic, polarized cuspidal π of GL_a over a CM field has an attached semisimple ℓ-adic Galois representation with the right Hodge–Tate weights and local–global compatibility away from l" (Harris–Taylor, Shin, Chenevier–Harris, Caraiani). **Status PARTIAL**: `CuspSub`, `IsRegAlg`, `PolarizedPair`, `IsSSRep`, `AwayB`/`AboveB` internals are analyzed in [pillar_galois.md](pillar_galois.md).
- [L] **`IsRecT rc := ∃ a ha, LawsT a ha rc`** (IsRecTOfIsRec.lean:76) with `LawsT` (line 55) = 12 fields: `dim, one, langlands, cusp, nu, absCentral, twist, central, dual, inj, depth, type`. [S] shape = characterizing properties of local Langlands for GL_n. [L] Observations: `twist/central/dual/inj/depth` are restricted to `Good` representations (lines 65–71, confirmed in source); there is no surjectivity field; `TypeLaw` is **OPAQUE** here.
- [L] **`RecTExists`** (line 78) := ∀ E Ω A w (h : IsPlaceOver A w), ∃ rc, IsRecT h rc; proved by `recTExists` (RecTExists.lean:20) — diamond root #35, only ⟦595⟧ dominated.
- [L] **`OpenLiteratureStatements`** (EveryCharacterOfLiteratureOfVWin.lean:215) : Prop with fields `caraianiLocalGlobalDual : One.M.Row`, `localLanglandsExists : Zero.LLC.RecTExists`, `galoisRepOfPolarizedPairLit : One.M.Row`; `One.M.Row := Row0b (fun h rc ↦ IsRecT h rc)` (RecT.lean:6). Instantiated, not assumed (§1.5). Field users: `localLanglandsExists` → `local_langlands_recT_exists_of_literature`; `galoisRepOfPolarizedPairLit` → `pair_u_of_literature`; `caraianiLocalGlobalDual` → `carU_local_global_of_literature`, `literature_automorphy`. See also [pillar_volume_lit.md](pillar_volume_lit.md): one slot (`published_results_eigen.siegelEisensteinSimplePole`, `UnusedSlot72`) is literally `Prop := True` (EveryCharacterOfLiteratureOfVWin.lean:505) — **[L]** a degenerate slot, harmless only because nothing downstream needs content from it.
- [L] **`VWin := ∀ ψ : PChar, VWinAt ψ 401`** (ExistsPageN.lean:49) — quantitative window statement; `PageN`, `WinPair`, `VAt` **OPAQUE** here (unfolded in [pillar_window.md](pillar_window.md)).

## 5. The 331,598-decl shared diamond

**What it is, exactly.** [L] `everyCharacter` has **110,900** dominator children; removing the two branches leaves **110,898 diamond roots** whose subtrees total **331,598** (= 1,409,555 − 982,855 − 95,102). A decl is dominated by `everyCharacter` but by neither branch iff it is reachable from `everyCharacter` along ≥ 2 internally-distinct routes. Exact forward closures over all 114,115,002 kernel edges (`leanre/decompile/spine.py: diamond_analysis`):

| cone | size |
|---|---|
| reach(`everyCharacter_of_row`) | 1,373,275 |
| reach(`galoisLocalGlobalStrong_recParameter`) | 485,089 |
| reach(row) ∩ reach(gal) | 389,987 |
| reach(`UpperTheory.EveryCharacter` def, the type) | 51,574 |
| **diamond decls in reach(row) ∩ reach(gal)** | **331,598 / 331,598 (100 %)** |

So **every** diamond decl is used by both the Galois engine (B) and the row ⟹ EveryCharacter engine (A/C/D); none is pulled in only through the statement type. [M] Analogy: a static library linked into two executables; a dominator tree cannot attribute it to either. *Where it breaks:* "shared" here is reachability, not "load-bearing in both" — a diamond lemma may be essential on one side and incidental on the other.

**Composition** [L]: 210,398 project decls (63.4 %) + 119,413 Mathlib/Lean (36.0 %) + 1,787 project auto-instances/attr/other; kinds 280,147 thm / 49,561 def / 1,856 inductive / 34 opaque. Module folders: Mathlib 103,568 + external-private 15,845; `Development.AbelianVarietyTheory` 85,659; `Development.WeilBound` 34,534; `Development.AutomorphicSpectrum` 26,725; `Development.AutomorphicArithmetic` 16,240; `GroundTheory.AutomorphicForms` 12,096; … Namespaces: `GlobalTheory` 116,854; `PositivityTheory` 31,957; `GroundTheory` 30,170; `_private` 27,409; `CategoryTheory` 16,878; `UpperTheory` 7,371.
Of the 387 `GlobalTheory.Published.*` statement defs, **100 sit in the diamond**, 276 under `everyCharacter_of_row`, 11 under the Galois branch.

**Root-size distribution** [L]: 81,857 roots are singletons, 11,391 have size 2, …; only **18 roots ≥ 1,000** and **74 ≥ 300**. The diamond is a very wide, shallow fan of reusable lemmas — no single hidden third argument.

**Top 60 diamond roots** (verdict = statement *shape* vs the named classical result; `PARTIAL` = project predicates in the statement not unfolded to Mathlib; full per-node summaries in `spine_map.json` → `nodes[group=diamond]`). Ranks 1–60 were inspected from headers and marked `PARTIAL` where inner predicates were not unfolded.

| # | declaration | ⟦dom⟧ | anchor | statement gist | verdict / status |
|---|---|---|---|---|---|
| 1 | `UpperTheory.V.Z.GSp4Splitting.coreG` | 3,421 | CoreG.lean:17 | `: CoreG` (HighestVectorsRegularLine.lean:56): for antitone λ ∈ ℤ^n, K-module E, operator T with IsLefK, and a unitary-group module σ with IsCoreMod, the trace of flipA on the (finite-dim, nonzero) invariants equals ±2^n. Archimedean representation-theory… | unknown / PARTIAL |
| 2 | `GlobalTheory.T.zarhinGeometric_of_semistableReduction` | 2,519 | ZarhinGeometricOfSemistableReductionStatement.lean:14 | Conditional: Published.SemistableReductionSt → ZH.ZHGeoSt. Hypothesis (SemistableReductionSt.lean:15) = for every polarized AV over a finite K/ℚ_p there is a finite K'/K and a semi-abelian group scheme over O_K' whose generic fibre is the pullback [S:… | unknown / PARTIAL |
| 3 | `GlobalTheory.RgGu.Leib.Hand.leibnizOrd` | 2,398 | HighestDerivProd.lean:23 | `: LeibnizOrd k` (LeibnizOrd.lean:36): for a non-archimedean local field k and smooth π₁, π₂, the ℓ-th derivative of π₁×π₂ has a filtration whose graded pieces are (twisted) products of derivatives of π₁ and π₂. [S] = the Bernstein–Zelevinsky Leibniz rule… | real / PARTIAL |
| 4 | `UpperTheory.HeckeLevelFrameExistence.frameEx_of_fin` | 2,355 | FrameExOfFin.lean:43 | USide → CandFin → FrameEx. USide (SimpleTwistedTraceFormulaStable.lean:239) is a finiteness/exhaustion statement for automorphic reps of unitary groups of given weight and level; FrameEx asks Nonempty (RunFrame F₀ T). Project-internal 'frame' machinery, not… | unknown / OPAQUE |
| 5 | `GlobalTheory.deRham_potentiallySemistable` | 2,251 | DeRhamPotentiallySemistable.lean:11 | `: Published.DeRhamPotSemistable` (DeRhamPotSemistable.lean:13): every continuous finite-dim ℚ_l-representation of G_K that IsDR is IsPst. [S] = Berger's p-adic monodromy theorem. 5 users on both sides (Gal.Int.Inp.pst, Gal.TP.Sub.pstOfDR,… | real / PARTIAL |
| 6 | `GlobalTheory.T.jacquetRallisUnitMatch_all_ranks` | 1,957 | JacquetRallisUnitMatchAllRanksStatement.lean:6 | `: ∀ r, UnitMatch r` (FourierMatch.lean:158): for unramified E/F, Match M (unitG r F) (unitU r F E). [S] shape = Jacquet–Rallis fundamental lemma for the unit element (Yun; Beuzart-Plessis). Match/Meas not unfolded. | unknown / PARTIAL |
| 7 | `UpperTheory.ConvolutionTheory.GM.gm_of_bcfl` | 1,946 | GmOfBcfl.lean:5 | Conditional BCFLUnit → GM. BCFLUnit (InvTransposeGLInvTransposeGL.lean:263) = base-change fundamental lemma for the unit of the Hecke algebra in unramified cyclic E/k with normalized Haar measures [S: Kottwitz/Clozel–Labesse shape]; discharged by… | unknown / PARTIAL |
| 8 | `UpperTheory.BaseChangeIdentities.FrameWordIdentity.frameBound` | 1,841 | FrameBound.lean:42 | `: FrameBound` — ∀ ReadLimit, DiagAlg, CM E unramified, automorphic π, frames F₀/F: (F.toGenIn hD h).Bound. Project-internal, not unfolded. | unknown / OPAQUE |
| 9 | `PositivityTheory.AdelicQuotientData.rsPole` | 1,754 | JacquetShalikaRigidity.lean:10 | `: RSPole` (CauchyLoc.lean:46): for normalized cuspidal π (GL_m), π' (GL_k) over totally complex E, partial Rankin–Selberg L^S(s,π×π') has (s−1)·ZS·L^S holomorphic on Re s>0 with ZS non-vanishing on the line, and Z(1)=0 unless (m,π) = (k,π'). [S] =… | real / PARTIAL |
| 10 | `PositivityTheory.RgBcC.wave_existence_speed_multiplicity` | 1,545 | WaveFinal.lean:15 | `: WaveEx ∧ WaveSpeed ∧ KerEx ∧ MultAlg` (IsMultZero.lean:106–117): existence of solutions of a wave equation on GL_n(ℂ)-modules, finite propagation speed, existence of compactly supported multiplier kernels, and the multiplier algebra laws. 14 direct users.… | unknown / PARTIAL |
| 11 | `GroundTheory.Arith.SchemeCoh.finite_H_of_isProper` | 1,509 | ProperFiniteness.lean:23 | : X proper over Spec A (A Noetherian), F coherent (IsCoherent = quasi-coherent ∧ finite on affines, TwistingSheaf.lean:18) → H^p(X,F) is a finite A-module. [S] = EGA III 3.2.1. Sheaf.H is a project definition (not unfolded). | real / PARTIAL |
| 12 | `GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations` | 1,375 | CrystallineSmoothLiftOfRelations.lean:52 | `: Published.CrystallineSmoothLift` (BijectiveCechDeRhamComparisonDegreeOne.lean:130): ∃ isomorphisms H¹,H² (crystalline-type cohomology of `Data`) ≅ de Rham HH¹,HH², cup-product and pull-back compatible. `Data` not unfolded, so which comparison theorem this… | unknown / PARTIAL |
| 13 | `GlobalTheory.dualAbelianScheme` | 1,363 | DualAbelianSchemeExistsBiduality.lean:29 | `: Published.DualAbelianScheme` (ExistsCrystalPairing.lean:25): every abelian scheme A/S (S : Scheme.{0} arbitrary; IsAbelianScheme = commutative, smooth, proper, geometrically connected group object) has B, P : LB(A×B) with B abelian, same relative… | unknown / PARTIAL |
| 14 | `PositivityTheory.Rg.BcB.CV.ellFormula2J` | 1,286 | EllFormula2J.lean:12 | `: EllFormula2J` (QuotIntegralZero.lean:46): ∃ C ≥ 0, for fundamental domains of GL_a(E), GL_b(E) and test functions of radius r with C(1+r) ≤ τ, the τ-cut trace cutTr2 equals the elliptic sum ellSum2 (a trace-formula truncation identity). cutTr2/ellSum2 not… | unknown / PARTIAL |
| 15 | `PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible` | 1,256 | BernAll.lean:27 | `: Published.BernsteinUnitaryProductIrreducible` (BernsteinUnitaryProductIrreducible.lean:10): smooth irreducible unitarisable π₁ of GL_r(k), π₂ of GL_t(k) ⇒ prod₂ π₁ π₂ irreducible. [S] = Bernstein (1984). prod₂/IsUnitarisable not unfolded. | real / PARTIAL |
| 16 | `CategoryTheory.IsGrothendieckAbelian.enoughInjectives` | 1,208 | — | Mathlib/Lean library declaration (ground; not authored in the RH project). | real / READ |
| 17 | `GlobalTheory.T.exists_degenerationData_uniformisation_of_torsionCount` | 1,151 | ExistsDegenerationDataUniformisationOfTorsionCouStatement.lean:17 | Conditional: (torsion count #A[n] = n^{2g} over alg. closed fields) → Laws → Laws2 → for every HidaSetting there are degeneration data D and a uniformisation U matching it. Laws / Laws2 (GlobalSectionsRankAlgClosed.lean:187, SecBaseChangeAnySt.lean:73) are… | unknown / PARTIAL |
| 18 | `GlobalTheory.automorphicFormsFiniteGL` | 1,078 | AutomorphicFormsFiniteGL.lean:8 | `: Published.AutomorphicFormsFiniteGL` (ExistsSpanFormsNeBot.lean:23): for totally complex E, open L ⊂ GL_a(A_f), continuous finite-dim K∞-type ρ and infinitesimal character c, span(forms L ρ c) is finite-dimensional. [S] = Harish-Chandra finiteness… | real / PARTIAL |
| 19 | `PositivityTheory.Rg.BcB.G8.global_character_holds` | 939 | GlobalCharacterHolds.lean:6 | `: G4` (IsTransl.lean:82): ∃ c ≠ 0 relating ellS-type global character sums for GL_a×GL_b over unramified CM E. Not unfolded. | unknown / OPAQUE |
| 20 | `HodgeLocalDeRhamField.HLdR.field_outright` | 879 | Outright.lean:7 | `: Published.HeckeLAdicCharacterDeRham` (HeckeLAdicCharacterDeRham.lean:11): the ℓ-adic character μ attached to an algebraic Hecke character χ of type n is de Rham at every place above l with HT jumps {−n∘ι∘τ}. [S] = Serre/Weil + Fontaine.… | real / PARTIAL |
| 21 | `PositivityTheory.Rg.Sw.HSt.holLeadB` | 870 | HolLeadB.lean:9 | Proves PositivityTheory.SiegelWeilFormula.HolLead: if the j-th derivative at s₀ of an analytic Eisenstein-style family Ê(s,g) vanishes against all singular Schwartz test functions ψ (IsSingTest), then y ↦ ∂_s^j Ê(s₀, g·ι(y)) satisfies the holomorphic… | real / PARTIAL |
| 22 | `PositivityTheory.Rg.Cz.kType_holds` | 839 | KTypeHolds.lean:27 | Proves PositivityTheory.Rg.Cz.KType: for a (𝔤,K)-module M with GL_n relations (IsGK, IsKD), integral quantum-determinant infinitesimal character l, and nonzero Whittaker functional ℓ (IsWh), there exists s : ℤ and a nonzero K-invariant alternating tensor η… | real / PARTIAL |
| 23 | `GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis` | 805 | UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallisStatement.lean:8 | Deduces both Jacquet-Rallis fundamental-lemma identities on lattices/orbital sums (UnitLemmaLie and UnitLemmaGroup) from the rank-general Fourier-matching statement ∀ r, UnitMatch r. | wrapper / PARTIAL |
| 24 | `GlobalTheory.CompanionTheory.SiegelRed.siegelCore` | 803 | SiegelSetUnitary.lean:17 | Proves PositivityTheory.ThKR.SiegelCore: constructs compact K, Ω ⊆ minParOne, and c > 0 for an adelic unitary group GAd σ J with Witt frame (X,Y), establishing Iwasawa decomposition, GoodPosition, Siegel-set fundamental domain coverage, height bounds, and… | real / PARTIAL |
| 25 | `PositivityTheory.Rg.Sw.lc_of` | 800 | LcOf.lean:6 | Proves FFT → LC: derives the Howe-duality / Capelli-operator vanishing theorem LC (any linear functional killing differential operators hOp ε c a b vanishes on the null-cone ideal NullSec ε c) from the unitary-group First Fundamental Theorem FFT. | real / PARTIAL |
| 26 | `GlobalTheory.PreStabU.geomURat_eq_geomU` | 793 | UnitaryGeometricSideSeparableTest.lean:453 | For an unramified CM field E, section S of places, weight lam, level K', and test function f, equates the rational-point geometric sum geomURat lam (∏_{w∈S} twOrb ...) with the adelic elliptic orbital-integral sum geomU S lam f. | real / PARTIAL |
| 27 | `PositivityTheory.SiegelWeilFormula.Fin.whitGenEq` | 745 | SiegelWeilStdOf.lean:46 | Proves Gen.WhitGenEq := WhitGenX (fun M n => M = n ∧ 1 ≤ M) False 2: equal-rank (M = n ≥ 1) unitary Siegel-Weil identity equating the holomorphic value at z = 0 of the regularized Whittaker integral to 2 * meanC (Tamagawa number 2) of the theta integral over… | real / PARTIAL |
| 28 | `UpperTheory.V.Z.Inf.genFE` | 733 | GenFE.lean:13 | Proves the global Godement-Jacquet functional equation for factorizable matrix coefficients of cusp forms on GL_n(𝔸_K) (n ≥ 2): the completed L-function Λ(s) is entire and satisfies Λ(1-s) = c' * archZeta(φ̂) * (∏_{v∈S} zetaIntegral(Φ̂_v)) * dualPartialL S π… | real / PARTIAL |
| 29 | `UpperTheory.V.Z.GSp4Splitting.lowIso2` | 704 | PartSum.lean:82 | Proves LowIso: if a unitary (𝔤,K)-module V with infinitesimal character infOf lam (IsLoc) contains a nonzero K-highest-weight vector at weight ν with m0 lam - ν in the positive root cone (inCone), then the K-isotypic component isoSp σ E in V for a Lefschetz… | real / PARTIAL |
| 30 | `GlobalTheory.SS.exists_neutral_group_model` | 699 | ExistsNeutralGroupModel.lean:18 | Over a strictly Henselian DVR (R, K) (SH R K), given a projective abelian scheme A over K (IsAbelianScheme A, IsProjBy A.hom), constructs a smooth separated quasi-compact R-model G with commutative group scheme structure SmConn G.Y such that some power c ≥ 1… | real / PARTIAL |
| 31 | `GroundTheory.Automorphic.IsExpLieAlgebra.exists_kernel_eq_conv_of_aeval_laplacian` | 664 | GKStableConv.lean:17 | Reproducing-kernel theorem for a Lie subgroup G ⊆ 𝔸ˣ (IsExpLieAlgebra G 𝔤): for any monic positive-degree polynomial P and neighborhood U of 1, there exists smooth compactly supported κ with tsupport κ ⊆ U such that every smooth f with P(Δ) f = 0 satisfies… | real / PARTIAL |
| 32 | `GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers` | 626 | AbelianSchemeHomLiftingNilpotentDividedPowers.lean:19 | Proves GlobalTheory.Published.AbelianLifting: Grothendieck-Messing crystal lifting for abelian schemes (LiftObj: lifting along nilpotent PD thickening R ↠ R₀ corresponds to admissible Hodge filtrations in HdR) and homomorphisms (LiftHom: unique lift… | real / PARTIAL |
| 33 | `PositivityTheory.RgUd.T.Final.thmT` | 616 | LocStep.lean:32 | Proves PositivityTheory.RgUd.ThmT k (for characteristic-zero nonarchimedean local field k): any distribution ξ on C_c^∞(M_n(k) × k^n) invariant under Z_G(Z) (Z reduced commutative subalgebra of M_n(k)) and supported on Z_M(Z) × k^n vanishes on all functions… | real / PARTIAL |
| 34 | `PositivityTheory.SiegelWeilFormula.Gunr.locC` | 597 | CFinal.lean:22 | Proves PositivityTheory.SiegelWeilFormula.Gunr.LocC: evaluates the local unramified nonarchimedean Siegel-Weil Whittaker integral ∫ whI ∂νv under GoodLoc (self-dual lattice, unimodular J,T, unramified quadratic extension with sign ε) for Re(z) > n^2 as… | real / PARTIAL |
| 36 | `PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.separation_holds` | 582 | SeparationHolds.lean:12 | Proves Sep4: for fixed K_∞-type W and finite-adelic level K, finds uniform finite families Ω(M), Θ(M) such that any stable IsAutForm-submodule U with NonPos, CentIm, and simple infinitesimal character generated by TypeB K W vectors maps equivariantly and… | real / PARTIAL |
| 37 | `UpperTheory.ConvolutionTheory.Sph.ramSph` | 571 | QuadLift.lean:10 | Proves UpperTheory.ConvolutionTheory.Sph.RamSph: for a prime-degree Galois extension M/K of totally complex number fields and cuspidal π, P related by WeakBC, any Satake parameter B of π at w ∩ 𝓞_K lifts to a Satake parameter B of P at ramified places w of M. | real / PARTIAL |
| 38 | `PositivityTheory.Rg.Rs.ascSeed_holds2` | 538 | AscSeedHolds2.lean:11 | Proves AscSeed := AscAll ∧ Clause3Asc (Moeglin-Waldspurger residual-spectrum seed): every discrete automorphic representation V with regular integral slice embeds into parabolic induction of a unitary cuspidal π twisted by Speh exponents (AscEmb), and its… | real / PARTIAL |
| 39 | `GroundTheory.Automorphic.ContragredientTranspose.rank_whittaker_le_one` | 516 | ContragredientTranspose.lean:77 | Proves Shalika's local Whittaker multiplicity-one theorem: for any irreducible admissible representation π of GL_n(F) over a nonarchimedean local field F and nontrivial continuous additive character ψ₀, Module.rank ℂ (equivariantFunctionals π psiN(ψ₀)) ≤ 1. | real / PARTIAL |
| 40 | `GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup` | 478 | UnitaryGroupFiniteVolume.lean:8 | Proves FinVol F E σ M J: for any CM extension E/F and nondegenerate Hermitian matrix J of size M, Haar measures μ on U(J)(𝔸_F) and fundamental domains 𝓕 for U(J)(F) exist and satisfy μ(𝓕) < ⊤. | real / PARTIAL |
| 41 | `CompanionTheory.RgGu.segmentRepresentation` | 474 | SegmentRepresentation.lean:9 | Proves GlobalTheory.Published.SegmentRepresentation: over a nonarchimedean local field k, for any irreducible cuspidal σ of GL_d(k) and l ≥ 1, the parabolic induction multiProd (σ, σ\|det\|, …, σ\|det\|^{l-1}) has a unique irreducible subrepresentation S,… | real / PARTIAL |
| 42 | `PositivityTheory.Rg.BcB.E2.orthogonal_keeping_holds` | 473 | OrthogonalKeepingHolds.lean:37 | Proves E.OrthogonalKeepingOperator: spectral approximation on L^2(H(F)\H(𝔸))^ι producing continuous, left-invariant, polynomially-weighted L^2 approximate eigenfunctions f_k for a countable *-algebra subset C, while remaining orthogonal to a given sequence… | real / PARTIAL |
| 43 | `GroundTheory.ProfCoh.card_cohomology_mul_div_eq` | 463 | EulerCharGaloisOfCardEq.lean:97 | Proves Tate's local Euler characteristic formula over a nonarchimedean local field K: for a finite discrete Gal(K_sep/K)-module M with (\|M\| : K) ≠ 0, \|H^0(M)\| * \|H^2(M)\| / \|H^1(M)\| = \|𝒪_K / (\|M\|)\|^{-1}. | real / PARTIAL |
| 44 | `PositivityTheory.Rg.BcB.SpectralAccumulation.eFinal_of` | 452 | EFinalOf.lean:11 | Proves Sep4 → FinDisc → LimVec → EFinal: combines tree separation, finite discreteness of bounded-infinitesimal-character automorphic forms, and limit extraction to show converging Hecke-eigenfunction tuples yield a nonzero limit in pairSpace s₁.space… | real / PARTIAL |
| 45 | `PositivityTheory.SiegelWeilFormula.Fin.whitGenLow` | 446 | SiegelWeilStdOf.lean:49 | Proves Gen.WhitGenLow := WhitGenX (fun M n => M < n ∧ 1 ≤ M) True 0: lower-rank (1 ≤ M < n) Siegel-Weil vanishing identity showing the regularized Whittaker integral has holomorphic value 0 at z = (M - n)/2 when P = 1 and signs ε are uniform. | real / PARTIAL |
| 46 | `GlobalTheory.CongMatch.match_principal_congruence_inert` | 442 | CongruenceSubgroupIndicatorWeight.lean:41 | Proves local orbital-integral matching (Match n a b w 1) at an inert non-split place w of an unramified CM field E between the indicator of the principal congruence subgroup K(w^k) ⊆ U(n) and (-q_w^{1/2})^{-kab} times the pullback indicator of K(w^k) along… | real / PARTIAL |
| 47 | `GlobalTheory.T.theta_measure_nonzero_vectors_bound` | 433 | ThetaMeasureNonzeroVectorsBoundStatement.lean:7 | Bounds the theta-measure (thetaMeas) of nonzero rational vectors X ∈ E^M with denominator dividing N (N·X_fin ∈ latV) and archimedean norm ≤ r by ENNReal.ofReal(C * (r^{[F:ℚ]M} + r^{2[F:ℚ]M})) for M ≥ 3. | wrapper / PARTIAL |
| 48 | `GlobalTheory.FlagBase.SiegelStep.glVol_step` | 418 | GlNormOneAdelicQuotientVolumeSiegelStep.lean:214 | Inductive volume recursion for GL_j(𝔸_E) over a totally complex number field E (j ≥ 2): if glVol E (j-1) < ⊤ then glVol E j = glVol E (j-1) * (vInv E)^{fDeg E * (2j-1)} * ζ_E(j). | real / PARTIAL |
| 49 | `PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound` | 412 | JacquetShalikaBound.lean:77 | Proves GlobalTheory.Published.JacquetShalikaBound: for any unitary cuspidal automorphic representation π : CG E a (E totally complex) and any place w with Satake parameters B (π.HasSat w B), every α ∈ B satisfies q_w^{-1/2} < \|α\| < q_w^{1/2}. | real / PARTIAL |
| 50 | `AlgebraicGeometry.isSheaf_type_propQCTopology_iff` | 403 | — | Mathlib/Lean library declaration (ground; not authored in the RH project). | real / READ |
| 51 | `GlobalTheory.SS.semistableReductionSt` | 403 | SemistableReductionPpavPadicField.lean:19 | Proves GlobalTheory.Published.SemistableReductionSt: every principally polarized abelian variety P over a finite extension K/ℚ_p acquires a semi-abelian group-scheme model G (IsSemiAbelian G, with torus-extension fibers over algebraically closed points) over… | real / PARTIAL |
| 52 | `GlobalTheory.GLq.ResCuspProd.main` | 398 | HarishChandraRestrictionCuspidalProductSumSubset.lean:226 | Proves the Mackey/Harish-Chandra restriction formula for parabolic induction of cuspidal characters of GL_n(𝔽_g) (g prime): res a b (hcL L (a+b)) evaluates to the sum over subsets I of L with degree sum a of hcL(I, a) * hcL(Iᶜ, b). | real / PARTIAL |
| 53 | `PositivityTheory.Rg.Bc.ArchbcB.B.m1` | 391 | ArchimedeanBaseChangeFirst.lean:63 | Proves PositivityTheory.Rg.Bc.ArchbcB.B.M1: base change fundamental lemma for the unit element of the spherical Hecke algebra at inert non-split places w of an unramified CM field E (matching 1_{KL n w} with 1_{KGL a × KGL b}). | real / PARTIAL |
| 54 | `PositivityTheory.SiegelWeilFormula.SwLocFin.locFinX` | 381 | LocFin2.lean:8 | Proves PositivityTheory.SiegelWeilFormula.Gen.LocFinX: for any Schwartz-Bruhat Φ_v with continuous orbital-density function g on regular Hermitian T, the local nonarchimedean Whittaker integral ∫ whI ∂νv converges for Re(z) > t and extends to an entire… | real / PARTIAL |
| 55 | `GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses` | 374 | HeckeTraceWeightFormsEqDimMulRationalClassesStatement.lean:8 | Equates the trace of the Hecke operator hop S K' f on algebraic-weight automorphic forms forms S lam K' of a definite unitary group to dimW lam * geomURat lam (twOrb ...), assuming separable support at some w ∈ S. | wrapper / PARTIAL |
| 56 | `UpperTheory.Gal.InertialTypesAlt.G.varTrace` | 372 | VarTrace.lean:20 | Proves UpperTheory.Gal.InertialTypesAlt.G.VarTrace: at a non-split place v of a prime-degree cyclic Galois extension E/F, for local components τ, τ' of a WeakBC-related Galois-invariant cuspidal pair (π, P), matching test functions φ, f with f supported in… | real / PARTIAL |
| 57 | `PositivityTheory.Groth.grothendieckRingPolynomial_of_seg` | 371 | GrothendieckRingPolynomialOfSeg.lean:8 | Proves GlobalTheory.Published.SegmentRepresentation → GlobalTheory.Published.GrothendieckRingPolynomial: derives the Bernstein-Zelevinsky isomorphism GrothGL k ≃+ MvPolynomial (Segment k) ℤ (multiplicative under parabolic induction prod₂ and sending segment… | real / PARTIAL |
| 58 | `GlobalTheory.grothendieckRingPolynomial_outright` | 370 | GrothendieckRingPolynomialOutright.lean:9 | Proves GlobalTheory.Published.GrothendieckRingPolynomial unconditionally by applying grothendieckRingPolynomial_of_seg (#57) to segmentRepresentation (#41). | real / PARTIAL |
| 59 | `PositivityTheory.Rg.Tf.Loc.bcflUnit` | 370 | BcflUnit.lean:30 | Proves PositivityTheory.Rg.Tf.Loc.BCFLUnit (Arthur-Clozel base change fundamental lemma for the unit element): for an unramified cyclic Galois extension E/k of char-0 nonarchimedean local fields, twOrbIntegral(1_{GL_n(𝓞_E)}, δ) = orbIntegral(1_{GL_n(𝓞_k)},… | real / PARTIAL |
| 60 | `PositivityTheory.RgBcC.cxData_model` | 357 | CxDataModel.lean:10 | Constructs an explicit Hilbert-space Clifford/Weyl model (lefE, lefFr, lefε, lefι, lefS, lefΓ, lefT) satisfying all axioms of CxData lam for any antitone lam : Fin n → ℤ (smooth GL_n(ℂ)-action extending U(n)-module, CAR relations, Dirac-like involution T,… | real / PARTIAL |

**Patterns worth a skeptic's attention** [L]:
- *Conditional + discharge.* Several big roots are implications whose premises are named "published" statements, discharged elsewhere by proved theorems: `zarhinGeometric_of_semistableReduction : SemistableReductionSt → ZHGeoSt` (premise proved by `GlobalTheory.SS.semistableReductionSt`, rank 51); `gm_of_bcfl : BCFLUnit → GM` (premise proved by `bcflUnit`, rank 59); `grothendieckRingPolynomial_of_seg` + `_outright` (57/58).
- *Hypothesis bundling.* `exists_degenerationData_uniformisation_of_torsionCount` takes `Laws` and `Laws2`, Prop-structures bundling 14 + 4 named statements (GlobalSectionsRankAlgClosed.lean:187, SecBaseChangeAnySt.lean:73); discharged in `exists_degData_unif_unconditional`. Bundles are not axioms, but each field is a separate obligation to audit (see [tcb_and_contracts.md](tcb_and_contracts.md)).
- *Re-export wrappers.* Ranks 23, 47, 55 (`*Statement.lean`) are 1-child re-exports of internal theorems.
- *Unused hypotheses / vacuous switches.* `geomURat_eq_geomU` binds its separability premise as `_` (UnitaryGeometricSideSeparableTest.lean:458 — the statement is stronger than needed, not weaker); `WhitGenEq := WhitGenX (…) False 2` turns the `vac → …` premise off (WhitGenLowOf.lean:171).
- *Scope restrictions.* `automorphicFormsFiniteGL` and `rsPole` are stated for totally complex E only; `LawsT` restricts five laws to `Good` reps.
- *Follow-up note:* `dualAbelianScheme` asserts a dual abelian **scheme** with Poincaré bundle for every abelian scheme over an arbitrary `S : Scheme.{0}` (ExistsCrystalPairing.lean:25). [S] Classically, over a general base the dual is first obtained as an algebraic space (Faltings–Chai I.1); a scheme-valued statement for every S is at least as strong as the standard literature, so `LB` / `IsDual` were unfolded in [deep_followup_audit.md](deep_followup_audit.md) and [adversarial_cohomology_recheck.md](adversarial_cohomology_recheck.md).

## 6. OPAQUE register (unfolded in pillar dossiers)

Inner predicates of: `Row0b`/`PropsB` (`CuspSub`, `IsRegAlg`, `PolarizedPair`, `IsSSRep`, `AwayB`, `AboveB`), `LawsT.type` (`TypeLaw`), `IrrGL`, `WD`; pillar heads `every_character_of_theta_integrals_local_matching` (A), `topCovolSlim2_use_alt_alt` (D), `VWin`'s `PageN/WinPair/VAt` (C); diamond predicates listed per node in `spine_map.json` (`opaque_inner`, and the top-level `opaque` array). These are covered in [pillar_galois.md](pillar_galois.md), [pillar_theta.md](pillar_theta.md), [pillar_volume_lit.md](pillar_volume_lit.md), [pillar_window.md](pillar_window.md), and [tcb_and_contracts.md](tcb_and_contracts.md).

## 7. Tool: `leanre decompile` (`leanre/decompile/`)

| command | what it gives |
|---|---|
| `contract <Name> [--body] [--json]` | exact header, namespace, in-scope `variable` binders, structure/class fields, inductive ctors; `--body` only for def/abbrev; projections resolved to the parent field |
| `unfold <Name> --depth k` | recursive contract tree (thm → type edges; def/structure → type+value edges) down to Mathlib ground deps |
| `horn <Name> [--graph]` | Horn clause: hyps (binders + curried premises) ∧ direct lemmas → concl, from kernel type/value edges + header |
| `dom <Name\|ROOT>` / `path` / `node` / `search` | dominator spine, idom chain, schema-v1 node skeleton, name search |
| `validate <json…>` | `leanre.decomp/v1` validator (ids checked against kernel.db) |
| `spine-map` | regenerates `outputs/decomp/spine_map.json` (diamond/outside/literature stats included) |
