# Pillar A — "Theta-lift / integral matching / definite side" (`543,325` decls, 37.0%)

> **Target:** `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`543,325` decls, `37.0%` of live graph; pinned `40e56bab`, `solution.ndjson.zst` `5ea74b91…244e`, `dom_tree = ALL`) · **Blueprint:** `outputs/decomp/pillar_theta.json` (`leanre.decomp/v1`)
> **Conventions:** Anchors are paths relative to `data/rh_mirror/` followed by `:line` (bare `:N` continues the prior file); see [the analysis index](README.md) for tag definitions.

---

## 0. Findings first

1. **The pillar is one implication with a 46-field record in the middle.** `[L]`
   `nonempty_hyps_definite_side_of_closed_bound` (451,610 decls) *produces* an inhabitant of the record `GlobalTheory.Fc.HypsAlt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22`, 46 fields, `Type 1`); `every_character_of_green_v_win` (23,523 decls) *consumes* it and returns `UpperTheory.EveryCharacter`. The root theorem `every_character_of_theta_integrals_local_matching` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69-73`) is a 3-line term gluing the two.
2. **No theta lift, automorphic form or unitary group is *defined* at the level where the proof is assembled.** `[L]` The working objects are fields of a project record `Formalism.BasicNotions.D7` (135 fields, 11,475-node type, fan-in 155,523; `src/Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:76`). Its "automorphic forms" are functions `cls i → Y i → ℂ` on **abstract types** `cls : ℕ → Type`, `Y : ℕ → Type`, and its "lifts" are abstract linear maps `unf` (`ColumnChain`, `src/Formalism/LocalRingCardinality/DataKernels.lean:14`). The number fields, rings of integers, Hermitian spaces and lattices in the record *are* genuine Mathlib objects. So: **abstract record with concrete carriers**, tied together by predicates. Whether `cls i` is faithfully the class set of a definite unitary group is `OPAQUE` in our reading (§4).
3. **Genuine adelic theta integrals do exist in the pillar's inputs.** `[L]` The two contracts in the root's name, `ThetaIntegralsAgree` and `LocalMatching` (`src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:585`, `:581`), are stated over Mathlib `NumberField`/`AdeleRing`, a literal theta sum over rational points, unitary groups of Gram matrices and Haar fundamental domains. They are proved in-project, outside this pillar, by `PositivityTheory.ThKR.theoremK_head2` (dom 11,543). Inside the pillar they are used at exactly three steps (§5.1).
4. **Non-vacuity hinges on one field, and that field is honest in shape.** `[L]` About 25 of the 46 fields have the form `Closed 𝒞 P` = "for all small ε there is a threshold K such that every family in class 𝒞 that is `Large K` satisfies P" (`src/Formalism/SharpRestriction/ParamsHeightRankConstant.lean:159`). These are vacuous if no large family exists. The single existence field is `hEx : MinkDiv → ExS 𝒜 cT` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:26`); `ExS` unfolds to `DesignChoices`, which reads `∀ K, ∃ Fm, 𝒞 Fm ∧ Fm.Large K CH ∧ …` (`src/Formalism/SharpRestriction/DesignExistsOfChoices.lean:22`) — the right quantifier order. Its two guards are discharged on the live path: `MinkDiv` by `minkowski_bound_rat` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEx.lean:35`) and `HostExW` by `supplyChi` from `VWin` (`src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean:8`). The 37,318-decl existence proof behind `hEx` was **not** audited beyond signatures.
5. **Everything inside the pillar is conditional on ~113 "Published" statements — and all of them are proved in-project.** `[L]` `P : UnitaryGroupThirdPlaceHypotheses` (60 fields) and `F : ThetaLocalInputs` (53 fields) are `Prop`-structures of `GlobalTheory.Published.*` statements. They are built at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:666-779` from `O : OpenLiteratureStatements`, which has **three** fields (`:215-218`), all discharged at `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-11`. "Literature" in these names does not mean "assumed" (all three fields of `OpenLiteratureStatements` are proved in-project; see [pillar_volume_lit.md](pillar_volume_lit.md) and [tcb_and_contracts.md](tcb_and_contracts.md)).
6. **Smells found — none is a soundness problem, each is a naming/abstraction problem.** `[L]`
   a literal `True` hypothesis field (`siegelEisensteinSimplePole : UnusedSlot72`, `UnusedSlot72 := True`); a "ghost" hypothesis whose content is discarded and re-proved (`hN`, §7 item 3); two parameter slots of the top shape instantiated to `True`; trivialized option slots (`anyGeometry := fun _ _ _ => True`, `SExt.none := … PUnit`); an alias layer `GlobalTheory.T.*` — 14,362 theorems in this pillar (38,194 kernel-wide) whose value is a single constant, re-exporting a lemma under a literature-sounding name the lemma itself does not have; folder names unrelated to content (46% of the pillar lives under `Development/AbelianVarietyTheory`).
7. **Earlier-draft contracts `Hyps` and `DRS` are dead code.** `[L]` `UpperTheory.Top.plugAll`/`plugWin` and the types `Hyps`/`DRS` occur in source (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:9,17`) but are absent from `kernel.db`; the live twins are `HypsAlt` and `DefiniteSideCondition`.
8. **Against `remark.pdf`:** the Lean matches the note on *chain of lifts of length m between unitary groups of ranks `k + j(t+1)`*, *mass/Chowla–Selberg/Weyl/Minkowski bookkeeping*, *seesaw + Bessel period*, *covolume/index statements*, *Behrend* (Mathlib's `Behrend` is live here) and *a Sha-length bound playing the "weak Vandiver" role*. No Lean counterpart was found, by name or by type, for "sixfold cover of GL5", "relative trace formula" or "Stepanov" inside this pillar (§6).

---

## 1. Census `[L]`

Repro: `python3 leanre/leanre.py decompile dom UpperTheory.Lit.every_character_of_theta_integrals_local_matching --depth 1 --min-size 2000`.

| quantity | value |
|---|---|
| dominator subtree of root | 543,325 decls (root id `956811`, idom `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin`) |
| kinds | `thm` 466,973 · `def` 74,169 · `inductive` 2,181 · `opaque` 2 (both Mathlib `ProbabilityTheory.Kernel.wrapped…`) |
| compiler auxiliaries (`._proof_`, `.match_`, `._simp_`, `.eq_N`, `_private…`) | 191,640 (35.3%) |
| kernel-reduction flags | `flags=1` 74,570 · `flags=3` 88 · none with `sorryAx`/`ofReduceBool` |
| taint sources inside (distinct decls; `kernel.db` after the `taint_sources` re-enrichment that added the `._proof_1_1` reduction auxiliaries) | `kexactB` 94 · `decide_kernel_pattern` 88 · `decide_kernel` 11 (6 modules) · `slow_con_leche` 6 (4 modules) · `CutCptCopy` 5 · `kcopy` 3 · `lean4lean_timeout` 2 (1 module) |
| direct dom children of root | 18,828; five ≥ 2,000 sum to 486,745; the rest (56,579) are shared small lemmas |

Where the code physically lives vs. what it declares:

| by module folder (2 levels) | decls | by declared namespace (1 level) | decls |
|---|---|---|---|
| `Development.AbelianVarietyTheory` | 250,280 | `GlobalTheory` | 263,551 |
| `Formalism.LocalToGlobal` | 72,267 | `Formalism` | 211,496 |
| `Formalism.SharpRestriction` | 56,825 | `PI` | 28,794 |
| `Formalism.HermitianCurvature` | 46,405 | `ReciprocityTheory` | 16,061 |
| `Formalism.PeriodIntegrals` | 34,300 | `UpperTheory` | 4,378 |
| `ReciprocityTheory.ReductiveGroups` | 15,468 | `PositivityTheory` | 2,356 |
| `Development.AutomorphicArithmetic` | 14,628 | `CompanionTheory` | 1,894 |
| (no module match) | 7,442 | | |

Reading: the folder `AbelianVarietyTheory` contains no abelian-variety theory relevant here; it holds namespace `GlobalTheory.*` (the construction of data records and the "rows"). Folder `HermitianCurvature` holds namespace `Formalism.FourierDecayAlt` (47,460 decls). Folder names are not evidence of content.

Top of the dominator tree (sizes include self):

```
every_character_of_theta_integrals_local_matching                     543,325
├─ UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound         451,610   PRODUCER of HypsAlt
│  ├─ GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt   153,377
│  │  ├─ GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0_alt         54,172   26-row table
│  │  │  ├─ GlobalTheory.LocalRows.lg1_sLp_sO_hTF                       23,153
│  │  │  ├─ GlobalTheory.T.hServ_of_linkR                               16,285
│  │  │  ├─ GlobalTheory.T.period_entries_tie_and_level_valuations_at_built  4,890
│  │  │  └─ GlobalTheory.CountRowByName.row_counts_of_labels_alt         4,259
│  │  ├─ GlobalTheory.T.large_unramified_exponent_bundles_exist_alt     37,318   existence package
│  │  ├─ UpperTheory.GalC.final_alt_alt                                 28,195   Galois "LinkN" row
│  │  ├─ GlobalTheory.T.liftInj_and_nonVan_typeNZ_of_given               6,418
│  │  └─ GlobalTheory.T.hyps_e_third_layer_ser_n_of_geometric_galois     2,218
│  ├─ GlobalTheory.Fc.S0.ontoX_and_lamLow_of_unitaryGroupHypotheses'    34,969
│  ├─ GlobalTheory.T.open0_of_unitary_group_hypotheses                  22,768
│  ├─ GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj           9,399
│  ├─ UpperTheory.Lit.functionalsSeparate_of_howeUnram_of_siegelWeil     7,161
│  ├─ GlobalTheory.BigTop.Fun.Close.fourier_coefficient_fit_of_join_alt  6,720
│  ├─ GlobalTheory.T.twisted_multiplicity_one                            5,815
│  ├─ Formalism.L2.SG.Pf.NcAllC.ncTieC_of_closed                         5,733
│  ├─ GlobalTheory.rowsPos_typeP                                         4,011
│  ├─ ReciprocityTheory.ChartRestriction.DS.Lap.TopClosed.besselNVG      3,026
│  ├─ GlobalTheory.SqTower.tower_alt_bis                                 2,820
│  ├─ CompanionTheory.WaveGrid.weighted_bound_rotated_uniform            2,368
│  ├─ ReciprocityTheory.ChartRestriction.DS.Xi.xiExists                  2,367
│  ├─ Formalism.FourierDecayAlt.P.CutSE.actual_compact_theorem           2,023
│  └─ 48,079 further direct children < 2,000 (mass ≈ 189,052; 37,078 are leaves)
├─ UpperTheory.Top.every_character_of_green_v_win                       23,523   CONSUMER of HypsAlt
│  └─ UpperTheory.Top.zero_free_all_of_green_v_win                      23,514
│     ├─ UpperTheory.Top.shape_closed_link_n_of_green                   19,248   (child Formalism.L2.G.linkG_concrete5 10,772)
│     ├─ UpperTheory.Top.supplyChi                                       2,686   (supplyOfAdm 2,584; hostOfField 830)
│     ├─ UpperTheory.Top.zeroFreeAll_of_topG                               498
│     └─ GlobalTheory.Fc.forall_goal_of_shape_of_hyps                       62
├─ GlobalTheory.T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces       4,685
├─ Formalism.MainNotions.G.GramWindowAlt.theorem_A_closed_form_holds     4,659
└─ Formalism.MainNotions.flipOneThree.Pf.theorem_I_closed_form_holds     2,268
```

Caveat `[L]`: a dominator child is not necessarily *called* by its parent. Of the 13 big children of `nonempty_hyps…`, only 4 are named in its proof term; the other 9 are there because they have ≥ 2 users in different subtrees (verified via kernel value-edge callers).

---

## 2. Question 1 — from `HypsAlt` to `Re(s) > 1/2`

### 2.1 The glue, as decompiled pseudocode `[L]`

```
every_character_of_theta_integrals_local_matching (P F hA hM hX hL hV) : EveryCharacter      -- src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69
  := every_character_of_green_v_win
       (green_of_regular P.greenRegularCharacters)                       -- Green        (src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumRangeEqRoots.lean:225)
       hV                                                                -- VWin         (pillar C)
       (nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL
          (fun cDep => boundAtTwoThree_linked_of_recT P.nLink _))        -- Nonempty HypsAlt (§5)

every_character_of_green_v_win hG hV h := imprimitive (zero_free_all_of_green_v_win hG hV h)   -- src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:16-18

zero_free_all_of_green_v_win hG hV h :=                                  -- src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12-15
  h.elim fun h =>
    zeroFreeAll_of_topG (la := 3/2)
      (forall_goal_of_shape_of_hyps _ _ _ _ (shape_closed_link_n_of_green hG) trivial trivial h)   -- : TopG
      (fun ψ => supplyChi ψ (hV ψ))                                      -- : ∀ ψ, HostExW (3/2) (GChi ψ).req
```

Inputs of the root and who supplies them (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810-813`) `[L]`:

| binder | type | supplied by | owner |
|---|---|---|---|
| `P` | `GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses` (60-field `Prop` bundle) | `published_results_eigen O` | `volume` |
| `F` | `GlobalTheory.FunPr.ThetaLocalInputs` (53-field `Prop` bundle) | `published_results_first O` | `volume` |
| `hA`, `hM` | `…WeilTensorModels.ThetaIntegralsAgree`, `.LocalMatching` | `theta_integrals_agree_and_local_matching_of_literature O` (`:565`; body ignores `O`) | `volume` |
| `hX` | `GlobalTheory.CovTop.CovolumeBoundOfX` | `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt …` | `volume` |
| `hL` | `UpperTheory.Zero.LLC.RecTExists` | `local_langlands_gl_recT_exists_of_literature O` | `galois` |
| `hV` | `UpperTheory.Top.VWin` | `UpperTheory.One.vwin_of_row` | `window` |

### 2.2 Contracts along the chain, unfolded

**`UpperTheory.EveryCharacter`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13`) `[L]` — `∀ N [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1/2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0`. Ground types only (Mathlib).

**`Formalism.HC.ZeroFreeAll`** (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:18`) `[L]` — `ZeroFreeOn fun _ => True`, with `ZeroFreeOn Q := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1/2)` (`:14`) and `PChar.ZeroFreeAbove ψ θ := ∀ s, θ < s.re → LFunction ψ.χ s ≠ 0` (`:11`). `PChar` = a level `N`, `NeZero N`, a character `χ` and a proof `χ.IsPrimitive` (`…/PrimePairSizeCondition.lean:7`). So `ZeroFreeAll` is exactly "every **primitive** Dirichlet L-function is zero-free on `Re s > 1/2`". Fully unfolded; not a wrapper.

**`UpperTheory.Top.imprimitive`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5`, dom 1) `[L]` — `ZeroFreeAll → EveryCharacter`. Mechanism read from the proof: pass to `χ.primitiveCharacter`, use Mathlib's `LFunction_changeLevel`, and show each removed Euler factor is non-zero because `‖p^{-s}‖ < 1`. `[S]` standard primitive/imprimitive reduction.

**`UpperTheory.Top.TopG`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:12`) `[L]` —
`∀ la (G : FReq), 1 < la → HostExW la G.req → (∀ Fm, G.cls la Fm → HypV Fm.toFamCore) → FamilyClassConnected (G.cls la)`.
- `FamilyClassConnected ℰ` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:13`): `∃ eD eL ε₁ > 0, ∀ eps ∈ (0, ε₁), ∃ Fm : FamP eps, ℰ Fm ∧ ∃ K cHH eK CL x0, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x`. A genuine `∃ Fm`.
- `HypV Fm` (`:10`): eventually, for every index `i`, `VVle (Fm.D x i).host.E (Fm.D x i).R.t (√(Fm.L x i).sc.b)`.
- `FReq.cls la` (`src/Development/AutomorphicArithmetic/CharacterBoxes/Supply.lean:22`): the family's core has windows of exponent `la` and every point satisfies the requirement `G`.

**`Formalism.MainNotions.ChainTied`** (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97`) `[L]` — an existential package: a base index `i0`, integers `m f`, a point map, a finite type `Top`, chain data `Dd`, constants, a functional `ell` on additive characters, sets `TT T2`, weights, followed by 16 conjuncts (`TiePts`, `TieGlobal`, `TieLocal`, `TieArith`, `Ident`, `SizeData₂`, `ErrWindows`, `BNBounds`, `GrowthInequalityRemainingHyps`, `CostWindows`, `RestSize`, and five equalities/inequalities). **Status: PARTIAL** — conjunct names read, bodies `OPAQUE`. This is the interface between "arithmetic of a family of data" and "a growth inequality for a prime sum".

**`zeroFreeAll_of_topG`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:26`, dom 498) `[L]` — applies `Formalism.HC.zeroFreeOn_of_tiedWin_cyc` (`…/TopWin.lean:90`) with the level `Level.cyc ψ` = the cyclic group of characters generated by `ψ.χ` (`…/ExplicitFormulaErrorOfHostConditions.lean:121`). Its three hypotheses per ψ are: a Chebyshev-type inequality on windows for any `ChainTied` family (`UpperTheory.Comparison₂.level_gm_le_on_family_scales`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean:28`), a form condition (`formB`), and existence of a tied family at window scale — which is exactly what `TopG` provides. The quantity controlled is `Level.Gm y = Gz y + Σ_{ψ ∈ Λ.Nt} wt ψ · Re gChi ψ y` (`…/ExplicitFormulaErrorOfHostConditions.lean:38`) and the bridge to zeros is `ChebyshevGrowthImpliesZeroFree : (∀ y ≥ y0, Gm y ≤ y^θ) → ZeroFreeAbove θ` (`:40`).
  `[M]` Reading: one positive combination over all powers of χ is bounded by `y^θ`, and a Landau-type positivity argument converts growth into a zero-free half-plane. *Where this breaks:* we did not read the proof of `zeroFreeOn_of_tiedWin` or `windowInequality_of_artinInputs`; both sit outside this pillar's dominator subtree (spine's shared diamond), and the exact role of windows (`la = 3/2`) is not unpacked here.

**`GlobalTheory.Fc.TopShapeAlt V NR N G`** (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShapeAlt.lean:24`) `[L]` — a curried Π-type: `∀ 𝒜 cT hEx sel hduty selS selP selDH selC selB hRB … , G`. Its binders are the fields of `HypsAlt` after decoding the raw selection `σ` into five selection components, plus two bare propositions `V` and `NR`. `goal_of_shape_of_hyps` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ShapeOf.lean:24`) is the uncurrying: it feeds `h.field` for each binder (two fields pass through an `iff`, one through an anonymous-constructor re-packing of nine named row components: `w1, covol, onto, lamLow, seeIso, miStar, fun0, pass, kap`). On the live path `V := True`, `NR := True` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:15`, two `trivial`s) — two hypothesis slots of the shape theorem are switched off.

**`UpperTheory.Top.shape_closed_link_n_of_green`** (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33`, dom 19,248) `[L]` — `Green → TopShapeAlt True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) TopG`. This is the theorem that says "the 46 fields suffice". Its body is 20 lines (`:33-52`), read at the level of "which lemma feeds which": it combines `Closed` facts with `Closed.and`/`Closed.imp`, obtains large families from `hEx` through `GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin` (`:50`; defined at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEx.lean:15`, where `hEx minkowski_bound_rat` appears at `:35`), and concludes with `UpperTheory.Top.topDesWin` (`:52`). Largest dominated lemma: `Formalism.L2.G.linkG_concrete5` (10,772; `src/Formalism/LocalToGlobal/GroupLattices/LinkGConcreteNoKer.lean:54`: `Closed 𝒞 GroupCompatibilityFamily → Closed 𝒞 Adm2F → Closed 𝒞 LinkG`). **Status: READ (skeleton)** — the dozen lemmas it calls (`link_gl`, `link_brest_alt`, `closed_family_admissible_twist_link_alt`, `selection_closed_of_wu_decay_alt`, `closed_linkDIVt_of_closed_bridge_kernel`, `topDesWin`, …) were not opened.

**`GlobalTheory.GLq.Green`** (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108`) `[L]` — for a prime `g`, a label datum and `d > 0`: a map `τ` from polynomials over `ZMod g` to class functions on `Gn g d` that sends each "prime label" to a cuspidal character of degree `∏_{i=1}^{d-1}(g^i − 1)`, injectively, and hits every cuspidal character. `[S]` This has the shape of J. A. Green's 1955 parameterization of cuspidal characters of `GL_d(F_g)`; note it is stated for **prime** fields only. Derived from `Published.GreenRegularCharacters` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:13`).

**`GlobalTheory.EX.HostExW la P`** (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:120`) `[L]` — for every `eps ∈ (0, 1/52)` there are constants and a set of scales `S : Scales la` such that at every scale in `S` beyond `x0` there exist `R : Ranks`, a host `H : Host R` and `q0` with `HostGood …` and the requirement `P`. `Scales la` (`src/Development/AutomorphicArithmetic/PrimeDiscriminants/Scales.lean:9`) carries a set `Win` containing, beyond every `y`, a whole interval `[Y, Y^la]`. So "window" = multiplicatively long interval of scales.

**`UpperTheory.Top.supplyChi`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean:8`, dom 2,686) `[L]` — `∀ ψ, VWinAt ψ 401 → HostExW (3/2) (GChi ψ).req`. `GChi ψ` (`src/Development/AutomorphicArithmetic/CharacterBoxes/Supply.lean:42`) asks for `EAtH (Level.cyc ψ) …` and `VVle H.E t (√ s.b)`. Via `supplyOfAdm` (`src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:17`) and `hostOfField` (`:8`, dom 830). This is where pillar C's `VWin` is spent: it yields **hosts** (CM-type number-field data) at window scales together with a Sha-length bound on them.

**`VVle E t B`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12`) `[L]` — for every algebraic closure `Ω` of `E` and every family of `LData E Ω p`: all `shaLen (ld p) e` with `0 < e < t` are finite, and `Σ_{l ∈ S} log l · Σ_{e=1}^{t-1} shaLen(l, e) ≤ B` for every finite set `S` of primes; `shaLen D e := Module.length ℤ_[l] (Sha D e)` (`src/Formalism/GaloisCohomology/Statement.lean:78`). `Sha`/`LData` `OPAQUE`. `[M]` this is a quantitative bound on ℓ-adic Tate–Shafarevich-type modules over all ℓ and all twists `e < t`; it is the natural candidate for the note's "significant weakening of Vandiver" `[A]`, but nothing in the Lean is *named* Vandiver, and the identification is ours.

### 2.3 `HypsAlt` — all 46 fields `[L]`

`structure HypsAlt (N : FamClass → Prop) (DR : R1.DefiniteSideType) : Type 1` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22`). Instantiation on the live path: `N := fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm` (= `S0.NL`, `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/GeometricWeakTiesOfStrong.lean:36`), `DR := DefiniteSideCondition`.

Notation: "[sel-pt]" = quantified over every family `Fm` in `𝒜`, every scale `x > Fm.x1` past the selection threshold, and every index `i : Fm.Ix x`. "Closed" = `Closed (D3 3 𝒜) …` unless stated.

| group | fields | shape | status |
|---|---|---|---|
| data | `𝒜 : FamClass`, `σ : RawSel BundleCondition 𝒜`, `cT : ℝ → ℝ → ℝ`, `c30`, `cIc` | the family class, a choice of "bundle" at every point, constants | READ |
| **existence** | `hEx : MinkDiv → ExS 𝒜 cT` | the only field asserting families exist | READ (proof behind it not audited) |
| class duties | `hduty`, `hc30`, `hcI` | every family in `𝒜` satisfies `Duty` (7 conjuncts, `src/Formalism/LocalToGlobal/ClassOfRecordOfChoice.lean:77`); constant inequalities | PARTIAL |
| indefinite realization | `hRB` [sel-pt] `IndefiniteRealisationBoundedRows`, `selJ` [sel-pt] `IndefiniteRealisationJoin` (10 fields), `hPA` [sel-pt] `PrimRows3 ∧ TypesSep3` | each selected bundle has a "real/indefinite realization" with bounded rows and a join to the definite data | OPAQUE below field names |
| **definite side** | `rRows : R1.SelectionDefiniteRows DR 𝒜 σ` | the `DefiniteSideCondition` rows hold along the selection | OPAQUE (see below) |
| row/lattice facts at points | `hTw`, `hLamP`, `hDivG`, `hDcPtG`, `hInstR`, `hMt` | twist ties, λ-rows, division rows, volume/class items, stability of a lattice under `𝒪` | OPAQUE |
| closed asymptotics | `hTu`, `hn4` (class-number formula), `hTF`, `sO`, `h30`, `jOn`, `aPt0`, `aPtTw`, `aPer0`, `aPerTw`, `aP10`, `aAtG`, `aC2`, `irrC`, `zL`, `tie` | `Closed … P` for 16 named predicates | OPAQUE |
| family-independent | `hLit : LitThin`, `hWu : WuDecayOfGap`, `hRF : RowsFinDim`, `sTy`, `sNG`, `sM`, `sLp`, `hU : ∀ D, MassRatioUnderVolume D`, `hG : ∀ D, GenusMassAt D 2`, `hServ` | statements about all data `D : D7` or all families | PARTIAL (`LitThin` read one level: three uniform statements `ShortIntervalPrimes.adm6/adm7/adm11` over all `D7`; those bodies `OPAQUE`) |
| **norm slot** | `nRest : N (D3 3 𝒜)` | on the live path: `Closed (D3 3 𝒜) LinkN` | READ |

**`Closed`** (`src/Formalism/SharpRestriction/ParamsHeightRankConstant.lean:159`) `[L]` — `∃ ε1 > 0, ∀ eps ∈ (0, ε1], ∃ K : TransportedAlt, ∀ (Fm : FamP eps) (CH : ℝ), 𝒞 Fm → Fm.Large K CH → P Fm CH`. `FamP.Large` (`:138`) compares three lists of the family's constants against thresholds in `K` (and contains a literal `∧ True ∧`). `[M]` it is an "eventually along a filter of ever-larger parameter choices" quantifier written by hand; *where this breaks:* it is not a Mathlib `Filter`, and nothing in the definition guarantees the filter is non-trivial — that is `hEx`'s job.

**`LinkN`** (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:45`) `[L]` — `∃ C x0, ∀ x ≥ x0, ∀ i, ShaFinOdd (Fm.D x i) → ∀ j ∈ lifts (Fm.D x i), LinkN_at (Fm.L x i) j C`, where `lifts D = Finset.Icc 1 D.R.m` and
`LinkN_at L j C := Summable (vvTerm D) → etaSum L j ≤ dZ0 j · (C · (f·m·b·L² + log²x · Nc) + Σ' l, vvTerm D l)` (`:40`);
`etaSum` sums, over places in the support where the twist differs from the base one, `lwP w · ramIdx w · etaJ j w` (`:36`); `vvTerm D l = (Σ_{e=1}^{t-1} shaLen l e) · log l` for prime `l` (`:31`); `dZ0 j = finrank ℂ (D.what₂.Zj mu0 j)`.
Reading `[M]`: for each of the `m` lifts, a weighted count of "twisted" places is bounded by (dimension of a space attached to lift `j`) × (size term + total Sha length). It is a conditional inequality (finiteness and summability are hypotheses), not a vanishing statement.

**`DefiniteSideCondition`** (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DefiniteSideCondition.lean:25`) `[L]` — a function of `(D, O, c, b, C, CH)` returning: for all side conditions (`Ok3`, `TypesSep3`, `CovolumeOntoIsometryConditions`, `PassIn3`, numerical facts, a family of `𝒪_LL`-submodules, three-sided division-compatibility data `I` with `DivTied3 …` and `HEq I b.P.I`), `∀ u, RowsU …`. The 7,027-node body repeats one long `packageOfPrimitiveLinks …` sub-term nine times. **OPAQUE**: we read the binder list, not `RowsU` (kernel name `Formalism.L2.RowDataTransport.RowsU`) nor `DivTied3`. The nine row components visible at the consumer are `w1, covol, onto, lamLow, seeIso, miStar, fun0, pass, kap` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ShapeOf.lean:29`).

**`hEx` chain** `[L]` —
`ExS 𝒜 cT := ∀ la G, 1 < la → HostExW la G.req → DesignChoices (WithTw fun Fm => 𝒜 Fm ∧ G.cls la Fm) 3 cT` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExS.lean:10`);
`DesignChoices 𝒞 C0 cT := ∃ ε0 > 0, ∀ eps ∈ (0, ε0], ∀ K : TransportedAlt, ∃ (Fm : FamP eps) (CH C5 Cb : ℝ), 𝒞 Fm ∧ 0 ≤ CH ∧ Fm.Large K CH ∧ …` (14 further conjuncts; `src/Formalism/SharpRestriction/DesignExistsOfChoices.lean:22`);
`MinkDiv := ∀ n, MinkMult n (minkM n)`, `MinkMult n M := ∀ H : Subgroup (GL (Fin n) ℚ), Finite H → Nat.card H ∣ M` (`:12`, `src/Formalism/SharpRestriction/GlobalSchurBounds/MainIn.lean:51`) — `[S]` Minkowski's 1887 bound on finite subgroups of `GL_n(ℚ)`; proved as `minkowski_bound_rat` (`src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/MinkowskiQ.lean:6`, dom 23).

---

## 3. The data model: what a "family" is `[L]`

| object | anchor | content |
|---|---|---|
| `Ranks` | `src/Formalism/LocalRingCardinality/Params.lean:6` | extends a `Frame`; naturals `k m t` with `Even k`, `Even m`, `Odd t`, `2 ≤ m`, `m+3 ≤ k`, `k + m − 1 + 5 ≤ t`, `3m < t`, `m ≤ 2·ord ≤ k`, `m² ≤ k + m(t+1)`. Derived: `N j = k + j(t+1)`, `r = k+m−1`, `nV = r+t`, `rankY j = r + j·t`, `sigY0 = (k + rS, rS + 1)` with `rS = m/2 − 1`. |
| `Host R` | `src/Formalism/LocalRingCardinality/DataHost.lean:39` | extends `HostAx`; 45 own fields: a field `E` with an element `sqq`, `sqq² = −q`, Galois action on it, primes `g 0`, `g 1`, `pde`, `pde'`, level primes, a class-group subgroup `ccK`, finite sets `TT`, `T2`, … (names read; types mostly not). |
| `HSpace E` | `src/Formalism/LocalRingCardinality/DataSpaces.lean:26` | a module `V` with a Hermitian form, rank, basis, signature per complex embedding, and a **unimodular `𝒪_E`-lattice** `L0`. Mathlib-ground. |
| `Spaces` | `…/DataSpaces.lean:77` | 43 fields: Hermitian spaces `X i`, `X'`, `Y i`, `W`, `V` with signatures/ranks and isometries between them, anisotropic vectors `z`, hyperbolic pairs. |
| `ColumnChain` | `src/Formalism/LocalRingCardinality/DataKernels.lean:14` | `cls : ℕ → Type`, `stab : ∀ i, cls i → Type`, `DGam` with `card (stab i c) ∣ DGam` for `i ≤ m`, `Y : ℕ → Type`, unit-norm scalars `rhoDet`, and `unf : ∀ i, cls i → cls (i+1) → ((Y i → ℂ) →ₗ[ℂ] (Y (i+1) → ℂ))`. **All carriers abstract.** |
| `PeriodMap` | `…/DataKernels.lean:163` | abstract types `Mt Wz Wrow`; linear maps `evz` from `(cls m → Y m → ℂ)`, `lowerMap`, and `period : Wrow →ₗ Mt →ₗ ℂ`. |
| `Rows.Data R` (`what₂`) | `src/Formalism/LocalRingCardinality/DataRows.lean:36` | 70 fields: a number field `LL` with embedding to ℂ, places, a ring `O`, index types `Tau`, `Tup`, `Word`, complex spaces `EE`, `Amb μ`, `Mu u`, lattices `Mtilde`, pairings `perCol`, `Bu`, weights `etaJ`, `shaLen`, … |
| `NData` | `src/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:55` | an algebraic closure `Om` of `host.E`, places, `ldat p : LData host.E Om p` for every prime, a tie `shaLen (ldat p) e = n → what₂.shaLen p e = n`, an index type `Loc`, … |
| `D7` | `src/Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:76` | 135 fields bundling all of the above for one "datum": `R`, `host`, `sp`, `what₂`, `mem u : Member` (= `ColumnChain` + `ColumnsAtT` + `PeriodMap`) for every word `u`, `LL` Galois and totally complex, lattice-of-class maps `clsLat : cls i → Submodule (𝒪 host.E) (sp.X i).V` with `IsLattice`, identifications `eMu`, `eMt`, and the N-layer records `nd`, `ntw`, `naut`, `nbc`, `nexp`, `ntypes`, `nth`. |
| `SizeData₂ D` | `src/Formalism/LocalRingCardinality/DataParams₂.lean`, line 76 | 63 fields of real-valued sizes/windows attached to a datum (scale `sc.x`, `sc.eps`, `sc.b`, supports, gains, …). |
| `FamCore eps` / `FamP eps` | `src/Formalism/SharpRestriction/FamCore.lean:71`, `src/Formalism/SharpRestriction/ParConsts.lean:31` | a threshold `x1 > 1`; index types `Ix x`; an unbounded window set `Win` with `Ix x` non-empty on it; `D x i : D7`, `L x i : SizeData₂ (D x i)` with `sc.x = x`, `sc.eps = eps`; ranks constant in `i`; (`FamCore`: 43 fields) then, in `FamP`, 39 more fields of parameter choices and cross-index compatibilities. |
| `FamClass` | `src/Formalism/SharpRestriction/ParamsHeightRankConstant.lean:157` | `∀ {eps}, FamP eps → Prop`. |

`[M]` Reading (ours; the identifications are not stated in Lean): `N j = k + j(t+1)` is the rank of the `j`-th Hermitian space `X j`; `cls j` plays the role of the finite class set of a lattice genus in `X j`, `stab` of the finite stabilizers, `cls j → Y j → ℂ` of vector-valued functions on that class set (i.e. algebraic automorphic forms on a definite unitary group), and `unf` of the kernel carrying forms from step `j` to step `j+1`; `lifts D = {1,…,m}` are the `m` steps. *Where this breaks:* `ColumnChain` itself imposes none of this — it would be satisfied by any types and maps with the stated cardinality/norm properties. The link to actual lattices is `D7.clsLat` plus tie predicates (`Ties`, `LocTied`, `ClassItemsAt`, `GenusMassAt`, …) that we did not unfold. On the live path the chain is built as `GlobalTheory.Mem.Col2.TC.chain` with `cls i := (I.stp u a i).Cl` and a proved lattice property for each class (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/LatAtLattice.lean:147-165`); what `Cl` is, is `OPAQUE`.

How a `D7` comes into existence on the live path `[L]`: not by a single definition but by record surgery through stages — `GlobalTheory.Mem.assemble` / `GlobalTheory.Mem.Stages.toD7` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/AssembleLattice.lean:197`, fan-in 2,726), then setters `setTw`, `setAut`, `setCG`, `setBC`, `setTy`, `setN`, `withLoc`, … (`…/BlocksUnique.lean:80-113`, `…/RingSpecNormalisedCharacterEq.lean:172,367`). The first stage has `Loc := Empty` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/BareStatementOfDiscreteSeries.lean:36`) and several setters require `IsEmpty D.nd.Loc`; `withLoc` then installs local data. We did not verify that the final family's `Loc` is non-empty (§7 item 6).

---

## 4. What is and is not concrete — verdict table

| layer | example | verdict | tag |
|---|---|---|---|
| target statement | `EveryCharacter`, `ZeroFreeAll`, `PChar` | **real** — Mathlib `DirichletCharacter.LFunction` | `[L]` |
| analytic reduction | `imprimitive` | **real** — standard, read | `[L]` |
| interface predicate | `ChainTied`, `TopG` | **unknown** — existential package over project records; bodies not unfolded | `[L]` |
| hypothesis record | `HypsAlt` | **proxy** — 46 fields over an abstract family class; content depends on `hEx` | `[L]` |
| datum | `D7`, `ColumnChain`, `PeriodMap` | **proxy** — abstract carriers for forms/lifts, concrete carriers for fields/lattices | `[L]` |
| theta contracts | `ThetaIntegralsAgree`, `LocalMatching` | **real** — adelic, Mathlib-ground (entire 606-line file checked; leaves `SiegelRule`, `IsDblCoord`, `LS` not opened) | `[L]` |
| covolume contract | `CovolumeBoundOfX` | **proxy** — `Closed FamHyp (… L3 …)` over project records | `[L]` |
| published bundles | `UnitaryGroupThirdPlaceHypotheses`, `ThetaLocalInputs` | **wrapper** — hypothesis bundles, all fields discharged upstream | `[L]` |
| alias layer | `GlobalTheory.T.*` | **boilerplate** — one-node re-exports | `[L]` |

---

## 5. Question 2 — the producer (`451,610` decls) and the definite/indefinite bridge

### 5.1 `nonempty_hyps_definite_side_of_closed_bound` `[L]`

Header (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44`): `P → F → ThetaIntegralsAgree → LocalMatching → CovolumeBoundOfX → ∀ hL : RecTExists, (∀ cDep, LinkedAt (parametersOfDependence hL cDep) (… BoundAtTwoThreeFamilyFonAlt …)) → Nonempty (HypsAlt S0.NL DefiniteSideCondition)`.

Proof skeleton (lines 45-68; only `intro/have/obtain/exact`, every step a named lemma):

| line | produces | by | consumes |
|---|---|---|---|
| 47-48 | `hS : …LevelPlusSubgroup.FunctionalsSeparate` | `functionalsSeparate_of_howeUnram_of_siegelWeil` (7,161) | `F`, `Hk3.howeUnram_holds` (closed theorem, dom 488), `P.siegelWeilUnitaryConvergent` |
| 49-50 | `hRat : S0.RowRat` | `rowRatW_of_rowTest (T.test_vector_assembly_holds …)` | **`hA`, `hM`**, `hS`, `P.greenCuspidal`, `F`, `P.litN.join/.fe` |
| 51 | `hFit : BigTop.Fun.ConstantFunctionFits Fld` | `fourier_coefficient_fit_of_join_alt` (6,720) | **`hA`, `hM`**, `hS`, second half of `ontoX_and_lamLow_of_unitaryGroupHypotheses' P` (34,969) |
| 52-54 | grid evaluation `EvLgG (GridA …)` | `evaluation_grid_of_join` | **`hA`, `hM`**, `hS`, `twisted_weil_representation_convergence`, `T.twisted_local_factors_match`, `T.twisted_square_theta_integrals_eq` |
| 55-56 | `rowFun` statement | `StageOne.rowFun_at_gridA_alt` | five `P.*` fields, `hFit` |
| 58 | `hOpen1 : S0.OpenParameterStatements …` | `T.open0_of_unitary_group_hypotheses P hL _` (22,768) | `P`, `hL` |
| 59-62 | monotone transport to the extended parameters | `Glob.open_and_linked_of_stronger_extension_alt` | — |
| 65-67 | `hL3` | `Glob.CovolRow.linked_bundles_l3_of_open_alt` | **`hX`**, five `P.*` fields |
| 68 | goal | `StageU.hypotheses_nonempty_of_unramified_exponents_alt` (153,377) | `P`, `hRat`, `hL`, `hEv`, `hN _`, `hFun`, `hL3` |

So the theta contracts enter at three steps and produce three things: a *rationality row* (`RowRat`), a *Fourier-coefficient fit* and an *evaluation grid*; the volume contract enters once and produces the *L3 (covolume) row*.

### 5.2 `StageU.hypotheses_nonempty_of_unramified_exponents_alt` (153,377) `[L]`

`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HypothesesNonemptyOfUnramifiedExponents.lean:41-61`: nine `have`s and one `exact Fc.nonempty_hyps_of_allRows_alt …` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/NonemptyHypsOfAllRows.lean:19`, dom 714 — the place where the `HypsAlt` record literal is written; `hEx` at `:59`). Three ingredients:

1. **Existence package** — `T.large_unramified_exponent_bundles_exist_alt` (37,318; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MemberBundlesLargeUnramifiedExponents.lean:69`, a one-node shell): returns `SiegelMassRatioCM ∧ MemberE ∧ ExBL`.
   - `SiegelMassRatioCM`: `mass(stdForm K M) / mass(stdForm K (M−1)) = massRatioRightSide K M` for `M ≥ 3` over unramified CM fields (`src/Formalism/SharpRestriction/GlobalSchurBounds/StandardLattice.lean:281`).
   - `MemberE 𝒮 := BaseCond ∧ FirstG ∧ ExportF ∧ SecondG` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ThetaChr.lean:102`): for every sufficiently large *context* there is a base number-field datum, over it an untwisted constructed point, which can be re-twisted into a "good" point.
   - `ExBL`: every large good built point carries a linked bundle.
   - Via `Bl.exists_baseLattice_of_prime_alt` (26,262; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExistsBaseLatticeOfPrime.lean:57`): a staged chain `Start → Has3 → Has4 → HasC (BuiltE)` whose stage lemmas take as hypotheses ray class fields, CM curves with good reduction, discrete series existence/uniqueness, Casselman–Wallach, the Weil representation of a unitary pair, Chebotarev, Poitou–Tate, Greenberg–Wiles, local Tate duality/Euler characteristic.
   - `[L]` All "eventually" quantifiers here (`Ev`, `EvG`, `EvP`, `EvLgG`) are of the form `∀ K : Ctx, … → p K`: they never assert that a context exists. Contexts come from hosts, i.e. from `HostExW`, i.e. from `VWin` at the consumer (§2.2).
   - The theorem name says "large unramified exponents"; **no type in its statement mentions exponents or ramification**. The name is `[A]`-grade evidence only.
2. **The 26-row table** — `AllAtMemberStage0.allRows_of_open0_alt` (54,172; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkROfIsLinked.lean:50`). Conclusion `AllRowsAlt …`, one row per `HypsAlt` field. A "row" is `Fc.Row Q Lk H := ∃ E, RowE Q Lk E ∧ ∀ 𝒜 σ, IsSel Q Lk E 𝒜 σ → H 𝒜 σ`: a pointwise property `E` holding eventually at built points, such that every family class assembled from such points satisfies `H`. Sources of rows (read from lines 56-79; the body continues and the sources of `rRows`/`nRest` were **not** read):
   - `sLp`, `sO`, `hTF` ← `LocalRows.lg1_sLp_sO_hTF` (23,153) ← `CarrierGap.offDiag` (22,167; `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OffK0Closed.lean:673`), which contains the hypothesis-free `CarrierGap.carrierP : Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP` (8,009; `:665`) and a quantitative "Theorem S" (`theoremS_of_conj`, 2,853).
   - `hServ` ← `T.hServ_of_linkR` (16,285) ← `Svd.servH_row_of_artin`: from `Published.GlobalArtinReciprocity` to a "service" row about kernels.
   - `aPt0, aPtTw, aPer0, aPerTw, tie, aP10` ← `T.period_entries_tie_and_level_valuations_at_built` (4,890), hypothesis-free.
   - `c30` ← `CountRowByName.row_counts_of_labels_alt` (4,259).
   - `hPA, hLamP, hDivG, hDcPtG, selJ` ← copied from `OpenParameterStatements` (the 12 "open" rows proved separately from `P`, 22,768).
   - `[L]` Several rows are proved for *every* class and selection (`LocalRows.at_choice_alt`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/AtChoice.lean:16`). Either their targets are `Closed`-statements whose own premises carry the content, or they are weak; not resolved — `OPAQUE`.
3. **The Galois "LinkN" row** — `UpperTheory.GalC.final_alt_alt` (28,195; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CFinal.lean:19`) produces exactly the field `nRest`. Mechanism (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean:37-63`, read): at every point choose a "good cut" of the datum (`CutGivesAlt`), get uniform constants (`T.exists_const_tieChi_bound_of_facts`, 6,332), prove the conclusion for the cut family from `Hypotheses₂` and a bound "at two and three" (`NLinkClose.main_alt_alt`, 18,288), convert to `LinkN`, transfer back. `Hypotheses₂` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoAndThreeForFamily.lean:18`) = `{FontaineBcris, GlobalArtinReciprocity, BlochKatoLocal, LocalTateDualityK, LocalEulerCharK, LocalFinitenessK, BhattScholzeIntegral}`.

### 5.3 "Definite side" vs "indefinite side" — what the bridge is `[L]`/`[M]`

- **Definite side** `[L]`: the `D7` chain itself — Hermitian spaces `X j` of rank `N j` with unimodular lattices, class types, stabilizer cardinalities dividing `DGam` (Minkowski), mass ratios (`SiegelMassRatioCM`, `GenusMassAt`, `MassRatioUnderVolume`), class-number formula (`hn4`), and the rows `covol / onto / lamLow / seeIso / miStar / fun0 / pass / kap` of `DefiniteSideCondition`. These are statements about finite-dimensional lattices and their indices/covolumes.
- **Indefinite side** `[L]`: namespace `GlobalTheory.IndefiniteRowSideFullHecke` (4,942 decls in the pillar; folder `src/Development/AbelianVarietyTheory/BlockTheory/…`) — adelic unitary groups `UA σ J` of (skew-)Hermitian Gram matrices with prescribed real signatures, Schwartz–Bruhat test functions, Weil representations characterized axiomatically (`IsUWeilPair`), theta integrals over Haar fundamental domains. The Lean field names `IndefiniteRealisationBoundedRows`, `IndefiniteRealisationJoin` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/IndefRRealTB.lean:39`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ColJoinSOfSTiesR.lean:67`) attach to each selected bundle a "real realization" (`RealTBAlt`, `STiesRAlt`, `RecTAlt`) plus a join record with maps from the datum's complex spaces `Mu u`, `EE` into the realization and four tie predicates (`ChainTieT`, `RowTieT`, `ColNormT`, `PairTieT`).
- **Bridge** `[L]`: the record `Fc.BundleCondition D O c` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ColumnChoiceWithTies.lean:47`, 7 fields: `R`, `S`, `P`, `pin`, `DH`, `C`, `B`) chosen at every point by the selection `σ`; `rRows` then asserts the definite-side rows for the package built from that bundle. In the producer, the theta contracts are what turn adelic integral identities into the rows `RowRat`, `ConstantFunctionFits`, `EvLgG`.
- `[M]` Reading: periods computed on an indefinite unitary group (via Weil representation / seesaw / Bessel models) are matched against integral-structure data on definite unitary groups. *Where this breaks:* we did not unfold `RealTBAlt`, `STiesRAlt`, or any of the four tie predicates, so "matched" is the Lean's field vocabulary, not a verified mathematical statement.

### 5.4 What `Development/AbelianVarietyTheory` actually contributes here `[L]`

| namespace | decls in pillar | what it declares (sampled) |
|---|---|---|
| `GlobalTheory.Mem` (`.Top.Bl`, `.Col2`, `.SRe`, `.LiteralAutomorphy`, …) | 19,158 | the staged construction of data (`Base`, `Cols`, `Stages`, `assemble`, `toD7`), contexts, parameters, built/good points |
| `GlobalTheory.T` | 14,772 | alias shells and their immediate targets |
| `GlobalTheory.IndefiniteRowSideFullHecke` | 4,942 | adelic unitary/theta/Weil objects (§5.3) |
| `GlobalTheory.HeightCounting` | 4,857 | record setters (`setAut`, `setCG`, `withLoc`, …) and layer moves |
| `GlobalTheory.Fc` (`S0`, `R1`, `RL`, `StageU`, …) | 672 | rows, bundles, links, `HypsAlt`; `S0` = "stage 0" of the row table |

Spot sample of 13 definitions among the ~190k small children: `𝒪_E`-lattices, adelic idempotents, `U(p,q)` matrix groups, Haar measures — real objects. 45 live lemmas sit under `src/Development/AbelianVarietyTheory/Counterexamples/…`; the path is misleading (their consumers look ordinary), bodies not opened.

---

## 6. Question 3 — against `remark.pdf`

All right-hand entries are `[L]`; all left-hand entries are `[A]` and carry Footnote 4's caveat. Name-substring counts are over the 543,325 kernel names of the pillar and are *hints only*.

| note item `[A]` | Lean evidence in this pillar `[L]` | status |
|---|---|---|
| #8 iterated lifts `U(X0) → … → U(Xm)` between totally definite unitary groups; "wins multiplicity m" | `Ranks`: `N j = k + j(t+1)`, `lifts D = Icc 1 m`, `Spaces.X i` Hermitian of rank and signature fields, `ColumnChain.unf` step maps; `LinkN` is quantified over `j ∈ lifts`. Substring `lift` in 14,042 names. | **MATCH (structure)**; "totally definite" lives in signature fields we did not read; "multiplicity" as such not located |
| #8 "π ↦ π ⊞ µ_j[t]" | rank step `t+1` and parameter `t` (odd) exist; no Arthur-parameter object found | **OPAQUE** |
| #9 norms/levels with divisibility "via Chowla–Selberg, Weyl, and Siegel mass" | `GlobalTheory.chowla_selberg_lattice` (`src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean:250`), `PeriodClassSumWeyl`, `SiegelMassRatioCM`, `GenusMassAt`, `MinkDiv`; `mass` in 14,610 names, `weyl` 2,560, `chowla` 6 | **MATCH (objects present)**; how they combine not traced |
| #12 seesaw; period of the iterated lift is a Bessel period; Rallis | `GlobalTheory.T.exists_seesaw_pair_of_theta_data` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ExistsSeesawPairOfThetaData.lean:40`), `BesselId` (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:65`), closed theorem `…DS.Lap.TopClosed.besselNVG` (3,026: an integral is non-zero), `ArchimedeanRallis*`; `seesaw` 1,679, `bessel` 2,946, `rallis` 148, `ggp` 16 | **MATCH (objects present)**; "independent of the Hecke characters" not located |
| #13 Bost slope inequality | `Formalism.HermiteSiegelSlopes.base_change_slope`, `WeightedSlopeBounds`; `slope` 611, `bost` 0 | **PARTIAL** — slope vocabulary present, attribution not |
| #16 relative trace formula; sixfold cover of GL5; norm of a projected Poincaré series; near-orthogonality of columns | `PoincareAmplitudeLowerBounds.CarrierP` (8,009, hypothesis-free), "column" vocabulary throughout (`ColumnChain`, `ColNormT`); `poincare` 608; `relativeTrace` 0, `sixfold` 0; `traceFormula` 6 (`IsotypicProjectorTraceFormula…`, `heisenbergDeriv_archimedeanLift_traceFormula`; neither is a relative trace formula by name, bodies not read) | **DIVERGE / not found**: no relative trace formula and no sixfold cover by name or by any type we read. Poincaré-series lower bounds exist. |
| #17 "significant weakening of Vandiver" for classes in an `H¹` with `Q_ℓ/Z_ℓ(−e)` coefficients | `VVle`, `ShaFinOdd`, `vvTerm`, `LinkN` (Sha lengths over all ℓ and twists `e < t`); `vandiver` 0 | **MATCH (role)**, identification is ours; the Lean statement is a *length bound*, not a vanishing |
| #18 covolumes, theta series' index, congruences between lifts and forms | `CovolumeBoundOfX`, row `covol`, `T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces` (4,685; name only, not unfolded), `covol` 627, `congruen` 1,055 | **MATCH (objects present)** |
| #19 "precise choice of the Iwasawa tower, specifically using Behrend" | Mathlib `Behrend.*` (3-AP-free sets) is live via `Formalism.FrobeniusOrbits.hostThickExists` (`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean`, dom 33, direct child of the pillar root) | **MATCH (Behrend is used)**; "Iwasawa tower" not located as an object (the 28,744 module hits are a *folder* named `IwasawaDecomposition`) |
| #15 integral structure glued across Hecke characters ("gcd", extra averaging) | families indexed by `Ix x` with cross-index equalities (`FamP.eta_eq`, `Sc_shared`, `hP_eq`, `bs_eq`, …), `Level.cyc ψ` averaging over powers of χ | **PARTIAL** |
| #14 "one would stop at 2/3 a priori … need for division" | `DivData`, `DivRows3G`, `DivTied3`, `DivisionKernelConstantBounds`; exponent `2/3` not located | **PARTIAL** |
| #1/#4 Stepanov determinant | `stepanov` 0 | **not found in this pillar** |
| #5/#6 the Λ-sum and positivity trick giving `> 1 − η` | `Level.Gm`, `ChebyshevGrowthImpliesZeroFree` (consumer side; proof outside pillar) | **MATCH (shape)** |
| unramified exponents (theorem names) | appears only in names; no type-level counterpart | **name only** |
| theta lifts as adelic integrals | `ThetaIntegralsAgree`, `LocalMatching`, `thetaSum` | **MATCH**, but proved outside the pillar and used at 3 steps |

What remains `OPAQUE` at this boundary: `ChainTied` conjuncts; `DefiniteSideCondition`/`RowsU`; `BundleCondition` components; `Duty`; the 16 `Closed` predicates of §2.3; `MemberE` internals (`ExportAt`, `Forced`, `Has3/Has4/HasC`); `Sha`/`LData`; `Host` field types; `TransportedAlt`; everything below signatures in the 26,262-decl existence chain.

---

## 7. Question 4 — skepticism ledger

Severity: **S0** would threaten the headline theorems (none found); **S1** weakens what an intermediate statement means; **S2** naming/hygiene.

| # | finding | receipt `[L]` | sev |
|---|---|---|---|
| 1 | **Abstract record standing in for automorphic forms.** `ColumnChain.cls/stab/Y : … → Type` and `unf` are unconstrained carriers; `PeriodMap.Mt/Wz/Wrow : Type`. All "row" statements are about these. | `src/Formalism/LocalRingCardinality/DataKernels.lean:14`, `:163` | S1 |
| 2 | **`Closed` is vacuous without large families**; ≈25 `HypsAlt` fields, `CovolumeBoundOfX`, `ConstantFunctionFits`, `S0.NL` have this form. Mitigation present: `hEx` with correct `∀K ∃Fm`, both guards discharged. Residual: the existence proof (37,318) is unaudited. | `src/Formalism/SharpRestriction/ParamsHeightRankConstant.lean:159`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:26`; `src/Formalism/SharpRestriction/DesignExistsOfChoices.lean:22`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:50`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEx.lean:35` | S1 |
| 3 | **Ghost hypothesis.** The root passes `hN` (closed "bound at two-three" row, from `P.nLink`). Downstream, `linkN_of_boundAtTwoThree_slot` takes only `ε1` and the threshold `K` from it — the bound itself is bound to a name that is never used — and re-derives the bound from `Hypotheses₂` via `at23_family_alt`. Redundant plumbing, not vacuity. | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean:54-63` (and `:51`), `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/At23OfAll.lean:19,24`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:73` | S2 |
| 4 | **Literal `True` hypothesis.** Field `siegelEisensteinSimplePole : GlobalTheory.Published.UnusedSlot72`, with `abbrev UnusedSlot72 : Prop := True`. No statement about a simple pole of a Siegel Eisenstein series exists behind that field name. | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:74`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7` | S2 |
| 5 | **Two slots of the top shape set to `True`.** `TopShapeAlt True True …`; both discharged by `trivial`. | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:15` | S2 |
| 6 | **Empty index type at the first construction stage.** `Loc := Empty`; setters demand `IsEmpty D.nd.Loc`; lemmas such as `rowsC_of_isEmpty`, `serLoc_of_isEmpty` conclude by `h.elim`. `withLoc` later installs local data. Not shown here: that the families reaching `LinkN`/Galois rows have non-empty `Loc` (if `Loc` stayed empty, `∀ i : D.nd.Loc` statements on the Galois side would hold trivially). The same bare stage has all twist weights zero (`HasBare … IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0`), and `etaSum` in `LinkN` is built from such weights, so the question "are η and `Loc` non-trivial in the families that reach `LinkN`?" decides whether `LinkN` has content there. Pointers for a follow-up: `LinkEta`/`N.LocsCoverTw` ("local data cover the twisted places") and `Duty.TwAllF`. **Open — worth a targeted check.** | `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/BareStatementOfDiscreteSeries.lean:36`; `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/BlocksUnique.lean:80,103,112`; `src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/UnitaryRealisationReadingOfIdempotentActsViaLeve.lean:113,117`; `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/RingSpecNormalisedCharacterEq.lean:367`; `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonzeroPlacesOverPrimesLifts.lean:122`; `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:49` | S1 (unresolved) |
| 7 | **Trivialized option slots on the live path.** `anyGeometry : GeoP := fun _ _ _ => True`; `SExt.none : SExt := fun … => PUnit`; `parametersOfDependence` plugs both; `LinkedAt.of_row` fills an existential slot with a constantly-`True` property via `largeBaseProperty_true`; `FamP.Large` contains `∧ True ∧`. All on the parameter side ("no extra constraint"), none as a conclusion. | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:19`, `…/ThetaChr.lean:22`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Prm1.lean:20`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RowGood.lean:40-42`, `src/Formalism/SharpRestriction/ParamsHeightRankConstant.lean:139` | S2 |
| 8 | **Alias layer `GlobalTheory.T.*`.** 13,917 of the 14,006 `GlobalTheory.T.*` theorems under the producer (14,362 in the pillar; 38,194 of 38,677 kernel-wide) have `value_nodes = 1`: the value is a single constant, re-exporting an identically-typed lemma under a literature-sounding name. Example: `T.twisted_multiplicity_one` concludes `CuspMult.MultEq` — an equality of multiplicities under transfer, not multiplicity one. They also double the apparent depth of the dominator tree. | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OpenOrbitOfUnramifiedExponents.lean:75` (body read), `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedMultiplicityOne.lean:30`; count: `select count(*) from decls where name like 'GlobalTheory.T.%' and kind='thm' and value_nodes=1` | S2 |
| 9 | **Hypothesis bundles of ~113 statements** inside the pillar; discharged upstream, 182 of 195 `*_of_literature` wrappers ignore their `O` argument; `OpenLiteratureStatements` has 3 fields. Several Props are narrower than their names (Green: prime fields only; 13 Props quantify over `D7`). | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:22`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/BernsteinUnitaryProductIrreducible.lean:6`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215-218,565,666-779`; `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-11` | S2 (see `pillar_volume_lit.md`, `tcb_and_contracts.md`) |
| 10 | **"Example" record is live.** `Formalism.BasicNotions.Examples₂.exampleRecord` gives `Nonempty D7`, used once, inside a Wach-lattice existence argument (`GlobalTheory.MemLoc.record_nonempty` → `WachPlace.exists_positions_global`). Looks like a default-inhabitant use, not a substitution for the main family. Not audited. | `src/Formalism/LocalRingCardinality/SpanPowerMembership.lean:49-51`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalGapNonemptyAndRecordNonempty.lean:14` | S2 |
| 11 | **Dead twins and near-duplicates.** `Hyps`/`DRS`/`plugAll` source-only; `AllRows`/`AllRowsAlt`, `Open0`/`OpenParameterStatements`, `Setup`/`SetupAlt`, `Prm`/`Parameters` near-copies; `S0.RowRat` and `Mem.LiteralAutomorphy.RowRatW` have identical kernel sighash; a second copy of a sub-development under namespace `Gp91`. | `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:9,17` | S2 |
| 12 | **Tuned constants in contracts**: `VWinAt ψ 401`, `eps < 1/52`, `Fm.CYL ≤ 9`, `la = 3/2`. These are artifacts of the proof, not of any published statement. | `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49`, `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:121`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:14` | S2 |

Why none of this is S0 `[L]`+`[M]`: the five headline theorems are stated over Mathlib objects and have no hypotheses; the kernel accepted the whole term with only `propext`, `Quot.sound`, `Classical.choice`. A vacuous *intermediate* statement cannot make a hypothesis-free conclusion false — if `HypsAlt` were degenerate, the consumer (which must still output `ZeroFreeAll`) would have had to prove RH from nothing. What S1 items do affect is **Layer 3**: how much of the proof's apparent mathematics is carried by statements we can read versus by a 135-field record whose instantiation we have not audited.

---

## 8. Not done (honest list)

- No proof body longer than ~30 lines was read end-to-end. `shape_closed_link_n_of_green` (the "46 fields suffice" theorem) is 20 lines and was read, but none of the lemmas it calls was opened.
- `allRows_of_open0_alt` body past line 79 (sources of `rRows`, `nRest`) unread.
- The existence chain behind `hEx` (37,318 decls) is known by signatures only.
- `Loc` non-emptiness in final families (§7 item 6) unresolved.
- `Base.IsGood` satisfiability for the theta contracts not checked (the contracts are ∀-statements over good bases; `theta_tower_step_exists_triple` exists).
- 15 of 131 distinct `Published.*` Props were unfolded in detail (see `published_catalogue.md` for the full census).
- The analytic step from `ChainTied` to the Chebyshev inequality (`windowInequality_of_artinInputs`) is outside the pillar and unread.

## 9. Repro

```bash
python3 leanre/leanre.py decompile dom UpperTheory.Lit.every_character_of_theta_integrals_local_matching --depth 3 --min-size 2000
python3 leanre/leanre.py decompile contract GlobalTheory.Fc.HypsAlt            # 46 fields
python3 leanre/leanre.py decompile contract Formalism.BasicNotions.ColumnChain # abstract carriers
python3 leanre/leanre.py decompile contract Formalism.MainNotions.Closed --body
python3 leanre/leanre.py decompile contract Formalism.MainNotions.DesignChoices --body
python3 leanre/leanre.py decompile validate outputs/decomp/pillar_theta.json
sed -n '44p;69,73p' data/rh_mirror/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean
```
