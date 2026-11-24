# Pillar A Sibling Subtrees: `ontoX_and_lamLow`, `GalC.final_alt_alt`, and `open0`

> **Target:** `ontoX_and_lamLow`, `GalC.final_alt_alt`, and `open0` (`85,932` dominated decls, `19.0%` of Pillar A's `451,610`-decl producer), complementing [the `StageU` existence audit](./stageu_existence.md), [the `AllRowsAlt` engines audit](./allrows_engines.md), and [the `StageU` spine](./stageu_hyps_spine.md); companion JSON `outputs/decomp/pillar_a_onto_galc_open0.json` (`316` nodes covering all `244` nodes `>= 500` decls, `681` edges, `3` Horn clauses, `5` claims, `86` `OPAQUE` entries) `[L]`.
> **Kernel check:** `0` `sorryAx`, `0` custom axioms/`opaque` decls, standard `[propext, Classical.choice, Quot.sound]` (`40e56bab` / `kernel.db` `ALL` `tree_id=0`; see [Scope & Tag Legend](README.md)).

---

## 1. Overview & Contract Unfoldings (`85,932` Decls / `19.0%` of Pillar A) `[L]`

| Subtree Root | `dom` Decls | Transitive Cone | Nodes `>= 500` | `GlobalTheory.T.*` (`vn == 1` / Total) | Target Contract & Mathlib Ground Primitives |
| --- | ---: | ---: | ---: | ---: | --- |
| [`GlobalTheory.Fc.S0.ontoX_and_lamLow_of_unitaryGroupHypotheses'`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SurjectiveAndLowWeightOfUnramifiedExponents.lean#L16) | `34,969` | `400,389` | `84` | `903 / 909` (`897` `*Statement`, `696` 1-child shells) | [`SurjectiveOntoX`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExportSt.lean#L47) (`IndefData.ON`) ∧ [`LambdaLowerBound₂`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Realised.lean#L126) (`IndefData.L6`): `Finset.sum` over `HeightOneSpectrum (𝓞 K)` (`S.Iw`, `ramw`, `plc`, `lw`) and `N.l6 j ≤ Real.log (S.lam j μ0 p v)`. |
| [`UpperTheory.GalC.final_alt_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CFinal.lean#L19) | `28,195` | `346,702` | `86` | `789 / 814` (`763` `*Statement`, `709` 1-child shells) | [`mainTheorem`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MainTyzTer.lean#L22): `BoundAtTwoThreeFamilyFonAlt → LinkN` (`Summable (vvTerm D) → etaSum ≤ dZ0 * (... + tsum (vvTerm D))` via `ShaFinOdd`, `Real.log`, `ENat`). |
| [`GlobalTheory.T.open0_of_unitary_group_hypotheses`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OpenOrbitOfUnramifiedExponents.lean#L75) | `22,768` | `469,996` | `74` | `1,334 / 1,370` (`1,317` `*Statement`, `1,080` 1-child shells) | `12`-field [`OpenParameterStatements`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/GeometricWeakTies.lean#L39) (`hPA..df`) via `LinkedAt` / `Lg1` into [`DefiniteSideCondition`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DefiniteSideCondition.lean#L25) (`Submodule`, `Matrix`, `Real.log`, `HEq`). |
| **Total (`19.0%` of `451,610`)** | **`85,932`** | *(shared)* | **`244`** | **`3,026 / 3,093` (`97.8%`)** | `73,574` theorems, `11,914` defs, `444` inductives; `0` `axiom`/`opaque`. |

---

## 2. `ontoX_and_lamLow_of_unitaryGroupHypotheses'` (`34,969` Decls) `[L]` `[S]`

Reads `18` projections of `P : UnitaryGroupThirdPlaceHypotheses` (including `P.litN.loc` → `UpperTheory.One.M.New.llOf_alt` for `RecTExists`) and splits into [`ontoX_of_hypotheses_alt_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OntoXOfPrints.lean#L28) (`34,362`) and [`lamLow_of_hypotheses_alt_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LamLowOfPublished.lean#L17) (`556`):

```text
34,969  ontoX_and_lamLow_of_unitaryGroupHypotheses'
├── 34,362  ontoX_of_hypotheses_alt_alt                      # -> SurjectiveOntoX (IndefData.ON)
│   ├── 10,151  runHolds_of_parOK -> 8,558 exists_indexBoundHypothesesWithNet_allValuedPoints
│   │   ├── 3,839 exists_primeData_curve_lifting_heightBounds -> 1,410 G.T0.Data.heights (516 exists_realisationPrimeData) [OPAQUE]
│   │   ├── 1,287 cmFamilyFunctionals_detect_lowCoefficients -> 1,035 exists_fj_ne_zero_at_split_point' [OPAQUE]
│   │   ├── 1,204 recursive_page_lattice_bound -> 1,154 quotientBound -> 861 cmArcDatumFamily_functional_bounded_linear [OPAQUE]
│   │   ├── 1,274 inputs4_of_net; 1,057 sharesAt_all [OPAQUE]
│   ├──  7,949  geoSt_of_pageSt_alt -> 7,525 leafDepth_all_record -> 7,274 depthTable_goodPrimes_of_chartForm
│   │   ├── 5,271 allGoodPrimeDepthDataExist_proof -> 2,799 exists_pkgCs_of_degree_bound_at_inert_primes [OPAQUE]
│   │   └── 1,704 depthLeaf_goodPrimes_of_point_data -> 1,596 depthTable_goodPrimeLeaf -> 1,506 goodPlaceDepthBound_proof [OPAQUE]
│   ├──  7,245  expSt_of_base_change_and_crystalline_lattices -> 7,244 exponent_bound_of_unitaryThetaStandardTheorems_alt
│   │   ├── 3,242 model_statement_of_crystalline_chebotarev_frame_gal -> 2,438 crystallineLatticeLink -> 2,188 wachLattices (937 record_nonempty) [OPAQUE]
│   │   ├── 2,321 expSt_of_num_sumExp_model -> 1,741 primePowerLatticeInclusion_of_localModels -> 1,486 inclusion_w_seven_real_holds [OPAQUE]
│   │   └──   505 galois_frame_compatibility_alt -> 504 galois_steinberg_local_alt [OPAQUE]
│   ├──    996  exportSt_of_reciprocity_and_casselman_wallach -> 993 exportSt_of_hypotheses_alt [PARTIAL]
│   ├──    832  ontoX_of_twist_shares_exp_alt (ignores hExport; invokes runs_estimate_statement' 474 & onto_x_of_all_estimates 351)
│   └──    542  compareOffOwn_atRuns_alt -> 540 traceLattice_le_span_thetaSeries_awayFromOwnPrime [OPAQUE]
└──    556  lamLow_of_hypotheses_alt_alt -> 463 finiteness_inputs_real_data_three_alt -> 315 adelC_of_parameter_choice_stdV
```

- **Spectral onto map (`ontoX`):** `ontoX_of_hypotheses_alt_alt` derives `RayClassFieldSt` and `SeriesRatS` from `HeckeLAdicCharacter.globalArtin`, builds `ExportedStatement` (`996`), combines `pageSt_alt` (`100`) → `geoSt_of_pageSt_alt` (`7,949`) + `compareOffOwn_atRuns_alt` (`542`) into `RankAtPlaces` and `TwistStatement'`, builds `ShareStatement` (`modelSt_alt` `305`) and `BadPlacesStatement` (`badWSt_of_greenCuspidal_of_modelSt` `232`), attaches `ExponentStatement` (`7,245`), and closes `SurjectiveOntoX` (`IndefData.ON`) via [`ontoX_of_twist_shares_exp_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OntoXOfTwistSharesExp.lean#L21) (which uses `intro _ hT hS hB hE`, ignoring the direct `hExport` already folded into `hTwist`, and pulls height/threshold runs from `runHolds_of_parOK` `10,151` and `runs_estimate_statement'` `474`).
- **`LambdaLowerBound₂` (`lamLow`, `556` decls):** [`lamLow_of_hypotheses_alt_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LamLowOfPublished.lean#L17) lifts `closed_Csz_ge FamHyp 8`, pulls `thetaLift_weightSizes_eventually_along_family` (`5`) + `hookLogSum_sub_sizeTerm_le_lowerBound` (`31`), sets error coefficient `0` (`_ - C * 0 ≤ _` by `le_rfl`), and calls [`finiteness_inputs_real_data_three_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/FinitenessInputsRealDataThree.lean#L35) (`463`) → [`adelC_of_siegelWeil_of_doubling_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/FinitenessInputsRealData.lean#L13) (`314`, ignoring `_hSWc` and passing `hDbl` via `ResidueKilled.sec_of_dm`).

---

## 3. `UpperTheory.GalC.final_alt_alt` (`28,195` Decls) `[L]` `[S]`

```text
28,195  UpperTheory.GalC.final_alt_alt                       # -> MainTyzTer.mainTheorem (BoundAtTwoThree -> LinkN)
├── 26,622  UpperTheory.GalC.final_of_alt                    # cuts along CutD D, transports GaloisPreconditions + Tie4
│   ├── 25,757  linkedAt_linkN_of_boundAtTwoThree -> 25,756 linkN_of_boundAtTwoThree_slot -> 25,755 linkN_of_twGood_galoisPreconditions
│   │   ├── 18,289  conclF_of_family_facts_and_bound_at_two_three -> 18,288 NLinkClose.main_alt_alt
│   │   │   ├── 6,332 star_ad_and_bb_le_of_joint_cond -> 6,281 adm_at_inert_of_range (3,425 thmB_closing, 2,555 thmC) [OPAQUE]
│   │   │   ├── 3,966 eventually_congBound_of_facts -> 3,292 blochKatoTop_of_localTateDuality_eulerChar (2,975 thmTOP) [OPAQUE]
│   │   │   ├── 3,326 theoremE_corollaryA_closing_all_data -> 3,256 Ln03.corollary_local_exists_constant (1,697 crystalline_lifting, 1,272 thmE) [OPAQUE]
│   │   │   ├── 2,421 embedding_jumps_aux2_of_setup -> 2,346 twistedPlace_selmerLengthBound_of_localDuality (2,155 thmA) [OPAQUE]
│   │   │   └──   689 fam_jointBCD_closed_alt -> 647 fam_jointBCD [OPAQUE]
│   │   └──  6,332  exists_const_tieChi_bound_of_facts -> 5,438 exists_bound_tieChi_of_prints -> 5,436 conclusion41_of_pAdicHodge_alt
│   │       ├── 5,144 crystallinePeriodBound_all_constant_ge_forty -> 5,036 theoremT_of_bhattScholze -> 4,681 lift_surjection_good_crystalline_lattices -> 1,406 breuilKisin [OPAQUE]
│   │       └──   725 no_cut_passes_of_artin_reciprocity -> 724 stepsNoCut_of_artin_alt [OPAQUE]
│   └──    836  tieChi_at_members_of_depthZero -> 788 tieChi_at_mem_of_depth_zero_inputs -> 662 locComp [OPAQUE]
├──    675  UpperTheory.GalC.exists_good_cut_facts_tie4 (pre_cut_alt + facts_of_galois_preconditions_of_cutRec -> NormChoiceFacts)
└──    152  UpperTheory.GalS.galois_preconditions_at_mem -> 49 core0_of_local_duality_inputs -> GaloisPreconditions
```

- **Exact Galois-criteria discharge & `UnusedSlot55`:** [`galois_preconditions_at_mem`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PreAtMem.lean#L86) constructs [`GaloisPreconditions`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/GaloisPreconditions.lean#L13) (`what₂, adm, Conclusion1, z, rhoBar, g3p, c2, large, trip, same, good`). Inside [`exists_good_cut_facts_tie4`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CFacts.lean#L58), `exists_good_alt` picks `c : CutD D` with `c.Good`, [`pre_cut_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CFacts.lean#L23) restricts `GaloisPreconditions` to `cut D c` (preserving `R.a.g4p : CuspidalGaloisUnramified'` = [`UnusedSlot55`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean#L89) `:= True` inside `provisionFirst` beside live `G4`), and [`facts_of_galois_preconditions_of_cutRec`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CFacts.lean#L45) supplies `Conclusion2` (via `LocalTateDuality`/`LocalEulerChar`), `g2`, `admJ`, and `duties` (`NormChoiceFacts`).
- **Exact `h23` / `BoundAtTwoThreeFamilyFonAlt` routing:** At the top contract [`linkN_of_boundAtTwoThree_slot`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean#L54), `obtain ⟨K, hK⟩ := hcl e he hle` **drops the external `h23` bound `hK` unused**. One call deeper in `linkN_of_twGood_galoisPreconditions`, [`at23_family_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/At23OfAll.lean#L19) (`41` decls in the shared cone) **re-proves** `BoundAtTwoThreeFamilyFonAlt` directly from `hP : Hypotheses₂` (`P.nLink`) and feeds it to [`conclF_of_family_facts_and_bound_at_two_three`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ImportsFurtherTailStatement.lean#L11) (`18,289`). Inside [`ImportsFurtherTail.main_alt_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ImportsFurtherTail.lean#L22), that internal `h23` **is genuinely consumed** (`obtain ⟨Ca, xa, ha⟩ := h23`) alongside `starSF_of_prints` to prove `htwo : StarF (Fm.L x i) X.ρ ...`, closing `ConclF` → `linkN_along_family_of_localBounds` → `LinkN`.

---

## 4. `GlobalTheory.T.open0_of_unitary_group_hypotheses` (`22,768` Decls) `[L]` `[S]`

[`open_orbit_of_unramified_exponents_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OpenOrbitOfUnramifiedExponents.lean#L39) (`22,767` decls) packs all `12` fields of [`OpenParameterStatements`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/GeometricWeakTies.lean#L39) using `23` fields of `UnitaryGroupThirdPlaceHypotheses` (`97.0%` of its `dom` weight sits in two engines):

```text
22,768  GlobalTheory.T.open0_of_unitary_group_hypotheses -> 22,767 open_orbit_of_unramified_exponents_alt
├── 20,146  main_theorem_published_inputs_third_alt_alt -> 20,145 miStarRow_alt_alt (MIstar2 ∧ RowMultiplicityCondition -> mi, hDivG)
│   └── 19,762 main_theorem_published_inputs_variant_alt_alt -> 19,265 main_theorem_published_results_final_alt_alt -> 18,804 main_theorem_from_published_results_alt_alt_alt_alt_alt
│       └── 17,877 true_geometry_family_row_data_alt -> 17,876 famAllQ_of_allTrue_alt
│           ├── 6,300 true_geometry_family_invariance_alt -> 2,082 laws_resc_alt -> 2,079 seeSawTwistPlaceLaws -> 1,250 seeSawIteratedIntegralLaw -> 1,081 doubleStep_adelicIntegral -> 500 iteratedInnerIntegral [OPAQUE]
│           ├── 4,105 true_geometry_family_column_data_alt -> 2,156 seeSaw_latticeFramePins_finiteIntegralLaws (762 lawLevelPrime_all, 522 seeSawUnfolded) + 742 cls_pin_d [OPAQUE]
│           ├── 2,312 exists_botDat_of_placedP_framed -> 781 exists_isAt_of_placed_framed [OPAQUE]
│           └── 1,330 all_true_family_datum_alt -> 709 local_component_vector_relation_alt -> 602 local_component_measure_identity [OPAQUE]
├──  1,930  weil_unitary_entries' -> 1,929 linkedAt_prmR_df_of_cuspRapidDecay (drops all 4 published hyps!) -> RowDefectCondition (df)
│   └── 1,780 definiteSideCondition_of_nprimeDef_of_nuFull -> 1,779 kernel_columns_from_ties_alt -> 1,778 rowsU_of_colPins_alt -> 1,704 memberRows_of_kernelDatum_sizes -> 1,342 kernelHalf_chainNumbers_any_levelPrime [OPAQUE]
└──    691  remaining 10 fields: good_ft_entries (396 -> lab), harish_chandra_inputs (80 -> kap), linkedAt_tie (30 -> tie), linked_bundles_good (29 -> good), bk_law_entries (9 -> hDivG), entries_combined_real (8 -> selJ), linkedAt_geometricWeakTies (7 -> geo), hPA (4), real_group_inputs (4 -> hLamP), hDcPtG (3)
```

Specifically, [`weil_unitary_entries'`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PointEvaluationSideStatement.lean#L14) (`1,930`) delegates to [`linkedAt_prmR_df_of_cuspRapidDecay`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PointEvaluationSide.lean#L85), which ignores its 4 published arguments (`fun _ _ _ _ => linkedAt_df_of_parameters ...`) and proves `DefiniteSideCondition` internally from `PointEvaluationSide` and `rowsU_of_colPins_alt` (`1,778`), while `ontoAll_of_theta_doubling` and `mi_star2_of_pu_nz` consume the published inputs from the shared cone under `miStarRow_alt_alt` (`20,145`).

---

## 5. Adversarial Audit Across All `85,932` Decls `[L]` `[M]`

| Check Class | `ontoX_lamLow` (`34,969`) | `GalC` (`28,195`) | `open0` (`22,768`) | Ground-Truth Verdict |
| --- | --- | --- | --- | --- |
| `sorryAx` / `axiom` / `opaque` / `ofReduceBool` | `0` | `0` | `0` | Clean kernel terms (`thm`/`def`/`inductive` only). |
| `decide +kernel` / taint | `4` `decide_kernel` (`loop_run` timeout, `lcmUpto`, `table_ok`, `BB_disj0`) + `5` small-`ℕ` patterns | `0` | `3` small-`ℕ` patterns + `1` [`kexactB`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemLevelIffTwistedClass.lean#L165) (`MemLevelIffTwistedClass:165`) | [`loop_run`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/SmallLoop.lean#L24) is the **sole live `lean4lean` default-fuel timeout**; [`table_ok`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L301) & [`BB_disj0`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L554) are finite prime checks. |
| `*junk*` / `UnusedSlot*` | `0` `*junk*`, `0` `UnusedSlot*` | `0` `*junk*`, `2,047` `UnusedSlot80` | `0` `*junk*`, `2` `UnusedSlot33` edges | `UnusedSlot80` (Breuil–Kisin/Wach lattices) & `UnusedSlot33.HK` (conjugation) are real math; [`UnusedSlot55`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean#L89) (`:= True`) enters `GalC` from outside via `GaloisPreconditions` beside live `G4`. |
| `Empty` / `Unit` / `PUnit` / `True` / `IsEmpty.elim` | [`mpTrivialAb`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/Divisibility/LocalNonemptiness/SubsingletonRankIndicatorIff.lean#L574) + [`provWithPoints`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLocalDataPrescribedPointsFlag.lean#L308); `trivialClassCondition`; `9` `isEmptyElim` | `3` `isEmptyElim`, `5` `Nonempty.elim`, `EmptySecondBlock` | `7` `isEmptyElim`, `1` `Nonempty.elim` | **Key finding in `ontoX`:** `exists_prov_prescribed_points` (`97` decls under `runs_estimate_statement'` `474`) fills unused curve/moduli/line-bundle slots of `ModuliIntegralCharts.Prov` with `Empty`/`Unit`/`PUnit`/`True` while retaining real `Ylat`/`be_posDef`/`Pm` lattice data; [`trivialClassCondition`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/ProjectiveLattices/ValSetAlgSubset.lean#L14) strengthens `regular₂` universally; `EmptySecondBlock` & `isEmptyElim` handle genuine empty-block / out-of-range guards. |
| `Degenerate` / `trivial` | `23` `Degenerate` (`AlphaPair`, `NondegenerateCharts`) | `7` `Nondegenerate` (`traceSemisimple`) | `5` `Degenerate` (`degenerate_and_collisions_uncond`) | Real nondegeneracy hypotheses and degenerate-collision error bounds (`0` vacuous `:= trivial` conclusions). |

<details>
<summary>Verify locally & key pinned anchors</summary>

```bash
python3 leanre/leanre.py decompile validate outputs/decomp/pillar_a_onto_galc_open0.json
python3 verify/p4_decomp_check.py outputs/decomp/pillar_a_onto_galc_open0.json
python3 verify/p4_analysis_check.py analysis/pillar_a_onto_galc_open0.md
python3 verify/r3_audit.py && python3 verify/audit_tree.py --leak
```

- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SurjectiveAndLowWeightOfUnramifiedExponents.lean:16` (`ontoX_and_lamLow_of_unitaryGroupHypotheses'`, 34,969)
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CFinal.lean:19` (`UpperTheory.GalC.final_alt_alt`, 28,195)
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OpenOrbitOfUnramifiedExponents.lean:75` (`GlobalTheory.T.open0_of_unitary_group_hypotheses`, 22,768)
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean:54` (`UpperTheory.GalC.linkN_of_boundAtTwoThree_slot`, 25,756)
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ImportsFurtherTailStatement.lean:11` (`GlobalTheory.T.conclF_of_family_facts_and_bound_at_two_three`, 18,289)
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MainTheoremPublishedInputsThird.lean:34` (`GlobalTheory.T.main_theorem_published_inputs_third_alt_alt`, 20,146)
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PointEvaluationSideStatement.lean:14` (`GlobalTheory.T.weil_unitary_entries'`, 1,930)
- `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/SmallLoop.lean:24` (`PI.PC.loop_run`, 2)
- `src/Formalism/SharpRestriction/Divisibility/LocalNonemptiness/SubsingletonRankIndicatorIff.lean:574` (`mpTrivialAb`, 2)

</details>
