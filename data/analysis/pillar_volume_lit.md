# Pillar D (`SelfIntersectionVolumeEstimates`) & Literature / Published Theorems Audit

> **Target:** **Pillar D** (`SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt`, `80,720` decls) and the remaining **`305,998`-decl** literature/published subtrees under `every_character_of_literature_of_vWin` (`849,323` decls total, outside Pillar A's `543,325` decls), plus shared-diamond classical pillars (`globalEulerChar_full`, `abelianDeRham`, `harishChandraFinite`, `localConverseGL`, `gsBaseCase`, `poitouTateNormalised_holds`) at `40e56bab` (`kernel.db` `ALL` `tree_id=0`) `[L]`.
> **Kernel check:** `0` `sorryAx`, standard axioms `[propext, Classical.choice, Quot.sound]`; unread bodies stay `OPAQUE` (see [Scope & Tag Legend](README.md)).

---

## 1. Executive Summary & Top-Level Footprint

1. **Where Pillar D + Literature sit under `every_character_of_literature_of_vWin` (`849,323` decls)** `[L]`:
   - `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (`EveryCharacterOfLiteratureOfVWin.lean:810`) has `51,363` direct dominator children in `kernel.db` (`dom.tree_id=0`, summing to `849,322` descendant decls).
   - Pillar A (`UpperTheory.Lit.every_character_of_theta_integrals_local_matching`) dominates `543,325` decls (`63.97%` of `849,323`). The remaining **`305,998` decls (`36.03%`)** belong to Pillar D (`80,720`), the named `*_of_literature` / `published_results_*` subtrees (`~36k+` directly under `every_character_of_literature_of_vWin`, plus shared classical libraries), and geometric/analytic infrastructure.
2. **Pillar D (`80,720` decls) is real, non-vacuous Arakelov / covering-volume machinery, but lives in a split coordinate-ring + `IntersectionSystem` abstraction** `[L]`:
   - It proves `GlobalTheory.CovTop.CovolumeBoundOfX` (`LiftLambdaBound.lean:60`), a project-specific covolume/lattice-point bound `(p.S false).L3 (p.N C CH)` on `Closed FamHyp` theta-lift families.
   - Its `46,110`-decl core (`PositivityTheory.HtPt.Ah.deep_slim_use`) translates 8 arithmetic-geometry theorems into `Plug.DeepStR` (`MeanAll` slope/volume inequalities with paper-specific bounds `D.R.m^2 ≤ D.R.k`, `primeFactors.card ≤ 15`, `3 * D.q + 1 ≤ D.p + D.q`, `T.bad.card ≤ 4 * |CMType H| * (D.p + D.q)^2`).
   - The Arakelov/Hilbert–Samuel core (`MoriwakiBigStatement`, `HSUse`, `PoincareLelongInv`, `NefRR`, `hsChain`) is formulated over **multigraded polynomial coordinate rings `MRing ι`** and **quantified universally over any `II : IntersectionSystem` satisfying the 3 axioms of `IsIntersectionFamily`**, rather than directly on general abstract schemes — and then **`arithIntersectionSystem_of_poincareLelong_resK` (`468` decls) constructs an explicit `II` satisfying `IsIntersectionFamily`**, discharging `moriwakiBig_outright` and `hsUse_outright` with zero axioms `[L]`.
3. **The `OpenLiteratureStatements` (`195` vs `185`) reconciliation is exact** `[L]`:
   - `EveryCharacterOfLiteratureOfVWin.lean` contains **195 `theorem` declarations**: **185** single-theorem `:=` consequences (`L219–588`), **9** `where`-record assemblers (`L589–781`), and **1** top theorem (`every_character_of_literature_of_vWin`, `L810`).
   - Only **4 of 195** theorems (`jae-63` `[C]`) directly project a field of `O : OpenLiteratureStatements`: **3** among the `185` (`keithadler` `[C]`'s `3 + 30 + 152 = 185` split) plus `literature_automorphy` (`L618`: `car := O.caraianiLocalGlobalDual`) among the `9` record assemblers.
   - In `everyCharacter_of_row` (`MainConclusion.lean`), all 3 fields of `O` are filled by proved in-repo theorems `⟨h, recTExists, h⟩` `[L]`.
4. **Classical "Famous Theorems" span genuine Mathlib-grounded theorems, narrow unitary specializations, and one `True` dummy slot** `[L]`:
   - **Genuine (`FULL/GENUINE`):** `GlobalEulerChar` (`2,710`), `PoitouTateNormalised` (`502` + `gsBaseCase` `872`, with standard `l ≠ 2 ∨ IsTotallyComplex F` condition), `AbelianDeRham` (`2,281`), `LocalConverseGL` (`924`, `[CharZero k]`), `SiegelToroidalIntegral` (`5,446`), `ToroidalForFanKS` (`7,185`), `SemiAbelianLieSeminegative` (`806`, `[CharZero k]`), `FarguesExact` (`107` + `prismaticDieudonneHodge` `2,373`), `PointSeparationPair` (`96`), `ResolutionCharZero` / `functorialResolutionCharZero` (`2,144` + `5,400`), `PrincipalisationCharZero`, `GrothendieckDeformation`, `ArithHilbertSamuel`, `L2ExtensionLogCanonical`, `BhattScholzeIntegral`, `StrongApproxSU` (`699`, statement read).
   - **Narrow / Specialized (`NARROW/SPECIAL-CASE`):** `HarishChandraFinite` (`2,133`, specialized to project unitary spaces `GA D V`), `ZarhinStatement` (`411`, `(A × A^∨)^4` over valuation rings of algebraically closed fields), `ThetaIntegralsAgree ∧ LocalMatching` (`14,173`, unitary `Spc F E` models), `ArDegree` (`416`), `WeilSiegelFormulaUnitary` (`2,495`), `DiscreteSeriesClassification` (`2,333`), `FlathFactorisation` (`1,193`), `CasselmanWallach` (`619`), `GoodChernWeil`, `JacquetShalika` (`IsTotallyComplex E`).
   - **Wrapper / Dummy (`WRAPPER/OPAQUE`):** `published_results_arithmetic` (`7,105`), `published_results_eigen` (`4,339`), `published_results_first` (`4,078`) are pure `Prop`-record assemblers; inside `published_results_eigen`, field `siegelEisensteinSimplePole` has type `GlobalTheory.Published.UnusedSlot72`, which is literally **`abbrev ... : Prop := True`** (`DiscreteSpectrumResidualClassification.lean:7`), proved by `trivial` (`EveryCharacterOfLiteratureOfVWin.lean:505`) `[L]`!

---

## 2. Pillar D: `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` (`80,720` decls)

### 2.1 Architecture & Dominator Spine

`SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` (`TopCovolSlim2Use.lean:16-22`, `dom.subtree = 80,720`, `idom = every_character_of_literature_of_vWin`) takes **15 hypotheses** (all discharged by proved `*_of_literature` or `*_outright` lemmas in `EveryCharacterOfLiteratureOfVWin.lean:812`) and returns `_root_.GlobalTheory.CovTop.CovolumeBoundOfX` `[L]`.

Its `80,720`-decl dominator subtree splits cleanly into three parts `[L]`:

| Branch / Node | Kernel `id` | `subtree` | Module Anchor | Role in Pillar D |
|---|---|---:|---|---|
| `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` | `1186805` | `80,720` | `ThirdPlaceSeries/TopCovolSlim2Use.lean:16` | Pillar D root → `CovolumeBoundOfX` `[L]` |
| ├─ `PositivityTheory.HtPt.Ah.deep_slim_use` | `1186804` | `46,110` | `HilbertSamuelApplications/AhSlimU.lean:9` | Arakelov/Hilbert–Samuel/tower chain → `Plug.DeepStR` `[L]` |
| │  └─ `GlobalTheory.CompanionTheory.Ar.Plug.deepStR_of_use` | `1184111` | `45,411` | `HilbertSamuelApplications/DeepStROfUse.lean:12` | Dispatches `lineOfLargeDegree_of_use`, `given_of_use`, `good_tower_volume_theorem_bis`, `deepStR_of_volume` `[L]` |
| │     ├─ `GlobalTheory.CompanionTheory.Ar.Link.good_tower_volume_theorem_bis` | `1182065` | `31,846` | `HilbertSamuelApplications/GoodTowerVolumeTheoremBis.lean:9` | → `GoodTowerExistsX ∧ VolumeTheoremX` `[L]` |
| │     │  └─ `GlobalTheory.T.final_theorem_of_inputs_right` | `1182058` | `31,842` | `GeometryProofs/FinalTheoremOfInputsRightStatement.lean:19` | Wrapper → `goodTower_volume_of_reduced` (`31,841`) `[L]` |
| │     │     └─ `GlobalTheory.T.good_tower_volume_theorem` | `1182056` | `27,142` | `DivisibilityProofs/GoodTowerVolumeTheoremStatement.lean` | → `goodTower_and_volume` (`27,141`) → `volume_theorem_of_inputs` (`13,623`) `[L]` |
| │     ├─ `GlobalTheory.CompanionTheory.Ar.Plug.deepStR_of_volume` | `1184110` | `2,012` | `GeometryProofs/DeepStROfVolume.lean:21` | `VolumeTheoremX` + `abelian_cm_comp_laws_bound` (`1,827`) → `DeepStR` `[L]` |
| │     ├─ `GlobalTheory.T.final_theorem_of_inputs_left` | `1133286` | `1,707` | `GeometryProofs/FinalTheoremOfInputsLeftStatement.lean` | Builds `Top.Given` (`1,706` via `given_of_inputs`) `[L]` |
| │     ├─ `GlobalTheory.CompanionTheory.Ar.Giv.lineOfLargeDegree_of_use` | `1130615` | `1,617` | `HilbertSamuelApplications/LineOfLargeDegreeOfUse.lean:10` | Dual metric energy + stacked graph → `LineOfLargeDegree.Statement` `[L]` |
| │     └─ `GlobalTheory.CompanionTheory.Ar.Link.given_of_use` | `1146018` | `1,122` | `HilbertSamuelApplications/GivenOfUse.lean:11` | `nineFree_of_use` (`357`) + `inputs_of_use` → `Top.Given` `[L]` |
| ├─ `SelfIntersectionVolumeEstimates.topCovolG_alt_alt` | `1125207` | `20,154` | `ThirdPlaceSeries/TopCovolG.lean:39` | Covering-geometry & Bergman/Gram height chain → `CovolumeBoundOfX` `[L]` |
| │  ├─ `SelfIntersectionVolumeEstimates.height_lower_bound_general_alt` | `1119235` | `2,954` | `ThirdPlaceSeries/HeightLowerBoundGeneral.lean:21` | `HeightCondition` from `DeepStR`, `VolumeEstimateHypotheses`, Bergman section bounds `[L]` |
| │  ├─ `PublishedHodgeBundleTheorems.toClassicalTheorems` | `1102749` | `1,817` | `HodgeBundleWeights/CoveringTopologyRefinement.lean:10` | Adds `toroidalFlagProportionality_of_goodChernWeil` (`1,801`) → `Hypotheses''` `[L]` |
| │  ├─ `GlobalTheory.T.coverHeightSum_of_flatDeg_coverDegree_share` | `1121056` | `1,607` | `ThirdPlaceSeries/HilbertSamuelLowerBoundOfComponents.lean` | Hilbert–Samuel lower bound over covering components `[L]` |
| │  ├─ `GlobalTheory.T.lowDef_of_gram_of_anchor` | `1122612` | `1,215` | `ThirdPlaceSeries/CoveringLowDefectBound.lean` | Low-defect covering bound from Gram matrix & anchor `[L]` |
| │  ├─ `GlobalTheory.T.orbits_separated_by_regular_cusp` | `1124083` | `1,014` | `HodgeBundleWeights/ExistsCuspRegularLevelDeterminant.lean` | Separates orbits via regular cusp level determinants `[L]` |
| │  └─ `UpperTheory.Lit.Tam.tamagawa_local_volume_factor` | `1116085` | `834` | `FockModels/TamagawaPeterssonLambdaSqNonneg.lean` | Local Tamagawa / Petersson $L^2$ nonnegativity factor `[L]` |
| └─ Shared direct dom siblings (`3,412` other direct children) | — | `14,456` | `GeometryProofs/`, `Heights/`, `HodgeBundleWeights/` | `FlatDegree_holds` (`990`), `germ_system_height_free` (`764`), `finite_constant_all_holds` (`612`), `mahlerSection` (`434`), `ChowFormSectionVertical.full` (`423`), `tanpf_inj` (`347`), `small_sections_injective` (`318`), `eigen_frames_analytic` (`304`), `chow_form_height_comparison` (`151`), etc. `[L]` |

### 2.2 Exact Contracts & Unfolding (`[L]`)

1. **`GlobalTheory.CovTop.CovolumeBoundOfX`** (`LiftLambdaBound.lean:60-61`):
   `def CovolumeBoundOfX : Prop := Closed FamHyp fun Fm CH => ∃ C0 : ℝ, 0 ≤ C0 ∧ EventuallyAtAllPoints Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)`
   - Quantifies over closed theta-lift families `Fm` (`Closed FamHyp`) and proves that eventually in `x` (at all points `p` satisfying `RowsTAlt p`), the finite-index/covolume property `(p.S false).L3 (p.N C CH)` holds `[L]`.
2. **`GlobalTheory.CovTop.HypothesesX`** (`HypothesesX.lean:10-20`, `5` fields) and **`GlobalTheory.CovHt.HypothesesH`** (`SemiposAtOfPositive.lean:216-220`, `4` fields):
   - Pure `Prop` bundler records collecting `ToroidalForFanKS`, `SemiAbelianLieSeminegative`, `GreenCuspidal`, `PointSeparationPair`, `FubiniStudyChowHeight` (`HypothesesX`) and `SiegelToroidalIntegral`, `ToroidalChartsForFan`, `ToroidalCharts`, `ArDegree` (`HypothesesH`) `[L]`.
3. **`SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses`** (`VolumeEstimateHypotheses.lean:9-11` / `SelfInterBound.lean:10-14`):
   - `SelfIntersectionBound ∧ SmallSectionsInject`.
   - `SelfIntersectionBound` bridges an arbitrary integral scheme `X ⟶ Sp (𝓞 K)` with Hermitian line bundle `L : GlobalTheory.HermLB p` to a lattice/norm pair `(Nm, W)` via `GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s`, bounding the self-intersection `(L.shift t).IsSelfInter a` by `[K : ℚ] * (D + 1) * (imageDeg ev D * (imageHeight Nm W ev D + t))`. Proved by `ChowFormHeightComparison₂.chow_form_height_comparison` (`ChowFormHeightComparison.lean:11-12`).
   - `SmallSectionsInject` upper-bounds `(smallL ... (8*i) t).encard` by `((L.shift t).pow (8*i)).smallSec.encard` under `ImageModel.IsModelOf`. Proved by `PositivityTheory.Xj7N.small_sections_injective` (`SmallSectionsInjective.lean:13-14`).
4. **`GlobalTheory.CompanionTheory.Ar.Plug.DeepStR`** (`ModelSmall.lean:63-66`):
   - `∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → D.R.m ^ 2 ≤ D.R.k → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : GlobalTheory.CovTop.Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Y.d.l₂.M'.primeFactors.card ≤ 15 → GlobalTheory.CovHt.MeanAll Y.U (xiR D) (GlobalTheory.CovHt.ell D) C`
   - Here `MeanAll` (`SemiposAtOfPositive.lean:101`) is a mean slope lower bound `-C * errX s u g ≤ (∑ᶠ Z, sl Z) / #Comp` for `compVolSlope` across all components `Z : Comp Xo c` and gapped weights `WtGap u g`. Note the **paper-specific structural thresholds** `D.R.m ^ 2 ≤ D.R.k` and `M'.primeFactors.card ≤ 15` (`≤ 4 * |CMType| * (p+q)^2` in `DeepStROfVolume.lean:39-56`) `[L]`.
5. **`GlobalTheory.CompanionTheory.Ar.Top.GoodTowerExistsX` & `VolumeTheoremX`** (`GoodTowerExistsX.lean:22-36`):
   - `GoodTowerExistsX` gives a `RootTower (CMType H) (D.p + D.q)` and `GoodOrigin Y T` satisfying `o.Extra` (holomorphic charts with `fderiv ... .ker = ⊥` and `𝔐.R p = 4` on `o.S B`).
   - `VolumeTheoremX` asserts `T.Proportional ∧ T.VolEq ∧ T.T1 II ∧ T.ThmB II ... ∧ T.T2 II C ... ∧ T.MeanSlope II C ...` for any `IsFullIntersectionSystem II` when `1 ≤ D.q`, `3 * D.q + 1 ≤ D.p + D.q`, and `T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q)^2` `[L]`.
6. **The Arakelov / Moriwaki Bigness Engine (`MoriwakiBigStatement`, `HSUse`, `IsIntersectionFamily`, `hsChain`)** `[L]`:
   - **Coordinate-Ring Model (`IsIntersectionFamily.lean:13-95`):** `MRing ι := MvPolynomial (Σ k, ι k) ℤ`; `IsArithVar P d` is a relevant, horizontal (`P ∩ ℤ = ⊥`), multihomogeneous prime ideal of Krull dimension `d + |K|` (representing an arithmetic subvariety of $\prod_{k \in K} \mathbb{P}^{\iota_k}_{\mathbb{Z}}$); `HermLine ι` is a multidegree `a : K → ℤ` plus a positive scaling-covariant metric `h : ((Σ k, ι k) → ℂ) → ℝ`.
   - **Axiomatic Intersection System (`IsIntersectionFamily.lean:180-198`):** `IntersectionSystem` maps `(P, n, L : Fin n → HermLine ι) ↦ ℝ`, and `IsIntersectionFamily I` imposes 3 axioms:
     1. permutation symmetry `I P n (L ∘ σ) = I P n L`,
     2. additivity under tensor `I P (n+1) (snoc L (A.tensor B)) = I P (n+1) (snoc L A) + I P (n+1) (snoc L B)`,
     3. inductive Gillet–Soulé / Bost recursion `recR I P L A s` (summing `multAt * I W n L` over horizontal components, `geoNum * log(charOf W)` over vertical components, minus the archimedean `ptsIntegral` of `logNorm A s` against `dd^c log h_{L_j}`).
   - **`MoriwakiBigStatement`** (`MoriwakiSt.lean:29-36`) & **`HSUse`** (`SmallGeneratedCountUpperOfUse.lean:12-13`, `ArithKleiman ∧ G7 ∧ ArithmeticVolumeNef`): Both are proved **universally over any `II : IntersectionSystem` satisfying `IsIntersectionSystem II`** inside `hsChain` (`HSChain.lean`, `5,514` decls), then **instantiated outright** in `Outright.lean:9-15` (`moriwakiBig_outright`, `hsUse_outright`) via `arith_intersection_system_of_poincare_lelong` (`arithIntersectionSystem_of_poincareLelong_resK`, `468` decls).
   - **Verdict on Pillar D:** Genuine, substantial formalization of Moriwaki bigness, arithmetic Hilbert–Samuel, and covering-volume estimates (with zero `sorry` / custom axioms), classified **`NARROW/SPECIAL-CASE`** at the top interface (`topCovolSlim2_use_alt_alt` → `CovolumeBoundOfX`, `DeepStR`) due to paper-specific unitary/theta-lift thresholds, and **`ABSTRACT-RECORD`** (with a concrete `poincareLelong` witness!) at the `IntersectionSystem` / `MRing` core `[L]`.

---

## 3. `OpenLiteratureStatements` & Reconciliation of `195` vs `185` (`[L]` / `[C]`)

In `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215`):

1. **The `OpenLiteratureStatements` structure (`L215–218`):**
   A 3-field `Prop`-valued `structure` (`UpperTheory.LiteratureTheorems.OpenLiteratureStatements`) with fields `caraianiLocalGlobalDual : _root_.UpperTheory.One.M.Row`, `localLanglandsExists : _root_.UpperTheory.Zero.LLC.RecTExists`, and `galoisRepOfPolarizedPairLit : _root_.UpperTheory.One.M.Row` (`[L]`).
   In `MainConclusion.lean`, `everyCharacter_of_row h` constructs `⟨h, recTExists, h⟩ : OpenLiteratureStatements` from the proved in-repo theorems `galoisLocalGlobalStrong_recParameter` and `recTExists` (`[L]`).
2. **Exact Reconciliation of `195` (`jae-63`) vs `185` (`keithadler`) vs `186` / `199` / `262` in `kernel.db` (`[L]`):**
   - **Total `theorem` declarations in `EveryCharacterOfLiteratureOfVWin.lean` = `195`:**
     - **185** single-theorem `:=` consequences (`L219–588`) — this is `keithadler`'s exact `185` count (`PROOF-MAP.md:165–175`):
       - **3** directly project a field of `O`: `local_langlands_recT_exists_of_literature` (`L283`, `O.localLanglandsExists`), `pair_u_of_literature` (`L285`, `O.galoisRepOfPolarizedPairLit`), `carU_local_global_of_literature` (`L459`, `O.caraianiLocalGlobalDual`).
       - **30** forward `O` to other consequences.
       - **152** ignore `O` completely (`3 + 30 + 152 = 185`).
       - *(Naming split: `176` end in `_of_literature`; `9` do not: `logDerivOne`, `ellipticMainTheoremCM'`, `heckeTateFunctionalEquation'`, `hilbertClassFieldJ'`, `base_change_isobaric`, `doubling_method`, `siegel_eisenstein_simple_pole`, `zarhin_statement`, `localEulerChar_alt_alt`.)*
     - **9** `structure ... where` record-assembler theorems (`L589–781`): `literature_local` (`L589`), `literature_automorphy` (`L609`), `literature_cohomology` (`L626`), `literature_nonexistence` (`L639`), `published_results_analytic` (`L645`), `published_results_local` (`L658`), `published_results_eigen` (`L666`), `published_results_first` (`L727`), `published_results_arithmetic` (`L781`).
       - `literature_automorphy` (`L618`) directly projects `car := O.caraianiLocalGlobalDual` — making **4 of 195** theorems (`3 + 1 = 4`) that directly project a field of `O`, matching `jae-63`'s `BLUEPRINT.md:190–194` (`4` of `195`)!
     - **1** top assembly theorem: `every_character_of_literature_of_vWin` (`L810`, `849,323` decls).
   - **Total declarations in `EveryCharacterOfLiteratureOfVWin` inside `kernel.db` = `199`** (`195` theorems + `1` `OpenLiteratureStatements` inductive + `3` field projection theorems).
   - **Total `*_of_literature` declarations across ALL of `kernel.db` = `186`:** `176` from `EveryCharacterOfLiteratureOfVWin.lean` + `1` (`every_character_of_literature_of_vWin`) + `9` elsewhere in `Formalism`/`GlobalTheory` (`7` named theorems + `2` `_proof_1_*` auxiliary lemmas under `local_lemmas_of_literature`).
   - **Why `6` famous classical theorems sit at `idom = everyCharacter_of_row` instead of `every_character_of_literature_of_vWin`:** `kernel.db` also contains **63** `UpperTheory.LiteratureTheorems.*` declarations in `DenseThresholdCases.TemperedProductOfSquareIntegrable` (`OpenImageCondition` + `*_of_open`, used by `vwin_of_row`). Because both `*_of_literature` and `*_of_open` call `globalEulerChar_full`, `abelianDeRham`, `harishChandraFinite`, `localConverseGL`, and `poitouTateNormalised_holds`, their immediate dominator is pulled up to `everyCharacter_of_row` (`1373283`) `[L]`.

---

## 4. Classification of Named Literature & Classical Pillars (`[L]`)

Classification rubric:
- **`FULL/GENUINE`**: Statement matches standard mathematics over Mathlib ground types (fields, schemes, representations, measures) with non-vacuous proof in-repo (any standard scope conditions noted explicitly).
- **`NARROW/SPECIAL-CASE`**: Genuinely proved, but specialized to project-specific unitary/CM/theta models, restricted characteristics/fields, or narrow structural shapes relative to its famous name.
- **`ABSTRACT-RECORD`**: Statement is parameterized over an abstract axiomatic interface/structure (e.g., `IsIntersectionSystem II`).
- **`WRAPPER/OPAQUE`**: Record assembler / `O`-ignoring passthrough / `True` dummy slot, or body not unfolded (`OPAQUE`).

### 4.1 Subtrees Directly Under `every_character_of_literature_of_vWin` (`idom = 1254353`)

| Declaration (`subtree`) | File:Line Anchor | Underlying Prover (`subtree`) | Classification | Mathematical Reality & Receipts (`[L]`) |
|---|---|---|---|---|
| `theta_integrals_agree_and_local_matching_of_literature` (`14,173`) | `EveryCharacterOfLiteratureOfVWin.lean:565` | `PositivityTheory.ThKR.theoremK_head2` (`11,543`, `TheoremKOfMod.lean:26`) | **`NARROW/SPECIAL-CASE`** | Wrapper ignoring `O`. Proves `ThetaIntegralsAgree ∧ LocalMatching` (`WeilTensorModels.lean:581–592`) for unitary `Spc F E` models (`IsHerm`/`IsSkew`), Schwartz–Bruhat matching `RealMaps`/`FinMaps`, and `StepAlpha`/`StepBeta` shift identities via `closeSph` (`8,196`), `EisBL`, `SiegelWeilStd`. |
| `published_results_arithmetic` (`7,105`) | `EveryCharacterOfLiteratureOfVWin.lean:781` | Assembles 28 `*_of_literature` fields (`p1..p26, q1..q18`) | **`WRAPPER/OPAQUE`** | Pure `Prop`-bundle assembler (`PublishedHodgeBundleTheorems`, `ToKnownTheoremsOf.lean:7`); all 28 fields ignore `O`. Underlying theorems mix `FULL/GENUINE` (`ArithHilbertSamuel` `2,377`, `Principalisation`, `KawamataViehweg`, `ChowFormExists`, `L2ExtensionLogCanonical` `568`, `SemiAbelianHomExtension`) and `NARROW/SPECIAL-CASE` (`GoodChernWeil` `2,019`, `VolGe` `185`, `GreenSeriesSt`). |
| `siegel_toroidal_integral_of_literature` (`5,446`) | `EveryCharacterOfLiteratureOfVWin.lean:509` | `GlobalTheory.siegelToroidalIntegral_holds` (`5,445`, `SiegelToroidalIntegralHolds.lean:14`) | **`FULL/GENUINE`** | `SiegelToroidalIntegral` (`SiegelToroidalIntegral.lean:145–154`) states existence of projective toroidal compactifications `S ⟶ Sp (cycAway n)` of `SFam g n (zetaAway n)` for all `g ≥ 1`, odd `n ≥ 3`, with `IsSemiAbelian`, `HasChart` (`IsRegularLocalRing`, `PowerSeries`), and ample `hodge^k ⊗ BD⁻¹`. |
| `published_results_eigen` (`4,339`) | `EveryCharacterOfLiteratureOfVWin.lean:666` | Assembles 59 fields of `UnitaryGroupThirdPlaceHypotheses` | **`WRAPPER/OPAQUE`** | Record assembler (`BernsteinUnitaryProductIrreducible.lean:22`). **Contains a `True` dummy slot:** `siegelEisensteinSimplePole : GlobalTheory.Published.UnusedSlot72` where `UnusedSlot72 : Prop := True` (`DiscreteSpectrumResidualClassification.lean:7`), proved by `trivial` (`EveryCharacterOfLiteratureOfVWin.lean:505`). |
| `published_results_first` (`4,078`) | `EveryCharacterOfLiteratureOfVWin.lean:727` | Assembles 53 fields of `ThetaLocalInputs` | **`WRAPPER/OPAQUE`** | Record assembler (`LocalTypeDictionary/BernsteinUnitaryProductIrreducible.lean:6`), packing `kudla_splitting_split_unitary_of_literature` (`2,029`), `howe_duality_real_of_literature` (`636`), `cuspidal_mirabolic_of_literature` (`235`), `real_metaplectic_representation_of_literature` (`228`), etc. |
| `semi_abelian_lie_seminegative_of_literature` (`806`) | `EveryCharacterOfLiteratureOfVWin.lean:499` | `GlobalTheory.Nef.semiAbelianLieSeminegative` (`805`, `SemiAbelianLieSeminegativeBis.lean:22`) | **`FULL/GENUINE`** | Over any smooth projective geometrically connected curve `C / k` (`CharZero k`) and `IsSemiAbelian G` over `C`, any vector subbundle `W ↪ Lie G` has `deg(det W) ≤ 0` (`InterNumDetNonposSplitTorus.lean:23–27`). |
| `ar_degree_of_literature` (`416`) | `EveryCharacterOfLiteratureOfVWin.lean:251` | `PositivityTheory.Prw.arDegree_of` + `chernDegreeComplex` | **`NARROW/SPECIAL-CASE`** | `ArDegree = ArBirational ∧ ChernDegree` (`ArBirational.lean:13–25`): birational invariance of `HermLB.IsSelfInter` on `Scheme.{0}` + Chern integral identity on project `Var F`. |
| `zarhin_statement` (`411`) | `EveryCharacterOfLiteratureOfVWin.lean:547` | `PositivityTheory.HtPt.Narrow.zarhin` (`409`, `ZarTop.lean:6`) | **`NARROW/SPECIAL-CASE`** | Genuine Zarhin trick `(A × A^∨)^4` (`ZarhinStatementOfDualCubeQiR.lean:45–70`) over valuation rings `R` of algebraically closed fields `C`: any relatively ample `IsAbelianScheme A / Spec R` is a direct summand of a `PolAV`. Narrower than Zarhin's theorem over general Noetherian bases. |
| `fargues_exact_of_literature` (`107`) | `EveryCharacterOfLiteratureOfVWin.lean:549` | `UpperTheory.Lit.farguesExact` (`106`, `PrismaticDieudonneHodge.lean:27`) | **`FULL/GENUINE`** | Backed by `prismaticDieudonneHodge` (`2,373` decls). `PDivGroup p O` (`ToSpanSingletonConstGenInjective.lean:12–30`) is a concrete projective system of finite locally free cocommutative Hopf algebras over `O`; proves exactness of `hodgeTateLinear` / `dlogLinear` pairing (`FarguesExact.lean:10–18`). |
| `point_separation_pair_of_literature` (`96`) | `EveryCharacterOfLiteratureOfVWin.lean:471` | `NadelVanishingSeparation.NSI.pointSeparationPair` (`95`, `TopPointSep.lean:6`) | **`FULL/GENUINE`** | Genuine Angehrn–Siu point separation on projective normal integral schemes over `Spec ℂ` from klt log-canonical multiple + `c e^e < N₀^e / r^e` bounds (`PointSeparationPair.lean:15–30`), proved from `principalisation_closed`. |
| `toroidalForFanKS` (`7,185`) | `ToroidalCompactificationFanLogKodairaSpencerIso.lean:11` | `GlobalTheory.TorKSField.toroidalForFanKS` | **`FULL/GENUINE`** | Unitary Shimura toroidal compactification `Model Xo c id` with SNC boundary, Mumford charts, ample Hodge bundle, and `HasLogKS` (`ToroidalCompactificationBis.lean:45–54`). |
| `canonicalAlgorithmRules_isCorrect` (`5,400`) & `functorialResolutionCharZero` (`2,144`) | `PrincipalizationWithRadicalCenters.lean:42`, `HasSimpleNormalCrossingsOfInStrictNormalCrossing.lean:15` | Same | **`FULL/GENUINE`** | Functorial Hironaka resolution of singularities & radical-center principalization in characteristic 0 over Mathlib `Scheme.{u}`. |
| `hasSemiAbelianUniformisation_complete_normal_base` (`4,965`), `SiegelWeilCoefficients.field` (`2,533`), `weilUnitary` (`2,495`), `dsExhaust` (`2,333`), `strong_approx_su` (`699`), `casselman_wallach` (`619`) | See `outputs/decomp/pillar_volume_lit.json` | — | **`OPAQUE`** *(bodies unread)* | Statement headers read for `WeilSiegelFormulaUnitary`, `DiscreteSeriesClassification`, `StrongApproxSU`, `CasselmanWallach`; proof bodies not unfolded (`OPAQUE`). |

### 4.2 Classical Named Pillars in the Shared Diamond (`idom = everyCharacter_of_row`, `1373283`)

| Declaration (`subtree`) | File:Line Anchor | Classification | Mathematical Reality & Scope Notes (`[L]`) |
|---|---|---|---|
| `PositivityTheory.Lit1.GEN.globalEulerChar_full` (`2,710`) | `GlobalEulerCharOfLemmaX.lean:13`, `GalCoh.lean:157–162,226–231` | **`FULL/GENUINE`** | Tate's global Euler–Poincaré characteristic formula `|H0|*|H2|*|M|^[F:ℚ] = |H1|*archH0Card` for finite `ZMod (l^r)[G_{F,S}]`-modules (`l` prime, `r > 0`, `S` containing places above `l`), over Mathlib `NumberField`, `AlgebraicClosure`, `HeightOneSpectrum`, `Representation`, continuous cocycles `Z1/B1/Z2`. Proved via `ratioOne_of_lemmaX` (`2,024`). |
| `PositivityTheory.DualRT.abelianDeRham` (`2,281`) | `AbelianDeRhamDuality.lean:20`, `CrysToDRBijective.lean:24–67` | **`FULL/GENUINE`** | 5-part package (`Free`, `Hodge`, `BaseChange`, `Rigid`, `Duality`) for any `IsAbelianScheme A` over `Spec R` (`CommRing R`), including rank-`2g` projective `FirstDeRham`, wedge cup product, divided-power crystalline rigidity (`DividedPowers I`, `IsNilDP κ`), and polarization pairing duality. Backed by `abelianHodgeDeRham` (`1,898`). |
| `PositivityTheory.RgHf.harishChandraFinite` (`2,133`) | `FiniteOfCuspOfConstTerm.lean:129`, `HarishChandraFinite.lean:50–58` | **`NARROW/SPECIAL-CASE`** | Genuine constant-term + cusp-form finiteness proof (`Ψ : S →ₗ[ℂ] (∀ i, R i)`, `FiniteDimensional` of cusp forms + constant terms), but specialized to the project's unitary adelic spaces `GA D V` (`D : D7`, `V : HSp D`) with fixed `Formalism.REAL.KG` K-type and `gelf` eigenvalues — not general real reductive Lie groups. |
| `DiscreteGroups.sglob.LConv.localConverseGL` (`924`) | `LConvFinal.lean:18`, `LocalConverseGL.lean:12–17` | **`FULL/GENUINE`** *(char 0)* | Jacquet–Liu local converse theorem for cuspidal `IrrRep (GL (Fin (m+1)) k)` over any `[IsNonarchimedeanLocalField k] [CharZero k]`, proved from `HasPairEps` (`HasExponentZeroIff.lean:100–106`: Rankin–Selberg functional equation against all `GL (Fin m) k`). Restricted to `CharZero k`. |
| `GroundTheory.ProfCoh.gsBaseCase` (`872`) & `PositivityTheory.Lit1.PTN.poitouTateNormalised_holds` (`502`) | `PoitouTateNineTermGs.lean:23`, `PoitouTateNormalisedHolds.lean:18`, `PoitouTateNormalised.lean:12–28` | **`FULL/GENUINE`** *(`l≠2` or tot. complex)* | Genuine 9-term Poitou–Tate exact sequence, `ShaDual`, and `Hn = 0` (`n ≥ 3`) for finite `ZMod (l^r)[G_{F,S}]`-modules over `galUnramifiedOutside K ℚ̄ S`, under the standard scope condition `l ≠ 2 ∨ IsTotallyComplex F` (avoiding `l = 2` real-place archimedean subtleties). |

---

## 5. Skepticism & TCB / Vacuity Takeaways

1. **No top-level vacuity via `OpenLiteratureStatements` or `UnusedSlot72`:** `OpenLiteratureStatements` is completely discharged by proved in-repo theorems (`⟨h, recTExists, h⟩`), and `UnusedSlot72 := True` (`siegel_eisenstein_simple_pole := trivial`) only populates an unused field of the consumer bundle `UnitaryGroupThirdPlaceHypotheses` — it cannot make any downstream non-trivial theorem vacuously true `[L]`.
2. **Where abstraction hides complexity:** The Arakelov/Moriwaki engine (`MoriwakiBigStatement`, `HSUse`, `hsChain`) works in a bespoke multigraded polynomial ring model (`MRing ι`) and is universally quantified over an axiomatic `IsIntersectionFamily II` interface — though `arithIntersectionSystem_of_poincareLelong_resK` genuinely instantiates `II` `[L]`.
3. **Machine-readable artifact:** `outputs/decomp/pillar_volume_lit.json` (`leanre.decomp/v1`, `115` nodes, `316` edges, `7` Horn rules, `4` verified claims, `6` `OPAQUE` entries) passes `python3 leanre/leanre.py decompile validate` with `0` errors `[L]`.
