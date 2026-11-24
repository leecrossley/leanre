# Audit of `deep_slim_use` (Pillar D) and the `MeanAll` Lower Bound

> **Target:** `deep_slim_use` (`dom = 46,110`) → `deepStR_of_use` (`45,411`) → `DeepStR` / `MeanAll` (follows [the `UAt` audit](./audit_uat_and_c1_matching.md) §3 & §7; pinned `40e56bab`, `dom_tree = ALL`)
> **Kernel check:** `3` standard axioms, `0` `sorryAx`, `0` project opaques, `0` semantic hygiene findings; see [the analysis index](README.md) for tags.

## 1. Verdicts

1. **`deep_slim_use` is a one-line plug; `98.5%` of its subtree sits under `deepStR_of_use`, and `69%` is the tower volume theorem `[K][L]`.** [deep_slim_use](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/HilbertSamuelApplications/AhSlimU.lean#L9) calls [deepStR_of_use](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/HilbertSamuelApplications/DeepStROfUse.lean#L12) (`45,411`). Of that, `31,846` is the `GoodTowerExistsX ∧ VolumeTheoremX` producer. Only `2,012` is the `MeanAll` packaging (§2).
2. **`MeanAll` gets its strength from one arithmetic-degree lower bound, `T2` `[L][S]`.** The tower lower bound $\widehat{\deg}(\mathcal L_u^{\,d+1})\ge-C\,(d+1)\,\mathrm{vol}_T\,\deg(u)\,[\Lambda_B\ell_1(u)+q\,\mathrm{spr}(u)]$ is turned into a mean-slope bound by pure algebra. This uses equal component volumes (`VolEq`) and costs no constant. A second elementary step then gives `MeanAll` with $C=C_T+120$ (§3).
3. **`T2` rests on Zhang's successive-minima lower bound and three cusp estimates `[L][K]`.** `ZhangLowerX` comes from `HSUse.1` (arithmetic Kleiman) via `hsLinks_of_use`. `NineGeoU` (cusp heights $\ge-C_h\cdot$, cusp mean $\le C_u\cdot$, positivity) comes from `Top.Given`. They combine in `SlopeLower` with constant $C_h+C_u/2$. The tower Theorem B (averaged), `PropF` and the flag test-height bound then lift this to `T2` with $2C+3C'+5$ (§4).
4. **The Bergman kernel is outside the whole cone `[K]`.** `exists_section_bounded_by_bergman_kernel_alt` (`417`) and `carrying_section_integral_frame_alt` (`15`) have `cone_in = no` under `deep_slim_use`. Both are dominated by `height_lower_bound_general_alt`, so they enter `MultAt` only, as the earlier note said.
5. **No hypothesis is weakened or bypassed `[L][K]`.** All `8` binders are consumed. `cone-audit`: `3` standard axioms, `0` `sorryAx`, `0` project opaques. `hygiene --semantic`: `0` findings on `11` spine decls. There is one benign literal `True` conjunct (§5).

## 2. Sub-engine Breakdown (`dom ≥ 1,500`, plus key pieces) `[K]`

| Sub-engine (alias target where different) | `dom` | Role `[L]` |
|---|---:|---|
| `deepStR_of_use` | `45,411` | Builds `Given`, the tower pair and `HS`; projects the pullback–pushforward formula |
| `good_tower_volume_theorem_bis` → `goodTower_volume_of_reduced` | `31,846` / `31,841` | Rebuilds `Given`, adds `FamilyExistsPos` and the comparison pair |
| [goodTower_and_volume](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/GoodTowerVolumeTheorem.lean#L36) | `27,141` | Root-tower existence plus `VolumeTheoremX` |
| [volumeTheoremX_of_inputs](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/VolumeTheoremOfInputs.lean#L72) | `13,622` | Assembles `I1`–`I8`, `PropA/F`, `SlopeLower`, then calls `chain_tower` |
| `model_on_hodge_from_family` → `arithmetic_relations_statement_holds` | `3,787` / `3,388` | Hodge-lattice flag bound (`M3`) |
| `full_intersection_tower_I8_identity` | `2,644` | Tower intersection identity `I8` |
| `family_pos_of_hodge_tate_inputs` → `ordinary_curve_hodge_prime` | `2,442` / `1,563` | Ordinary CM test curve (`FamilyExistsPos`) |
| [chain_tower](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/TowerWeilInputsCombined.lean#L22) (`tower_weil_inputs_combined`) | `2,116` | `T1`, Theorem B, `T2`, `MeanSlope`; contains `test_height_bound` (`1,411`) and `tower_T2` (`228`) |
| `flag_cover_realisation_pullback` | `2,053` | Flag-cover pullback realization |
| [deepStR_of_volume](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/GeometryProofs/DeepStROfVolume.lean#L21) → [top_meanAll](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/GeometryProofs/AbelianCmCompLawsBound.lean#L54) | `2,012` / `1,826` | `MeanSlope` → `MeanAll`; contains `uniform_all_norm_height_bound` (`1,721`) |
| `final_theorem_of_inputs_left` (`given_of_inputs`) | `1,707` | Packs the 14-leg `Top.Given` |
| `lineOfLargeDegree_of_use` | `1,617` | Line-of-large-degree statement from `HSUse`/Moriwaki |
| `given_of_use`, `good_tower_I5`, `exists_geometric_height_constants` | `1,122` / `1,105` / `1,030` | `Given` adapter; `I5`/`I6`; `NineGeoU` |

The residual is `698` decls directly under `deep_slim_use` (`ais`, `resK`, …) and about `8,700` sub-`400` children of `goodTower_and_volume` `[K]`.

## 3. Statement and `MeanAll` Unpacked `[S][L]`

- **Statement `[S]`.** `deep_slim_use` takes `ResolutionCharZero`, `PrincipalisationCharZero`, `PoincareLelongInv`, `HSUse`, `MoriwakiBigStatement`, `FarguesExact`, `ZarhinStatement` and `NefRR`, and concludes [DeepStR](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ModelSmall.lean#L63).
- **`DeepStR` `[S]`.** There is one $C\ge0$ such that for every `D7` datum with $m^2\le k$, every $1\le j<m$ and every good deep cover `Y` with $\#\{p\mid M'\}\le15$, `MeanAll Y.U (xiR D) (ell D) C` holds.
- **`MeanAll` `[S]`.** [MeanAll](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/SemiposAtOfPositive.lean#L101) and [MeanGe](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/SemiposAtOfPositive.lean#L97) say: for every strictly anti weight $u$ with gap $g>0$ there are $s_Z\le\mathrm{compVolSlope}_Z(u)$ (in `EReal`) with
$$\frac1{|\iota|}\sum_{Z\in\iota}s_Z\ \ge\ -C\,\mathrm{errX},\qquad \mathrm{errX}=(\log B_{u,g}+s)\,\ell_1(u)+q\sum_\tau\big(\max_i u_{\tau i}-\min_i u_{\tau i}\big),$$
where $B_{u,g}=4|\Psi|(p+q)^2\big(1+\|u\|_\infty/g\big)$ ([errX](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/SemiposAtOfPositive.lean#L94)).
- **`top_meanAll` `[L]`.** The proof:
  - takes $(Y,T,o,\kappa)$ and `MeanSlope` with constant $C_T$ from `full_intersection_good_level` (that is, from `VolumeTheoremX`);
  - sets $s_Z:=\mathrm{slope}_T(\kappa Z,u)-2\,\mathrm{cost}_2\,\ell_1(u)$, where `uniform_all_norm_height_bound` (the `NefRR` consumer) gives $s_Z\le\mathrm{compVolSlope}_Z$;
  - uses `cost_two_log_bound` for $0\le\mathrm{cost}_2\le60(\log B+\log\mathrm{rd})$;
  - ends with `nlinarith` after `errX_eq`. The result is
$$\frac1{|\iota|}\sum_Z s_Z\ \ge\ -C_T\big(\Lambda_B\ell_1+q\,\mathrm{spr}\big)-120(\log B+\log\mathrm{rd})\ell_1\ \ge\ -(C_T+120)\,\mathrm{errX},\qquad \Lambda_B=\log(B\,\mathrm{rd})+|L_{\mathrm{val}}|.$$
- **`MeanSlope` from `T2` `[L]`.** [mean_slope_of_proportional_volume](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/FlagImmersions/MeanSlopeOfProportionalVolume.lean#L13) (`dom` `3`) uses `VolEq` to get $\mathrm{vol}_T=|\mathrm{Comp}|\,\mathrm{vol}(c_0)$. Hence $\frac1{|\mathrm{Comp}|}\sum_c\mathrm{slope}_c=\mathrm{PB}/((d+1)\mathrm{vol}_T\deg u)$, and [T2](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Definitions/DivisibilityTowers/HeckeSectionsIsotropicCommutatorPairingPower.lean#L87) gives [MeanSlope](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Definitions/DivisibilityTowers/HeckeSectionsIsotropicCommutatorPairingPower.lean#L91) with the **same** $C$ (`linarith`).
- `[M]` So `MeanAll` is exactly as strong as `T2`, the lower bound on the arithmetic self-intersection $\mathrm{PB}=\sum_c\widehat{\deg}_c(\mathcal L_u^{\,d+1})$. The averaging steps add only $+120$ and the log-cost.

## 4. Where `T2` Comes From `[L][S][K]`

1. **Zhang `[S][L]`.** [ZhangLowerX](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsZhangLowerX.lean#L11) is the easy half of Zhang's successive-minima theorem. If every arithmetic point $W\supseteq P$ has $h_{\bar A}(W)\ge e$, with $\bar A$ semipositive, nef on fibres and conjugation-invariant, then $(n+1)\,e\,\deg_P(A)\le\widehat{\deg}(\bar A^{\,n+1}\mid P)$.
   - [hsLinks_of_use](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/HilbertSamuelApplications/HsLinksOfUse.lean#L9) proves it from `SuccessiveMinimaLowerBound := hU.z1`.
   - `readers --conjunct`: `hU.z1` is the only reader of `HSUse.1` (`ArithKleiman`).
   - Moriwaki bigness supplies `SuccessiveMinimaUpperBound` and `ArithmeticVolumeLowerBound` in the same tuple.
2. **Cusp constants `[S][L]`.** [NineGeoU](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Statements/GeometryStatements/NineGeoU.lean#L59) $(C_h,C_u)$ bundles three estimates:
   - `HtU`: $h\ge-C_hfj'\Lambda_2-\frac pqK_A$ on arithmetic points;
   - `MeanU`: the cusp-weight mean is $\le C_ufj'\Lambda_2$;
   - `PosU`: positivity.

   [nineGeoU_of_given](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ExistsGeometricHeightConstants.lean#L17) takes them from `cusp_height_upper` (`782`), `cusp_volume_sum` (`26`) and `intersection_degree_lower` (`220`). All three use only `Given` (+ `FlatDegree`, `WeilSt`).
3. **`SlopeLower` `[S]`.** `slope_lower_base_settings` feeds Zhang and [HasBaseDegreeSettingStrict](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/HasBaseDegreeSettingStrict.lean#L16) into [SlopeLower](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Definitions/DivisibilityTowers/HeckeSectionsIsotropicCommutatorPairingPower.lean#L67) at $C=C_h+C_u/2$:
   $$-C\,|\Psi|\min(j,N-j)\,\Lambda_B\,(\dim X+1)\,\mathrm{vol}_T\,\deg_{\mathrm{test}}\ \le\ \mathrm{PP}_T(\mathrm{testPoly}_j).$$
   `HasBaseDegreeSettingStrict` comes per component from `base_setting_of_good_tower` (`594`), which consumes `NineGeoU`.
4. **Lift to `T2` `[L]`.** `chain_tower` combines three inputs:
   - [test_height_bound_slope_flat](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/TestHeightBound.lean#L32) (`SlopeLower` + `PropF` + `I9` + the flag test bound) gives `LowerBoundAtBase` with $K=2(C+C')+3$;
   - [tower_T2_of_inputs](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/TowerT2.lean#L69) adds the averaged Theorem B (`ThmBA`) and `Prop6`, giving `T2` with $K+C'+2=2C+3C'+5$;
   - `mean_slope_proportional_volume` closes `MeanSlope`.

   `volumeTheoremX_of_inputs` calls it with $C=\max(C_h+C_u/2,0)$ and $C'=4$. So the `VolumeTheoremX` constant is $2\max(C_h+C_u/2,0)+17$. `full_intersection_good_level` re-exports a $C_T$ `[S]`, and the final `MeanAll` constant is $C_T+120$.

## 5. Hypothesis Consumption and Hygiene `[L][K]`

- **All `8` binders are live `[L]`.**
  - $h_1,h_2$ feed `resK` and `ais`; `ais` also takes `hPL` through Poincaré–Lelong.
  - `hU` and `hBig` feed `hsLinks_of_use`, `lineOfLargeDegree_of_use`, `given_of_use` and `nineFree_of_use`.
  - `hF` feeds `hodge_tate_of_fargues_exact`, `hZ` feeds `family_pos_of_hodge_tate_inputs`, and `hN` (`NefRR`) feeds `uniform_all_norm_height_bound`.
  - Three slots are closed internally: `semiAbelianHomExtension`, `gagaSections` and `quot`.
- **Discards are rebuilt, not dropped `[L]`.**
  - `good_tower_volume_theorem_bis` discards `SA`, `SlopeBoundSt` and `AntisymPerturbation` from `Given` (`_`-binders).
  - `goodTower_volume_of_reduced` then reconstructs `Given` from `final_theorem_of_inputs_left`, so `Given` is built `3` times on this spine.
  - The `14`-leg `Given` destructuring in `volumeTheoremX_of_inputs` keeps `Inputs`, `HS`, the Zhang bundle and `AntisymPerturbation`.
- **One literal `True` conjunct `[L]`.**
  - The third leg of [ZhangDimensionPushDownGrassmannianHeightBounds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Statements/GeometryStatements/ZhangDimensionPushDownGrassmannianHeightBounds.lean#L32) is `True`, filled by `trivial` in [nineFree_of_use](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/HilbertSamuelApplications/NineFreeOfUse.lean#L10).
  - Its only consumer discards it (`⟨hZh, -, -, -, hGr⟩`). It is a benign placeholder, not a weakened hypothesis.
- **`cone-audit deep_slim_use` (`12.1s`) `[K]`.**
  - Cone: `301,836` total, `136,246` project.
  - Axioms: `[Classical.choice, Quot.sound, propext]`; `sorryAx`/`ofReduceBool`/`trustCompiler` = `0`; project opaques `0`.
  - `decide_kernel`: `6` project hits, all the $E_4$/$E_6$ $q$-expansion lemmas already seen under Chowla–Selberg.
- **`hygiene --semantic` (`11` decls, `0.24s`) `[K]`.**
  - `0` findings (`10` noisy findings suppressed).
  - Tuple legs are fully read: `chain_tower` reads `4/4` and `good_tower_volume_theorem_bis` reads `2/2`.

## 6. Verification Limits

- **Read `[L]`:**
  - in full: `deep_slim_use`, `deepStR_of_use`, `good_tower_volume_theorem_bis`, `goodTower_volume_of_reduced`, `goodTower_and_volume`, `nineGeoU_of_given`, `hsLinks_of_use`, `nineFree_of_use` and `mean_slope_of_proportional_volume`;
  - most of `top_meanAll`, `deepStR_of_volume`, `volumeTheoremX_of_inputs` and `chain_tower` (gaps in the middle).
- **`UNREAD`:**
  - the bodies of `htU_of_given`, `top_mean_cusp_weight`, `intersection_degree_lower`, `test_height_bound_slope_flat`, `tower_T2_of_inputs`, `uniform_all_norm_height_bound`, `base_setting_of_good_origin` and `errX_eq`;
  - the `I8` identity, `model_on_hodge`, the ordinary-curve family and `lineOfLargeDegree_of_use` beyond line `20`.
- **Not checked:**
  - that `compVolSlope`, `PPc` and `IntersectionSystem` match the standard Arakelov degree;
  - that the `DeepStR` side conditions ($m^2\le k$, $\le15$ primes) hold at the consumer;
  - the exact identification of $s$ = `ell D` inside `errX_eq`.
- **Interpretive `[M]`:** reading `ZhangLowerX` as "the easy half of Zhang" and `T2` as the decisive inequality.
- **`OPAQUE`:** the eight top-level hypotheses, discharged in the literature layer ([VWin audit](./audit_vwin_shafarevich.md)). *(Methodological note: `_`-prefixed `obtain` discards and `trivial`-filled `True` conjuncts of `∧`-bundles in §5 were verified manually in addition to automated hygiene scans.)*
