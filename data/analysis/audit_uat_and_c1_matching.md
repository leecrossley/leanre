# Audit of `UAt` (Height Averaging and Hilbert–Samuel) and the c₁-to-log Ω Matching

> **Target:** `UAt` (`atPoint`, `20`-decl core cone), `ArithHilbertSamuel` (`q9`), and `flat_at_of_split_covering` (`c₁`-to-`log Ω` matching) inside `topCovolSlim2_use_alt_alt` (`dom = 80,720`; pinned `40e56bab`)
> **Kernel check:** `3` standard axioms, `0` `sorryAx`, `0` project opaques across all `8` audited cones (`28/28` `PublishedHodgeBundleTheorems` fields projected); see [the analysis index](README.md) for tags.

## 1. Verdicts

1. **`UAt` is an elementary averaging inequality over five per-component inputs `[L]`.** [atPoint](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformLowerBoundOfSums.lean#L39) unpacks `HeightAt`, `HSAt`, `DegAt`, `ShareAt` and `SumAt` and calls [core](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformLowerBoundOfSums.lean#L15), an instance of [CombinedAverageDegreeBound](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/MeanHeightDescent/CombinedAverageDegreeBound.lean#L22). Its cone has only `20` project decls `[K]`. All the strength sits in the inputs (§2).
2. **The earlier note had the two inputs the wrong way round `[K][L]`.** `HSAt` is an arithmetic Hilbert–Samuel-*shaped* **lower** bound on degrees, proved from component numerics. It does **not** use the literature Hilbert–Samuel theorem: field `q9` lies outside its cone. The genuine arithmetic Hilbert–Samuel (`q9 : ArithHilbertSamuel`) has **exactly one reader**, [volume_line_bundle_le](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/VolumeLineBundleLe.lean#L11). That reader feeds `HeightAt` as a counting-volume **upper** bound (§3).
3. **`arith_hilbert_samuel_of_literature` is one of the adapters that ignore `O` `[L][K]`.** It passes `O` only to [principalisation_of_literature](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L253), whose body is `principalisation_closed` (`hygiene`: binder `O` has `0` references). The statement is the standard asymptotic nef form, not a weakened slot. It is proved internally from Hironaka principalisation (§4).
4. **The $c_1$ hypothesis is discharged, and the normalizations agree `[L]`.** $|c_1+\frac{p-q}2\log\Omega|$ is *exactly* $q\,|\log d-\mathrm{lrd}_E|\le3qL$. The $\frac{p-q}2$ vs $pq_j$ "discrepancy" is the factor $2$ in $\mu=2\cdot\mathrm{slope}$, and $pq_j=(k+l-1)-(m-l)=p_l-q_l$ is proved as an identity (§5).

## 2. `UAt` Unpacked `[S][L]`

[UAt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean#L138) is $-C\,E\le\mu_0:=\mu(\mathrm{wtOf}(u_M,0))$, with $E=\mathrm{unitE}=Z.l_{3u}$. `anchorAt_of` rewrites this as $E=f\,m\,b\,L\log\log x$. Fix the component set $\iota=\mathrm{Comp}$ and write:

- $h_Z$ for the height `Y.ht`, $\delta_Z$ for the degree `Y.dg`, and $\deg_Z,\mathrm{rk}_Z$ for `degC`/`rkC` at weight $u_M$;
- $T=\mathrm{lenT}$, $D=\mathrm{dimFlag}$ and $B_n=\mathrm{binT}$.

The five inputs, read at their definitions, are:

| Input | Inequality (for all $Z$) | Supplier `[K]` |
|---|---|---|
| [SumAt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean#L158) | $2\sum_Z\deg_Z/\sum_Z\mathrm{rk}_Z\le\mu_0$ | `sum_component_degrees_div_le_latticeSlope` via [sumC_of_deepGood_alt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SumCOfDeepGood.lean#L10) |
| `DegAt`, `ShareAt` | $\delta'\le\delta_Z\le\frac{\delta'}{1-\rho}$; $B_n\delta_Z\le\mathrm{rk}_Z\le\frac{B_n\delta_Z}{1-z}$ | cover-degree/share packages |
| [HSAt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean#L153) | $B_n\delta_Z\bigl(Th_Z-3(D+1)\lvert h_Z\rvert-A\log(2+\lvert h_Z\rvert)-R\bigr)\le\deg_Z$, with $A\log\max(A,1)+R\le C_2E$ | [hilbertSamuel_of_component_estimates_alt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HilbertSamuelLowerBoundOfComponents.lean#L25) (`dom` `1,606`) |
| [HeightAt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean#L146) | $h_Z+c_s\ge0$; $(1-\rho)\max(0,s_Z+c_s)\le h_Z+c_s+c_c$; $\frac1{\lvert\iota\rvert}\sum_Zs_Z\ge-X$ | [heightAt_eq_of_cover](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/HeightAddLogNonneg.lean#L66) (`dom` `171`) |
| budget | $TX,\ Tc_c,\ c_s(6D+10+T(z+2\rho))\le C_1E$ | same |

`core` instantiates the abstract bound with $R_2=LL_0=U=C_a=C_b=PP_f=0$, $e_1=e_2=C_1E$ and $b=4(3C_1+C_2+4)E$. Its side condition $c_s(\dots)+A\log\max(A,1)+4+R+e_1+e_2\le b/4$ uses $E\ge1$. The output is
$$\mu_0\ \ge\ -2\,(3C_1+C_2+4)\,E\qquad(C_U=2(3C_1+C_2+4)).$$
`[M]` In words: heights are bounded below on average (`HeightAt`). The degree of the $T$-th weight piece is at least $T\cdot$height$\cdot$rank minus lower-order terms (`HSAt`). The slope of the sum dominates twice the average degree ratio (`SumAt`). [lowAt_of_cover](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LowerBoundOfAllEstimates.lean#L65) then adds `FlatAt` to obtain `LowAt` with constant $2(C_F+C_U)+9$. It does this by descent (`DescentFamily.descent`) and `numeric`.

## 3. Where Hilbert–Samuel and the Bergman Kernel Actually Enter `[L][K]`

- **`HSAt` (degree lower bound, no literature Hilbert–Samuel).** The producer takes `twisted_bundle_degree_lower_bound` (`dom` `10`, from `PublishedHodgeBundleTheorems`) and the component data of `exists_degree_parameters_bound_alt_alt`. It closes with [deg_bound_of_claim_numbers](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DegBoundOfClaimNumbers.lean#L9).
  - Its witnesses are $A=26(26D^2+2zT)$, $R=4000b+2C_pz_{\mathrm{base}}^2$ and $C_2=10000+2C_p$.
  - [hilbertSamuel_ALogA_le](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertSamuelALogALe.lean#L5) gives $A\log\max(A,1)\le6000b$.
  - `dom --contains`: `q9` lies **outside** this cone. `ArithHilbertSamuel` appears only as a type mentioned by the hypothesis structure (`shared_in_cone`).
- **`HeightAt` (literature Hilbert–Samuel as a volume upper bound).**
  - Chain: [height_lower_bound_general_alt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HeightLowerBoundGeneral.lean#L21) (`dom` `2,954`) → [height_of_meanAll_bound](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HeightOfSteps.lean#L19) → `heightAt_eq_of_cover` → [slope_le_height](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/HeightAddLogNonneg.lean#L29) → `volume_line_bundle_le`.
  - The last step builds a nef model (`exists_nef_model_of_image`) and applies [countingVolume_le_selfIntersection_nefHermitianBundle](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CountingVolumeLeSelfIntersectionNefHermitianBundStatement.lean#L10) with `hP.q9`. This gives $\mathrm{countVol}\le\frac{A}{d(D+1)}$, hence $\mathrm{vol}_L(t)\le\delta_Z(h_Z+t)$.
  - `slope_le_height` turns this into $(1-\rho)\max(0,s+c_s)\le h+c_s+(c_c+\mathrm{htCost}\cdot l_1)$.
- **Mean slope.** $\frac1{\lvert\iota\rvert}\sum s_Z\ge-C_0\,\mathrm{errX}$ is [MeanAll](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/SemiposAtOfPositive.lean#L101), supplied whole by [DeepStR](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ModelSmall.lean#L63). At the top, `DeepStR` is built by [deep_slim_use](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/HilbertSamuelApplications/AhSlimU.lean#L9) (`dom` `46,110`) from the eight resolution, Moriwaki-bigness, `HSUse` and `NefRR` hypotheses of `topCovolSlim2_use_alt_alt`.
- **Bergman kernel.** It enters `MultAt` (the constant $c_c$) through `exists_section_bounded_by_bergman_kernel_alt` → `carrying_section_integral_frame_alt`. It does not enter `MeanAll` `[L]`.
- **Constants.** $C_1=C_s+C_m+C_b+C_0C_b$ (`heightAt_eq_of_cover`) and $C_2=10000+2C_p$, so $C_U=2(3C_1+C_2+4)$ `[L]`.

## 4. `arith_hilbert_samuel_of_literature` `[S][L][K]`

- **Body.** [arith_hilbert_samuel_of_literature](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L255) (`dom` `2,377`) is `arithHilbertSamuel_of_principalisation (principalisation_of_literature O)`. The latter ignores `O` and returns [principalisation_closed](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/ResolutionCharZero/PrincipalisationClosed.lean#L14).
- **Reduction.** [arithHilbertSamuel_of_principalisation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ArithHilbertSamuelOfPrincipalisation.lean#L11) applies `arithHilbertSamuel_nef_of_ample` to `ArCalc`, `AmpleHS` and `SemiPull`. All three are derived from principalisation. **No `OpenLiteratureStatements` slot is read.**
- **Statement.** [ArithHilbertSamuel](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SmallSecTensTriv.lean#L14) says: for integral $X\to\mathrm{Sp}\,k$ with `IsArithVar p D`, nef hermitian $\overline L$ with self-intersection $a$, and any $\overline N$, the small sections are eventually finite and
$$\log\#\widehat H^0_{\le1}(\overline L^{\otimes m}\otimes\overline N)=\frac{a}{(D+1)!}\,m^{D+1}+o(m^{D+1}).$$
  This is the Gillet–Soulé/Zhang/Moriwaki nef shape `[S]`. It is not a weakened or custom inequality, but `IsNef`, `IsSelfInter` (via the inductive `IsArithHeight`) and `smallSec` are project definitions we did not unfold `[M]`.
- **Cone.** `20,511` project decls; std axioms only; `0` `sorryAx`; `0` opaques. It contains `53` `Published.` decls, which are the `ArCalc` statement defs and their *proved* projections, not hypotheses `[K]`.
- **Placement.** It lies outside the `topCovolSlim2_use_alt_alt` cone. `q9` is a hypothesis field there, filled at top level by `published_results_arithmetic` (`dom` `7,105`) `[K]`. Agrees with [the volume-literature pillar](./pillar_volume_lit.md) (`152` adapters ignore `O`) and [the Hironaka audit](./harish_chandra_and_hironaka_core.md).

## 5. The $c_1$ Hypothesis and the Normalization `[L]`

- **Who discharges it.** [flat_alt_alt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/FlatBoundOfAnchor.lean#L34) feeds [flat_at_of_split_covering](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/FlatAtOfSplitCovering.lean#L28) the five-leg conjunction from [flat_val_alt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/FlatVal.lean#L13). `flat_val_alt` is applied to `FlatDegreeCondition` = [flatDeg_alt_alt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/FlatDegreeStatement.lean#L12) ← [FlatDegreeSt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/HtValOnSubset.lean#L118) ← [flat_tensor_swap_isIso](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/FlatTensorSwapIsIso.lean#L7) (`resK` + GAGA). `chowla_selberg_period` is in that cone at distance `9` `[K]`.
- **Why it holds.** [FlatDegree](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFlatSecRankZero.lean#L754) pins every flat section's degree. So [c1](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFlatSecRankZero.lean#L744) $=-$[flatDegVal](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFlatSecRankZero.lean#L751), and
$$c_1(\tau)+\tfrac{p-q}2\log\Omega=-q\,(\log d-\mathrm{lrd}_E),\qquad |\log d-\mathrm{lrd}_E|\le3L\ \ (\mathrm{lrd}_E=\tfrac{\log|d_E|}{2f}),$$
  by [abs_log_sub_lrd_le](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatLineC1LogBound.lean#L30). The hypothesis is a theorem, tight up to the discriminant term.
- **$\log\Omega$ identification.** [flatDegAt_of_st](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatDegreeStatement.lean#L15) rewrites with [logPeriod_eq_kroneckerCharacter_logPeriod_of_host](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogPeriodEqKroneckerCharacterLogPeriodOfHostStatement.lean#L9): $\operatorname{Re}\mathrm{CM.logOm}(E,\chi)=\mathrm{ofRecord}.\log\Omega=L.\log\Omega$ for a Kronecker $\chi$. This closes the earlier open item "$rd=\mathrm{rd}_E$, $\chi_K=\chi$" at the statement level `[S]`.
- **Normalization.** [AnchorAt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean#L98) asks $|\mathrm{mainT}-\sum_\tau(p-q)\,w_\tau\log\Omega|\le C\,E$. [anchorAt_of](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AnchorBoundStatement.lean#L77) proves it with $C=100$ in three steps.
  - `hc_eq` is the identity $(k+l-1)-(m-l)=p_l-q_l$ for $l=i+1$.
  - `hmainS` gives $\mathrm{mainT}=\sum_t(p-q)\,e_t(i)\log\Omega$.
  - The anchor weights $w_\tau$ differ from $e_t(i)$ by at most $f\cdot20b\cdot3L\le100E$.

  [twice_twist_ge](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatBoundOfAnchor.lean#L76) then gives
$$-\mathrm{mainT}-(11C_A+83)E\ \le\ 2\Bigl(\sum_\tau w_\tau c_1(\tau)-q\,\mathrm{lrd}\sum_\tau|w_\tau|-\dots\Bigr),$$
  because $2\cdot\frac{p-q}2=p-q$. **So $pq_j=p-q$ exactly, and the $\frac12$ is absorbed by $\mu=2\cdot\deg/\mathrm{rk}$.** There is no discrepancy. $C_F=11\cdot100+83=1183$ `[L][M]`.
- **Bonus: `MultEq`.** [MultEq](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinRepApply.lean#L118) (equal cuspidal multiplicities across a finite isomorphism) has `9` producers. The top one is [twisted_multiplicity_eq](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedMultiplicityOne.lean#L15) (`dom` `5,814`), proved under `Published.` Harish-Chandra/discrete-series inputs. [lu_of_multiplicity_equal](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/HoldsOfMultiplicityEqual.lean#L65) consumes it as a guarded premise `[K]`. Which producer is live on the Stage-U edge was not traced.

## 6. Hygiene and Cone Sweep `[K]`

| Target | `dom` | Project decls in cone | `Published.` decls |
|---|---:|---:|---:|
| `atPoint` | `24` | `12,750` | `0` |
| `mean_height_sum_bound_holds` | `13` | `20` | `0` |
| `hilbertSamuel_of_component_estimates_alt` | `1,606` | `124,393` | `203` |
| `heightAt_eq_of_cover` | `171` | `20,571` | `122` |
| `arith_hilbert_samuel_of_literature` | `2,377` | `20,511` | `53` |
| `flat_val_alt` / `anchorAt_of` | `7` / `36` | `44,290` / `6,615` | `1` / `0` |
| `flat_at_of_split_covering` | `10` | `72,532` | `126` |

- **`cone-audit`** (8 targets, `17.85s`): only the three standard axioms; `0` `sorryAx`; `0` project opaques. The `6` project `decide_kernel` hits are the $E_4$/$E_6$ $q$-expansions already seen under Chowla–Selberg.
- **`hygiene --semantic`** (11 decls, `0.32s`, 7 findings):
  - `O` unused in `principalisation_of_literature`: a true positive that confirms §4.
  - A `le_refl_closure` flag in `flat_val_alt`: a false positive. It is the witness $0\le0$ for the constant.
  - Benign: the constants discarded by `obtain` in the Hilbert–Samuel producer, and four `fun _` binders.
- **`kernel stats --with-alias`** resolves `uniform_lower_bound_of_sums'`, `coverHeightSum_…`, `flat_of_prints_…`, `anchor_bound`, `abs_flat_c1_…`, `flatDeg_of_scholzeWeinstein_of_prints` and `sum_c_of_deep_good` to the `_alt` bodies above.
- **`bundles`**: `PublishedHodgeBundleTheorems` has `28/28` fields projected.

## 7. Verification Limits

- **Read `[L]`:**
  - in full: `atPoint`, `core`, `lowAt_of_cover`, `heightAt_eq_of_cover`, `slope_le_height`, `volume_line_bundle_le`, `height_of_meanAll_bound`, `hilbertSamuel_of_component_estimates_alt`, `flat_at_of_split_covering`, `twice_twist_ge`, `flat_val_alt` and `flatDegAt_of_st`;
  - most of the `anchorAt_of` body (lines 1–133, with gaps);
  - the adapter chain of §4.
- **`UNREAD`:**
  - the bodies of `mean_height_sum_bound_holds`, `deg_bound_of_claim_numbers`, `twisted_bundle_degree_lower_bound`, `exists_degree_parameters_bound_alt_alt`, `sum_component_degrees_div_le_latticeSlope` and `exists_nef_model_of_image`;
  - the Bergman-kernel lemma;
  - `deep_slim_use` (the source of `MeanAll`);
  - `arithHilbertSamuel_of_ampleHS` beyond its first line;
  - the proof of `logPeriod_eq_…`;
  - the `resK`/GAGA route to `FlatDegreeSt`.
- **Not checked:**
  - the joint satisfiability of the size hypotheses ($T\cdot PP\le\sqrt b$, $z\le\frac12$) at the live parameters;
  - that `IsNef`/`IsSelfInter`/`smallSec` match the standard Arakelov notions;
  - which `MultEq` producer is live.
- **Interpretive `[M]`:** reading `HSAt` as a "Hilbert–Samuel-shaped" bound and `SumAt` as slope-dominates-average.
- **`OPAQUE`:** the eight top-level hypotheses of `topCovolSlim2_use_alt_alt`, discharged in the literature layer ([VWin audit](./audit_vwin_shafarevich.md)).
