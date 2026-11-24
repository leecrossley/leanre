# Dead code, lean4lean timeouts, and kernel-time computation

Every `.lean` file in the repository (`175,187 / 175,187`, `17,374,215` physical lines) is transitively imported by [the entry module](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L1), yet `28,904` files (`2,378,537` lines, `16.50%`) contribute zero declarations to `solution.ndjson.zst`. Almost all of them (`28,471` files, `2.36M` lines) are unused code—including four of the five files that timed out in `lean4lean`.

## Disjoint accounting of all 28,904 zero-kernel files

| Category | Modules | Lines (`wc -l`) | Explanation |
|---|---:|---:|---|
| Import-unreachable from `Main` | `0` | `0` | Full BFS reaches `175,187 / 175,187` modules |
| Alignment gaps (unmapped source modules) | `19` | `1,631` | `3` scanner misses, `5` anonymous instances, `11` shadowed duplicates |
| Pure import / re-export shims | `164` | `959` | Only `import`/`open`/`namespace` lines |
| Meta / elab / attribute-only | `11` | `248` | `BuildAid.D1..D5`, `kexactB`, `kcopy`, `CutCptCopy`, `3` local-instance files |
| Unused private / struct / abbrev / instance | `239` | `16,838` | Lean exports `_private` (`112,310` live) and `inst*` (`34,123` live) when used |
| **Imported but unused by kernel** | **`28,471`** | **`2,358,861`** | `19,363` in `Development.AbelianVarietyTheory`, `7,336` signature clones, `5,676` wrappers |

## Dead DyadicPrimeIntervals vs. live SmallLoop

All six files under `DyadicPrimeIntervals` contribute `0` declarations to the kernel export. The dead import chain terminates at two files that mix live data definitions with dead theorems:

- [`run1`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run1.lean#L6)..[`run4`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run4.lean#L6) (`0` decls) → [`small_natural_numbers_bound`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/SmallNaturalNumbersBound.lean#L153) (`0`) → [`primes_dyadic_range`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PrimesDyadicRS.lean#L7) (`0`) → [`counts_closed`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/ExplicitFormulaCounts/SqfCounts.lean#L43) (`0`).
- `SqfCounts` is imported by `CylinderCountFamily`, which calls `counts_closed` only inside the dead theorem [`family_bound_all`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/LevelLetterCocycles/CylinderCountFamily.lean#L324) (and `JCount`'s dead [`family_count_all`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/LevelLetterCocycles/JointConditionsZpowers/JCount.lean#L204)), while `Main` pulls both files in solely for their live structures [`AllRowsAt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/LevelLetterCocycles/CylinderCountFamily.lean#L11) and [`CountCylAt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/LevelLetterCocycles/JointConditionsZpowers/JCount.lean#L11).
- By contrast, the fifth `lean4lean`-timeout file, `ChebyshevPrimeBounds.SmallLoop`, is `9 / 9` live:

```lean
theorem loop_run : loop 362 131070 2 0 1 = true := by decide +kernel
```

[`loop_run`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/SmallLoop.lean#L24) runs a `131,070`-step Chebyshev sieve (`B = 362`) inside the kernel (`35.1s` in `con-leche`) and sits `21` hops from `riemannHypothesis`.

## The 14 live decide +kernel files

Across all `175,187` files, `native_decide` and `decide_cbv` never appear (`0` hits) and `decide +kernel` appears `151` times across `124` lines in `34` files. Twenty files (`93` lines / `120` occurrences) emit zero live reductions (`7` completely dead files including `Run1..4`, plus `13` live files whose calls sit only in `4` unexported `example`s and `9` unused witnesses such as [`witness_thirteen`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L293)), while exactly **`14` files (`31` lines/occurrences)** export **`18` live enclosing declarations** plus **`35` `._proof_1_*` kernel-reduction auxiliaries**, and **`0` feed Pillar B** (see [the live `decide +kernel` audit](../analysis/decide_kernel_live14.md)).

| Live enclosing declaration(s) (14 files, 18 decls) | Hits | Computation checked in the kernel |
|---|---:|---|
| [`loop_run`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/SmallLoop.lean#L24) | `1` | `131,070`-step Chebyshev sieve (`B = 362`; `lean4lean` timeout) |
| [`table_ok`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L301) | `1` | `12`-interval rational sum of $1/p$ on `[100, 16900)` vs $1/(5\log N)$ |
| [`factorial_ladder_thirteen`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L117), [`factorial_ladder_thirty_one`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L118), [`factorial_ladder_one_forty_one`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L119) | `3` | Factorial valuation ladders (`13!`, `31!`, `141!`) on `[100, 20000)` |
| [`lcmUpto_le_four_pow_small`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SumVonMangoldtLeTwoMul.lean#L11) | `1` | `Nat.lcmUpto n ≤ 4^n` for `n ≤ 100` |
| [`lcmUpto_le_three_pow`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiUpperBoundOfLtThirtyMulSixPow.lean#L27) | `1` | `Nat.lcmUpto n ≤ 3^n` for `n < 30` |
| [`sep_numerical_ineq`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SeparationNumericalIneqCuspidalGL.lean#L68) | `9` | Explicit `Nat.primeFactors n` for `n = 2..10` |
| [`discr_of_cyclic`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeInvariantsPeriodPairDictionary.lean#L131), [`qExpansion_E₄`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsPolynomialModularJOfHasQExpansion.lean#L62), [`qExpansion_E₆`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsPolynomialModularJOfHasQExpansion.lean#L71), [`g₃_eq_E₆`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsVariableChangeEqLatticeCurve.lean#L103), [`riemannZeta_six`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/GlobalFields/ComplexMultiplication/JInvariant.lean#L45), [`qExpansion_E₄_eq`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/ReciprocityTheory/DualLattices/Eisenstein4CoeffBound.lean#L12), [`qExpansion_E₆_eq`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/ReciprocityTheory/DualLattices/Eisenstein4CoeffBound.lean#L19) | `7` | Bernoulli evaluations $B_4 = -1/30$ and $B_6 = 1/42$ (`5` files) |
| [`db_counts`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/FrobeniusSmoothVectors/EpDimb.lean#L74) | `1` | Exhaustive check over the `8` maps `Fin 3 → ZMod 2` |
| [`redM_key`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/CompactIntegralFields/RedList.lean#L9), [`redT_ex`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/CompactIntegralFields/RedList.lean#L15) | `2` | `256`-state `4×4` Boolean transitive-closure SAT vs `9` `redTypes` blocks |
| [`BB_disj0`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L554) | `5` | Disjointness of `BB 9 413718278401` and `BB 9 603339156001` (pulled via toy `D7`) |

## Macro-generated proof terms

The two largest proof terms in the entire kernel export are not computational searches—they come from the destructuring macro [`copy_cases`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingSpecNormalisedCharacterEq.lean#L75), which inflates [`lam_copy`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamCopy.lean#L15) to `5,538,373` compiled proof-term DAG nodes (`value_nodes`, `#1`) and [`sigSpan_copy`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingSpecNormalisedCharacterEq.lean#L97) to `4,598,428` (`#2`).

<details>
<summary>Verify locally</summary>

```bash
python3 -c "
import json, sqlite3
k = sqlite3.connect('file:outputs/kernel/kernel.db?mode=ro', uri=True)
print('dyadic+smallloop:', k.execute(\"SELECT name, live_mask, value_nodes FROM decls WHERE name LIKE 'PI.PrimesDyadicRS.%' OR name IN ('PI.PC.loop_run','PI.PC.loop_run._proof_1_1','GlobalTheory.PrimeRecip.table_ok')\").fetchall())
print('loop_run depth from RH:', k.execute(\"SELECT r.depth FROM reach r JOIN decls d ON d.id=r.decl_id WHERE d.name='PI.PC.loop_run' AND r.root_id=0\").fetchone()[0])
print('top value_nodes:', k.execute('SELECT name, value_nodes FROM decls WHERE live_mask>0 ORDER BY value_nodes DESC LIMIT 5').fetchall())
d = json.load(open('outputs/decomp/compute_atlas.json'))
print('zero buckets:', {b: v['modules'] for b, v in d['zero_kernel_classification']['buckets'].items()})
"
```

</details>
