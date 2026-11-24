# Kernel-Time Computation and Zero-Declaration Files

> **Target:** All `175,187` `.lean` files (`17,374,215` lines, pinned `40e56bab`, `solution.ndjson.zst` `5ea74b91…244e`) · **Data:** `outputs/decomp/compute_atlas.json` (`leanre.compute_atlas/1` via `leanre/compute_sweep.py`)
> **Kernel check:** `LIVE` denotes presence in `solution.ndjson.zst` (`live_mask = 31` across all 5 roots); statement fidelity is audited in [tcb_and_contracts.md](tcb_and_contracts.md). See [the analysis index](README.md) for tags.

---

## Executive Summary `[L]`

1. **All `28,904` Zero-Kernel `.lean` Modules (`2,378,537` `wc -l` lines) Are Disjointly Accounted For `[L]`:**  
   `146,283 / 175,187` modules (`14,995,678` lines) map to `>= 1` kernel declaration in `outputs/kernel/kernel.db`, leaving **`28,904` modules (`2,378,537` lines)** with zero `decl_module` rows. Every one of those `28,904` modules is transitively imported by `Main` (`module_import_unreachable = 0` `[L]`). Only **`19` (`1,631` lines)** are `alignment_gap` mapping misses; **`164` (`959` lines)** are pure import/re-export shims; **`11` (`248` lines)** are pure erased `run_cmd`/`elab`/`attribute` modules; **`239` (`16,838` lines)** declare only unused `private`/`structure`/`abbrev`/`instance` items (despite empirical kernel evidence that Lean 4 *does* export `private` and `instance` declarations when referenced); and **`28,471` (`2,358,861` lines, `98.50%`)** declare normal theorems/defs inside `Main`'s import closure whose declarations are **never referenced anywhere in the 5 root proofs**.
2. **`DyadicPrimeIntervals.Run1..4` Are 100% Dead While `ChebyshevPrimeBounds.SmallLoop` Is 100% Live `[L]`:**  
   All `6` files under `DyadicPrimeIntervals` (`SmallLoop`, `Run1..4`, `SmallNaturalNumbersBound`) plus `OrbitalBoundsConclusion.PrimesDyadicRS` and `SqfCounts` have **`0` declarations in `solution.ndjson.zst`**. `Main` imports them transitively solely because `CylinderCountFamily` and `JCount` also define live data types alongside dead theorems (`family_bound_all`, `family_count_all`). By contrast, `ChebyshevPrimeBounds.SmallLoop` contributes all **`9/9`** kernel decls (`live_mask = 31`), including `PI.PC.loop_run` and its `._proof_1_1` reduction auxiliary at min `20`/`21` hops from the roots.
3. **`decide +kernel` & Kernel-Time Computation Scope `[L]`:**  
   Across `175,187` files, `native_decide` and `F_REDUCE_BOOL`/`F_REDUCE_NAT`/`F_SORRY`/`F_TRUST_COMPILER` are all **`0`**. `decide +kernel` appears **`151` times across `124` comment-stripped lines in `34` files**, splitting 3 ways at the declaration level: only **`14` files (`31` lines/occurrences)** put `decide +kernel` declarations into `solution.ndjson.zst`; **`13` files (`45` lines, `52` occurrences)** are *live modules* whose `decide +kernel` witness/sanity declarations (`example`, `witness_thirteen`, `toyPrimes`, `grid4`) are absent from `kernel.db`; and **`7` files (`48` lines, `68` occurrences)** are in completely dead modules (`Run1..4`, `FoundationsPrimeFact`, `CyclotomicIsCyclotomicExtension`, `DeltaQExpansionIntegral`). Meanwhile, `129,492` live `F_REFL_TRUE` decls are dominated by `rfl` and `norm_num` (`9,608` files / `24,581` hits, whose largest blocks are algebraic real-inequality chains rather than brute-force tables), alongside `472` `F_OF_DECIDE` decls (`decide` in `2,011` live files). Finally, the two largest kernel proof terms (`lam_copy` `5,538,373` `value_nodes`; `sigSpan_copy` `4,598,428`) are emitted by the `copy_cases` destructuring macro, while `cpt_copy_thms` synthesizes `5` live theorems in `CutMainCpt`.

---

## 1. Corpus Totals & `Main` Import Reachability `[L]`

| Metric | Modules | `% of Corpus` | Physical Lines (`wc -l`) | Local Source `[L]` |
|---|---:|---:|---:|---|
| Total `.lean` source modules | `175,187` | `100.00%` | `17,374,215` | `leanre.db` + `data/rh_mirror/src` |
| Reachable from `Main` (`module_edges` BFS) | `175,187` | `100.00%` | `17,374,215` | `leanre.db` BFS |
| Unreachable from `Main` | `0` | `0.00%` | `0` | `leanre.db` BFS |
| Matched `>= 1` decl in `kernel.db` (`decl_module`) | `146,283` | `83.50%` | `14,995,678` | `outputs/kernel/kernel.db` |
| Zero matched decls in `kernel.db` | `28,904` | `16.50%` | `2,378,537` | `kernel.db` / `compute_sweep.py` |

---

## 2. Disjoint Classification of All `28,904` Zero-Kernel Modules `[L]`

Precedence is strict and pairwise disjoint (`sum = 28,904` modules, `2,378,537` lines): (1) unreachable from `Main`, (2) matched in `kernel.db` via `alignment_gap`, (3) zero decls and zero meta commands, (4) meta/attribute commands only with zero non-meta decls, (5) only `private`/`@[inline]`/`instance`/`abbrev`/`structure`/`class` decls, (6) remainder (`imported_but_unused_by_kernel`).

| Bucket | Modules | `% Zero` | `% Corpus` | Lines (`wc -l`) | Bytes | Top L2 Folders (`modules`) |
|---|---:|---:|---:|---:|---:|---|
| `module_import_unreachable` | `0` | `0.00%` | `0.00%` | `0` | `0` | — |
| `alignment_gap` | `19` | `0.07%` | `0.01%` | `1,631` | `83,079` | `Development.AutomorphicArithmetic` (`3`), `Development.WeilBound` (`3`), `Formalism.PeriodIntegrals` (`2`), `Lemmata` (`4` L1) |
| `import_shim_reexport` | `164` | `0.57%` | `0.09%` | `959` | `73,301` | `CompanionTheory.AutomorphicTheory` (`35`), `CompanionTheory.SpectralGeometry` (`27`), `Development.WeilBound` (`25`), `Formalism.SharpRestriction` (`13`) |
| `macro_tactic_elab_syntax_only` | `11` | `0.04%` | `0.01%` | `248` | `11,294` | `BuildAid.D1..D5` (`5`), `Development.AutomorphicArithmetic` (`2`), `Formalism.LocalToGlobal` (`2`) |
| `unexported_private_or_inline` | `239` | `0.83%` | `0.14%` | `16,838` | `1,052,273` | `Development.AutomorphicArithmetic` (`162`), `Development.AbelianVarietyTheory` (`31`), `Formalism.LocalToGlobal` (`18`) |
| `imported_but_unused_by_kernel` | `28,471` | `98.50%` | `16.25%` | `2,358,861` | `142,363,653` | `Development.AbelianVarietyTheory` (`19,363`), `GroundTheory.HeightsAndTheta` (`1,598`), `Development.AutomorphicSpectrum` (`1,540`) |
| **Total** | **`28,904`** | **`100.00%`** | **`16.50%`** | **`2,378,537`** | **`143,583,600`** | Verified in `outputs/decomp/compute_atlas.json` |

### 2.1 Bucket 1: `module_import_unreachable` (`0` modules, `0` lines) `[L]`

Full BFS over `outputs/leanre.db` `module_edges` starting from `src/Main.lean:1` visits all `175,187` modules. Not a single `.lean` file in `data/rh_mirror/src` sits outside the transitive import graph of `Main`.

### 2.2 Bucket 2: `alignment_gap` (`19` modules, `1,631` lines) `[L]`

Inspection of `leanre/sighash.py` (`iter_source_decls`) and `outputs/kernel/kernel.db` exposes three exact causes why these `19` live-contributing modules received `0` rows in `decl_module`:

1. **`unmatched_named_decl` (`3` modules, `240` lines):**
   - `instance (priority := ...) name` breaks `sighash.py` (`with_sig=False` fast scanner): `src/Formalism/LocalToGlobal/ProjectiveLattices/RulInst.lean:13` (`Formalism.L2.Pj.rulesCommRing` and 6 sibling `rules*` instances, `wc=34`) and `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/NewformTwistNorms/NewformOfAdmissibleTwist.lean:21` (`GlobalTheory.Ord2.TwNewform.torsionFree`, `wc=181`).
   - Multi-component `namespace A.B.C` / `end C` stack bug (`leanre/sighash.py:1287-1292` pops the entire multi-component frame instead of suffix `C`): `src/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/CommonEigenvectors/KillPoly.lean:21` (`PositivityTheory.Rg.Rs.killPoly_holds`, `wc=25`).
2. **`anon_instance_unmatched` (`5` modules, `562` lines):** Strictly verified by matching `inst<Class>` name, confirming all kernel reverse dependents transitively import the candidate module, and confirming all project dependencies are transitively imported by that module (`decl_module.method = 'unmatched:project_auto_instance'`):
   - `src/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevD.lean:109` (`Formalism.BasicNotions.Examples₂.NZ.instInfinite_formalism`, `wc=205`)
   - `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExOm.lean:20` (`HcInf.instBorelSpaceUpqT`, `wc=34`)
   - `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/InstTopologicalSpaceHA.lean:16` (`HcS.BasicNotions.instTopologicalSpaceUpqT`, `wc=144`)
   - `src/GroundTheory/AutomorphicForms/GL2Classical/HeckeCommute.lean:34` (`GroundTheory.Automorphic.GL2Classical.instNeZeroNatHMul_groundTheory`, `wc=46`)
   - `src/GroundTheory/GlobalFields/Artin/Places.lean:17` (`GroundTheory.Global.Artin.instMulActionAlgEquivHeightOneSpectrumRingOfIntegers_groundTheory`, `wc=133`)
3. **`duplicate_decl_name_shadowed` (`11` modules, `829` lines):** `decl_module` is keyed `1:1` on `decl_id`, so when two modules define the same qualified theorem name and *both* have live kernel users importing them, `kernel.py` credits only the first module and leaves the second with `0` rows:
   - `src/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteIntegralCosetsOfBoundedDenominator.lean:10` (`GlobalTheory.ClassFin.adjugate_entry_mem_subring`, `wc=18`)
   - `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ClozelCohomology/ContinuousEntryPairings/ExistsConjPolynomialDefiniteUnitaryRational.lean:19` (`GlobalTheory.UnitaryBC.exists_cEmb_entry_eq`, `wc=50`)
   - `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ClozelCohomology/ContinuousEntryPairings/UnitaryCoordinateAlgebraDense.lean:10` (`GlobalTheory.PolyRealU.continuous_entry`, `wc=110`, where live kernel users exclusively import this file rather than `GlobalInterpolation`)
   - `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockTriangularMemMinimalParabolic.lean:255` (`GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi`, `wc=300`, exclusively imported by its kernel user)
   - `src/Development/WeilBound/CoreStatements/AutomorphicKernels/IsobaricBaseChange/IntegralCoefficientBaseChange/UnitaryBaseChangeCharacters/UnitaryBaseChangeLinks/LocalPointsIntegralAlmostAll.lean:18` (`GlobalTheory.LocRatPt.map_mem_UL`, `wc=91`)
   - `src/Development/WeilBound/SimpleEigenvalues/SimpleEigenvalueExtension/SimEig.lean:3` (`UpperTheory.V.LinAlg.simEig`, `wc=48`, used by `KillPoly4`)
   - `src/Lemmata/GeneralBFact/Imports.lean:8` (`Bl.general_b_fact.goal1`, `wc=25`, imported by `CauchyBinet`)
   - `src/Lemmata/GeneralBFactLast/Imports.lean:7` (`Bl.general_b_fact'''''''.goal1`, `wc=22`)
   - `src/Lemmata/GeneralBFactThirdAlt/Imports.lean:5` (`Bl.general_b_fact_third_alt.goal1`, `wc=37`)
   - `src/Lemmata/ProductIdentities/ProdInvZpowMulOfProdZpowEqOne.lean:22` (`Bl.ProductIdentities.goal1`, `wc=51`, imported by `THProvA`)
   - `src/PositivityTheory/AutomorphicForms/PublishedInputs/BorelInjectivity/EquivariantProjections/ExistsEquivariantProjOfLeSumIrreducible.lean:7` (`GlobalTheory.BorelCoh.exists_equivariant_proj_of_le_sum_irreducible`, `wc=77`)

*(Note `[L]`: `6` additional modules share duplicate names whose live kernel users exclusively import the sibling module, e.g., `FrameExBor`, `HostRam`, `TCHeights`, plus `4` modules whose `private` theorem collided unprefixed — these `10` supply no live kernel dependents and classify cleanly into `imported_but_unused_by_kernel`, with `4` tracked under `stale_duplicate_decl_unused`.)*

### 2.3 Bucket 3: `import_shim_reexport` (`164` modules, `959` lines) `[L]`

`150` flagged directly as `is_shim=1` in `leanre.db`, plus `14` pure `import`/`open`/`export`/`namespace`/`section` modules missed by `is_shim` (e.g., `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/CrystallineOrdinaryIdeals/Imports.lean:1` (`wc=8`) and `src/Formalism/LocalToGlobal/SiegelLatticeTheory/CasimirReductionTheory/OneParameterDerivatives/TauReduction/Imports.lean:1` (`wc=13`)). Top folders: `CompanionTheory` (`71`, `286` lines), `Development` (`49`, `269` lines), `Formalism` (`20`, `302` lines), `ReciprocityTheory` (`19`, `89` lines).

### 2.4 Bucket 4: `macro_tactic_elab_syntax_only` (`11` modules, `248` lines) `[L]`

Every one of these `11` files is completely erased before Lean 4 kernel export (contains zero theorems or non-meta mathematical definitions):

| Subkind | Module | File Anchor | Lines | Role `[L]` |
|---|---|---|---:|---|
| `run_cmd` (`5`) | `BuildAid.D1..D5` | `src/BuildAid/D1.lean:4`, `src/BuildAid/D2.lean:4`, `src/BuildAid/D3.lean:4`, `src/BuildAid/D4.lean:4`, `src/BuildAid/D5.lean:4` | `4` each (`20` tot) | Adds namespace prefixes to `Lean.LibrarySuggestions.nameDenyListExt` |
| `elab` (`3`) | `Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports` | `src/Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean:5` | `8` | Defines `elab "kexactB" e:term : tactic` |
| `elab` | `Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct` | `src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:53` | `66` | Defines `elab "kcopy"`, `elab "#kcopy_probe"`, and `Lean.Expr`/`MetaM` helpers |
| `elab` | `Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptCopy` | `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:87` | `91` | Defines `elab "cpt_copy_thms"` and `CoreM`/`Environment` decl-cloning helpers |
| `attribute` (`3`) | `...ThresholdArguments.DenseThresholdCases.LocalLanglandsGLOfPrints` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/LocalLanglandsGLOfPrints.lean:9` | `12` | Only `attribute [local instance]` + `open`/`namespace` |
| `attribute` | `...LocalTypeDictionary.BesselMapUniqueOfBesselModelUniqueness` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/BesselMapUniqueOfBesselModelUniqueness.lean:14` | `33` | Only `attribute [local instance]` + `section`/`variable` |
| `attribute` | `...DiscreteValuationRings.ExpandsPullOne` | `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsPullOne.lean:10` | `18` | Only `attribute [local instance]` + `open`/`variable` |

### 2.5 Bucket 5: `unexported_private_or_inline` (`239` modules, `16,838` lines) `[L]`

These `239` modules declare exclusively `private` items (`137` modules), `structure` (`67`), `abbrev` (`25`), and/or `instance` (`16`) with zero non-private theorems/lemmas/defs/inductives. **Key Lean 4 export finding `[L]`:** `outputs/kernel/kernel.db` proves empirically that Lean 4 **DOES export** `private`, `instance`, `structure`, `class`, and `@[inline]` declarations into `.olean`/kernel NDJSON whenever a live proof depends on them:

| Evidence in `outputs/kernel/kernel.db` + `outputs/leanre.db` | Count | Significance `[L]` |
|---|---:|---|
| `_private.%` kernel decls in `kernel.db` (`decl_module` `private_module`) | `112,310` (`82,799` matched) | `private` decls **export** to kernel whenever referenced |
| `inst*` kernel decls matched in `kernel.db` | `34,123` | `instance` decls **export** when typeclass synthesis uses them |
| Source `abbrev` / `structure` / `instance` / `class` in `leanre.db` | `13,202` / `8,286` / `8,199` / `43` | Export when referenced; `abbrev` unfolds away cleanly if unused directly |

Therefore, these `239` modules are absent from `kernel.db` **not because Lean hides `private`/`@[inline]`/`instance`/`structure`**, but because those private helpers/records/abbrevs were never needed by any of the 5 `Main` roots (`162` in `Development.AutomorphicArithmetic`, `12,965` lines).

### 2.6 Bucket 6: `imported_but_unused_by_kernel` (`28,471` modules, `2,358,861` lines) `[L]`

`98.50%` of all zero-kernel modules declare ordinary public `theorem`/`lemma`/`def` entries inside `Main`'s transitive import closure yet contribute zero constants to `solution.ndjson.zst`. Cross-referencing `outputs/flirt/tier1.db` (`[L]`):
- **`17,023` modules:** unique unused theorems/definitions (`19,363` modules in `Development.AbelianVarietyTheory`, `1,352,869` lines).
- **`7,336` modules:** `boilerplate_sigset_clone` (`1,164` `boilerplate_alpha_body_clone`).
- **`5,676` modules:** `statement_wrapper` (`*Statement.lean` re-exports unused by live proofs).
- **`4` modules:** stale unused duplicates shadowed by live siblings.

### 2.7 `DyadicPrimeIntervals.Run1..4` vs `ChebyshevPrimeBounds.SmallLoop` Chain Proof `[L]`

| Module | `wc -l` | Kernel Decls | Key Symbol & Status `[L]` | Direct Importers in `leanre.db` `[L]` |
|---|---:|---:|---|---|
| `...DyadicPrimeIntervals.SmallLoop` | `32` | `0` | `PI.PrimesDyadicRS.K.loop` (`ABSENT`) | `Run1..4`, `SmallNaturalNumbersBound` |
| `...DyadicPrimeIntervals.Run1`..`4` (`Run1.lean:6`..`Run4.lean:6`) | `8` each | `0` | `PI.PrimesDyadicRS.K.run1..4` (`ABSENT`) | `SmallNaturalNumbersBound` |
| `...DyadicPrimeIntervals.SmallNaturalNumbersBound` | `163` | `0` | `small_natural_numbers_bound` (`ABSENT`) | `OrbitalBoundsConclusion.PrimesDyadicRS` |
| `...OrbitalBoundsConclusion.PrimesDyadicRS` | `8` | `0` | `PI.PrimesDyadicRS.primes_dyadic_range` (`ABSENT`) | `ExplicitFormulaCounts.SqfCounts` |
| `...ExplicitFormulaCounts.SqfCounts` | `47` | `0` | `PI.EF.counts_closed` (`ABSENT`) | `LevelLetterCocycles.CylinderCountFamily` |
| `...LevelLetterCocycles.CylinderCountFamily` | `328` | `9` | `AllRowsAt`, `TieCountAt` LIVE; `family_bound_all:324` (`ABSENT`) | `JCount`, `AllRowsOf`, `IsUniUpMul`, `IrreducibleOfCountSizes` |
| `...JointConditionsZpowers.JCount` | `209` | `2` | `CountCylAt` LIVE; `family_count_all:204` (`ABSENT`) | `JCountP` |
| **`...ChebyshevPrimeBounds.SmallLoop`** | `26` | **`9`** | **`PI.PC.loop_run` (`#571291`), `_proof_1_1` (`#571290`, `flags=1`, `live_mask=31`)** | `ChebyshevPrimeBounds.CountSuccLe` (`PI.PC.count_succ_le`) → `PrimeCount` |

`CylinderCountFamily` (`src/Formalism/SharpRestriction/LevelLetterCocycles/CylinderCountFamily.lean:324`) and `JCount` (`src/Formalism/SharpRestriction/LevelLetterCocycles/JointConditionsZpowers/JCount.lean:204`) are the exact cut point explaining why `Main` transitively imports `DyadicPrimeIntervals.Run1..4` without using them in any kernel proof.

### 2.8 Deterministic Spot-Check Summary (`>= 30` per non-empty bucket `[L]`)

All `19` `alignment_gap` and all `11` `macro_tactic_elab_syntax_only` modules are enumerated in §2.2 and §2.4. Stratified `32`-module samples for each of the remaining 3 large buckets are persisted in `outputs/decomp/compute_atlas.json` (`spot_checks_per_bucket`), with verified representative anchors across each bucket:
- **`import_shim_reexport` (`32/164` checked):** `src/CompanionTheory/AutomorphicTheory/PieriRules/PieriDegreeBounds/AemeasurableBesselNormIntegrandBigCellImports.lean:1` (`wc=4`), `src/CompanionTheory/EightfoldTheory/VariationTheory/AutomorphicForms/AdTransfer.lean:1` (`wc=1`), `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/Imports.lean:1` (`wc=2`), `src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/UnitTraceSumBounds/Imports.lean:1` (`wc=91`), `src/ReciprocityTheory/GroupCohomology/ImportsAlt.lean:1` (`wc=13`), `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/CrystallineOrdinaryIdeals/Imports.lean:1` (`wc=8`).
- **`unexported_private_or_inline` (`32/239` checked):** `src/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/OLinearMaps.lean:21` (`structure`, `wc=50`), `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/JacquetShalikaRigidity.lean:23` (`structure`, `wc=32`), `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralCosetsDetFiniteSum.lean:15` (`instance`, `wc=29`), `src/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapCoefficientBoundStatement.lean:23` (`private`, `wc=208`), `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/IsobaricDense.lean:3` (`abbrev`, `wc=3`), `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCocompact/IsReducedInfiniteAdeleRing.lean:11` (`instance`, `wc=32`).
- **`imported_but_unused_by_kernel` (`32/28,471` checked):** `src/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean:8` (`wc=183`), `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdeleArchimedeanInclusionContinuousStatement.lean:9` (`statement_wrapper`, `wc=10`), `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrallyClosedPointLevelExtends.lean:31` (`sigset_clone`, `wc=164`), `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PairAdaptedPlaneCompatible.lean:35` (`wc=324`), `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/HformSmulRight.lean:12` (`alpha_body_clone`, `wc=179`), `src/GroundTheory/HeightsAndTheta/Heights/QuadraticFields/PSqfDiscr.lean:16` (`wc=147`).

---

## 3. Complete Kernel-Time Computation & Metaprogramming Atlas `[L]`

### 3.1 Kernel Reduction Flags vs Source Tactic Inventory `[L]`

| Metric / Construct | Total Files (LIVE / DEAD) | Total Hits (LIVE / DEAD) | Kernel DB Flags / Significance `[L]` |
|---|---:|---:|---|
| `F_REFL_TRUE` (`flags & 1`) | — | `129,492` live decls | `Eq.refl` proofs: driven by `rfl`, `norm_num`, `simp` closures, and `decide +kernel` `._proof_1_1` auxes |
| `F_OF_DECIDE` (`flags & 2`) | — | `472` live decls | `of_decide_eq_true` (`472/472` also have `flags & 1`); largest: `CoefPhaseG` (`79,103` `value_nodes`), `SplAdjUnit` (`72,243`) |
| `F_REDUCE_BOOL` / `F_REDUCE_NAT` / `F_SORRY` / `F_TRUST_COMPILER` | — | `0` / `0` / `0` / `0` | Zero compiler-trusted `native_decide`, `reduceBool`, `reduceNat`, or `sorry` in `solution.ndjson.zst` |
| `native_decide` / `decide_cbv` (source) | `0` (`0` / `0`) | `0` (`0` / `0`) | Completely absent from the 175k-file corpus |
| `decide +kernel` (source files) | `34` (`27` mod-live / `7` mod-dead) | `124` lines / `151` occ (`76` lines [`83` occ] / `48` lines [`68` occ]) | **Decl-level:** **`14` files (`31` lines/occ)** `LIVE_IN_KERNEL`, `13` files (`45` lines, `52` occ) `DEAD_IN_LIVE_MODULE`, `7` files (`48` lines, `68` occ) `ABSENT_DEAD` |
| `decide` (plain tactic) | `2,440` (`2,011` / `429`) | `6,735` (`5,637` / `1,098`) | Top file: `SpanPowerMembership.Primes` (`411` hits, Lucas primality witnesses) |
| `norm_num` (total / giant `>= 40` hits) | `9,608` (`8,040` / `1,568`) / `13` (`10` / `3`) | `24,581` (`20,114` / `4,467`) / `841` | Giant files (e.g. `SmallHostRootDiscriminantLe` `112` DEAD, `PChain` `77` LIVE) are algebraic inequality chains `[L]` |
| `rfl` | `62,752` (`54,485` / `8,267`) | `178,524` (`156,264` / `22,260`) | Struct/def unfolding & `Eq.refl` closures; feeds `F_REFL_TRUE` alongside `norm_num` |

### 3.2 Complete `decide +kernel` Inventory (`34` Files, `124` Matching Lines / `151` Occurrences) `[L]`

#### A. `LIVE_IN_KERNEL` (`14` files, `31` `decide +kernel` hits contributing live kernel terms, `live_mask = 31`)

| Module & Anchor | Hits (`Live`) | Kernel Target / Aux ID (`flags`, `value_nodes`, Min Hops) | Mathematical Content Checked |
|---|---:|---|---|
| `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/SmallLoop.lean:24` | `1` (`1`) | `PI.PC.loop_run` (`#571291`); aux `_proof_1_1` (`#571290`, `fl=1`, `vn=54`, `depth=21`) | `131070`-step `362` Chebyshev loop bound feeding `count_succ_le` |
| `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean:301` | `1` (`1`) | `GlobalTheory.PrimeRecip.table_ok` (`#570392`); aux `_proof_1_1` (`#570391`, `fl=1`, `vn=41`, `depth=19`) | `12`-interval rational sum of `1/p` across `100..16900` vs `1/(5*log p)` |
| `src/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean:120` | `3` (`3`) | `factorial_ladder_{thirteen,thirty_one,one_forty_one}` (`#226686` etc.; aux `vn=57`, `depth=20`) | Discrete factorial valuation ladders (`13`, `31`, `141`) on `100..20000` |
| `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SumVonMangoldtLeTwoMul.lean:12` | `1` (`1`) | `GlobalTheory.Mem.An.lcmUpto_le_four_pow_small` (`#236969`; aux `#236968`, `fl=1`, `vn=78`, `depth=23`) | Brute-force `Nat.lcmUpto n <= 4^n` for `n <= 100` |
| `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiUpperBoundOfLtThirtyMulSixPow.lean:28` | `1` (`1`) | `PI.PC.lcmUpto_le_three_pow` (`#571175`; aux `#571174`, `fl=1`, `vn=82`, `depth=23`) | Brute-force `Nat.lcmUpto n <= 3^n` for `n < 30` |
| `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SeparationNumericalIneqCuspidalGL.lean:74` | `9` (`9`) | `GlobalTheory.CuspGL.sep_numerical_ineq` (`#958760`, `vn=39025`); aux `#958744` (`fl=1`, `vn=699`, `depth=18`) | Explicit `Nat.primeFactors n` for `n = 2..10` |
| `src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeInvariantsPeriodPairDictionary.lean:135` | `1` (`1`) | `GlobalTheory.LatticeInvariants.discr_of_cyclic` (`#391540`); aux `#391535` (`fl=1`, `vn=72`, `depth=14`) | `bernoulli 6 = 1/42` (`ζ(6) = π^6/945`) |
| `src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsPolynomialModularJOfHasQExpansion.lean:65` | `2` (`2`) | `GlobalTheory.qExpansion_E₄`, `qExpansion_E₆` (`#392111` etc.; aux `vn=62, 57`, `depth=21`) | `bernoulli 4 = -1/30`, `bernoulli 6 = 1/42` (`E_4`, `E_6` q-expansions) |
| `src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsVariableChangeEqLatticeCurve.lean:107` | `1` (`1`) | `GlobalTheory.g₃_eq_E₆` (`#98582`, `fl=1`); aux `#98580` (`fl=1`, `vn=72`, `depth=11`) | `bernoulli 6 = 1/42` (`E_6` / `g_3` normalization) |
| `src/GroundTheory/GlobalFields/ComplexMultiplication/JInvariant.lean:47` | `1` (`1`) | `GroundTheory.Global.Elliptic.riemannZeta_six` (`#1018121`); aux `#1018120` (`fl=1`, `vn=57`, `depth=19`) | `bernoulli 6 = 1/42` |
| `src/ReciprocityTheory/DualLattices/Eisenstein4CoeffBound.lean:17` | `2` (`2`) | `ReciprocityTheory.PGsh.qExpansion_E₄_eq`, `qExpansion_E₆_eq` (`#1033161`, `vn=1880`, `depth=26`) | `bernoulli 4 = -1/30`, `bernoulli 6 = 1/42` (inline check) |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/FrobeniusSmoothVectors/EpDimb.lean:77` | `1` (`1`) | `_private...EpDimb.0.db_counts` (`#1279565`; aux `#1279564`, `fl=1`, `vn=346`, `depth=21`) | Exhaustive cardinality bounds on `Fin 3 -> ZMod 2` (`>=4`, `>=2`) |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/CompactIntegralFields/RedList.lean:13` | `2` (`2`) | `_private...RedList.0.UpperTheory.V.Ws.redM_key`, `redT_ex` (`#1333690`; aux `#1333689`, `vn=432`) | Exhaustive 8-Boolean `4x4` transitive closure SAT (`256` states) |
| `src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean:558` | `5` (`5`) | `Formalism.BasicNotions.Examples₂.BB_disj0` (`#575708`, `fl=1`, `vn=895`, `depth=25`; aux `#575699`) | Disjointness of `BB 9 413718278401` and `BB 9 603339156001` (`+ 411` `decide` Lucas checks) |

#### B. `DEAD_IN_LIVE_MODULE` (`13` live files, `45` matching lines / `52` occurrences absent from `solution.ndjson.zst`)

`4` are unexported `example`s (`src/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/LoweredSignatureVanishing.lean:47`, `src/Development/AbelianVarietyTheory/Definitions/Divisors/KernelNormConstantSpec.lean:357` [`3` occ on `2` lines], `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/TwSingle.lean:74`, `src/Formalism/GL3MeanSquares/HookFormulaTorsion/SquareEqDiagOfQuadraticEven.lean:91`), and `9` are unused concrete sanity checks/counterexamples inside modules whose *general* lemmas are live: `src/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean:359` (`exEntries_good`, `2` lines), `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SecondChernDegreeVanishesTrueSurfaces.lean:385` (`Fact (¬ IsSquare 29)` instance, `1` line), `src/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean:557` (`Level3.isCub_cube` / `chi7`, `7` lines / `10` occ), `src/Development/AbelianVarietyTheory/Definitions/Foundations/StrictInterlaceIffDescEnum.lean:1029` (`exGrid_*`, `14` lines / `15` occ), `src/Development/AbelianVarietyTheory/Definitions/Foundations/UnitarySixTwoHarishChandraParameter.lean:27` (`grid4` / `Icc (-6) 6`, `8` lines / `10` occ), `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/AuxiliaryPrimeMemAvoidedPrimes.lean:290` (`primeToPart_of_cube` / `minkM`, `2` lines), `src/Formalism/LocalRingCardinality/SpanPowerMembership.lean:40` (`exampleHost_split_prime_split`, `2` lines), `src/Formalism/LocalToGlobal/Columns/ChainInst.lean:1780` (`toyPrimes` / `xi_unit`, `3` lines), and `src/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean:303` (`witness_thirteen`, `1` line).

#### C. `ABSENT_DEAD` (`7` zero-kernel files, `48` matching lines / `68` occurrences)

`Run1..4` (`src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run1.lean:6`..`Run4.lean:6`, `4` lines), `FoundationsPrimeFact` (`src/Development/AbelianVarietyTheory/Definitions/Foundations/FoundationsPrimeFact.lean:44`, `15` lines / `23` occ), `CyclotomicIsCyclotomicExtension` (`src/Formalism/LocalToGlobal/Columns/CyclotomicIsCyclotomicExtension.lean:404`, `27` lines / `39` occ on 438-digit `nd2N`), and `DeltaQExpansionIntegral` (`src/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/DeltaQExpansionIntegral.lean:23`, `2` lines).

### 3.3 Giant `norm_num`, `rfl`/Numeric Tables, & Metaprogramming / Proof-Copy Macros `[L]`

- **Giant `norm_num` (`>= 40` hits, `13` files):** Top files include `SmallHostRootDiscriminantLe` (`112` hits, DEAD, `src/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SmallHostRootDiscriminantLe.lean:1`), `CosetExpUnique` (`85`, DEAD), `PChain` (`77`, LIVE, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean:28`), `ExponentInequalityNondegenerateMid` (`73`, LIVE, `src/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExponentInequalityNondegenerateMid.lean:8`), and `TopChoiceBounds` (`65`, LIVE). Direct reading confirms these are symbolic real-exponent / asymptotic algebraic proofs (`norm_num` + `linarith` + `positivity`), not lookup tables.
- **`decide` (plain) & Lucas Primality (`411` hits in `Primes`):** `SpanPowerMembership.Primes` (`src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean:558`, `49` live kernel decls, `336` literals `>= 18` digits) combines `decide` + `norm_num` + `BB_disj0` (`decide +kernel`) to prove Lucas/Pocklington primality of `413718278401`, `603339156001`, and the 116-digit witness `prime_large` feeding `SpanPowerMembership.record_nonempty_of_localGap`.
- **Metaprogramming & Copy Macros:**
  - **`CutCptCopy` (`cpt_copy_thms`):** `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:87` defines command macro `cpt_copy_thms`; invoking it at `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutMainCpt.lean:945` synthesizes `5` live kernel theorems (`Formalism.FourierDecayAlt.P.CutBP.{glFibreCpt, block_growth_bound_of_compact_coefCpt, germ_data_low_levelsCpt, low_level_gramCpt, low_level_fibreCpt}`, all `live_mask=31`, `decl_module.method='generated:CutCptCopy'`).
  - **`SideCopy.copy_cases` → `#1` & `#2` Largest Proof Terms in `kernel.db`:** `scoped macro "copy_cases"` at `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingSpecNormalisedCharacterEq.lean:75` destructures ~60 fields of `CopyAll`, inflating `lam_copy` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamCopy.lean:15`) to **`5,538,373`** `value_nodes` (`#1` in `kernel.db`) and `sigSpan_copy` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingSpecNormalisedCharacterEq.lean:97`) to **`4,598,428`** `value_nodes` (`#2`), alongside `3` more uses in `ExportTieMove`, `SideEigenformCopyTransfer`, and dead `EnlargedBaseLb2Rows`.
  - **`kexactB`:** Defined at `src/Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean:5` (`elab`); invoked `234` times across `50` files (`46` LIVE, `4` DEAD) for `Term.elabTermAndSynthesize` + direct `g.assign`.
  - **`kcopy`:** Defined at `src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:53` (`elab`, dead utility module); invoked in `FormsRe` (`345` live decls), `HermRe` (`95`), and `ExistsKeptChoiceUpperLattice` (`4`).
  - **`macro` / `syntax` / `run_tac` / `run_cmd`:** `macro` (`64` files / `87` hits: `59` LIVE / `5` DEAD); `syntax`/`notation` (`952` / `1,722`: `798` / `154`); `run_tac` (`16` / `32`: `15` LIVE / `1` DEAD); `run_cmd` (`5` / `5`: `BuildAid.D1..D5`, all DEAD).

### 3.4 Explicitly Certified Mathematical Quantities `[L]`

| Mathematical Object / Bound Certified | File & Line Anchor | Symbol & Status | Range / Witnesses / Role |
|---|---|---|---|
| Prime reciprocal sums vs `1/(5*log p)` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean:301` | `GlobalTheory.PrimeRecip.table_ok` (`LIVE_IN_KERNEL`) | `12` explicit intervals from `100` to `16900` (`decide +kernel`) |
| Chebyshev `SmallLoop` bound | `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/SmallLoop.lean:24` | `PI.PC.loop_run` (`LIVE_IN_KERNEL`) | `131070`-step / `362` threshold loop feeding `count_succ_le` (`decide +kernel`) |
| Dyadic prime intervals `Run1..4` | `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run1.lean:6` | `PI.PrimesDyadicRS.K.run1..4` (`ABSENT_DEAD`) | Intervals `32768`, `65536`, `98304`, `131072` — **0 decls in `kernel.db`** |
| Padic valuation factorial ladders | `src/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean:120` | `Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.factorial_ladder_one_forty_one` (`LIVE_IN_KERNEL`) | Stages `13`, `31`, `141` covering `100..20000` (`decide +kernel`) |
| Chebyshev `lcm(1..n) <= 4^n` (`n <= 100`) | `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SumVonMangoldtLeTwoMul.lean:12` | `GlobalTheory.Mem.An.lcmUpto_le_four_pow_small` (`LIVE_IN_KERNEL`) | Exact brute-force check on `0..100` (`decide +kernel`) |
| Chebyshev `lcm(1..n) <= 3^n` (`n < 30`) | `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiUpperBoundOfLtThirtyMulSixPow.lean:28` | `PI.PC.lcmUpto_le_three_pow` (`LIVE_IN_KERNEL`) | Exact brute-force check on `0..29` (`decide +kernel`) |
| `Nat.primeFactors` (`n = 2..10`) | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SeparationNumericalIneqCuspidalGL.lean:74` | `GlobalTheory.CuspGL.sep_numerical_ineq` (`LIVE_IN_KERNEL`) | Finite prime-factor sets for `n <= 10` (`decide +kernel`) |
| Bernoulli `B_4 = -1/30`, `B_6 = 1/42` | `src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsPolynomialModularJOfHasQExpansion.lean:65` | `GlobalTheory.qExpansion_E₄`, `riemannZeta_six`, `g₃_eq_E₆` (`LIVE_IN_KERNEL`) | Rational Bernoulli evaluations (`E_4`, `E_6`, `ζ(6)=π^6/945`) (`decide +kernel`) |
| Weak Shimura `4x4` Boolean SAT | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/CompactIntegralFields/RedList.lean:13` | `UpperTheory.V.Ws.redM_key` (`LIVE_IN_KERNEL`) | `2^8 = 256` states over `Fin 4 -> Fin 4 -> Bool` (`decide +kernel`) |
| Frobenius vector counts on `Fin 3 -> ZMod 2` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/FrobeniusSmoothVectors/EpDimb.lean:77` | `db_counts` (`LIVE_IN_KERNEL`) | All `8` maps `Fin 3 -> ZMod 2` (`decide +kernel`) |
| `D7` Cyclotomic Lucas primes | `src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean:558` | `Formalism.BasicNotions.Examples₂.BB_disj0`, `gA_prime` (`LIVE_IN_KERNEL`) | `751`, `991`, `413718278401`, `603339156001`, 116-digit `prime_large` (`decide` + `decide +kernel`) |
| `SL2` witness / `toyPrimes` / `grid4` / `exGrid` | `src/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean:303` | `witness_thirteen`, `primes_over_one_mod_four`, `unitary_six_two_grid_counts` (`DEAD_IN_LIVE_MODULE`) | Concrete witnesses (`k=13` / `24`, `q<=29`, `U(6,2)`) absent from `kernel.db` |
| Abelian variety Lucas primes | `src/Development/AbelianVarietyTheory/Definitions/Foundations/FoundationsPrimeFact.lean:44` | `GlobalTheory.Mem.Cert.foundations_prime_fact_ter` (`ABSENT_DEAD`) | `10944929`, `128860109809`, `328347841`, `1395478321` (`0` decls in `kernel.db`) |
| `438`-digit `nd2N` modular checks (`27` lines / `39` occ) | `src/Formalism/LocalToGlobal/Columns/CyclotomicIsCyclotomicExtension.lean:404` | `nd2N`, `example_first_prime` (`ABSENT_DEAD`) | Explicit primality / divisor checks on `nd2N` (`0` decls in `kernel.db`) |
