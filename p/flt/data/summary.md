# Fermat's Last Theorem (FLT)

Imperial College London formalization of Fermat's Last Theorem in Lean 4.

## Provenance & Scope

- **Repository:** [https://github.com/ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT)
- **Pinned commit:** `019805815d7d` (`019805815d7da565ed1e9f427b6fbd0cbc9d00d3`)
- **License:** Apache-2.0
- **Analysis mode:** Source-level import and declaration scan (no compiled kernel export)
- **Entry module:** `FLT` (reaches **261 / 265** modules, **98.5%**)

## Scale & Composition

| Metric | Value |
| --- | ---: |
| Lean modules | 265 |
| Lines of code | 58,362 |
| Project import edges | 663 |
| Declarations (source) | 3,732 |
| Theorems / lemmas | 2,241 |
| Defs / abbrevs / instances | 1,440 |
| Inductives / structures / classes | 48 |
| Custom `axiom` declarations | 3 |
| `sorry` / `admit` hits | 60 (20 files) |
| `decide +kernel` hits | 0 |

## Axioms, Incomplete Proofs, and Kernel Directives

### `sorry` / `admit`: 60 hits in 20 files

- [FLT.Data.HurwitzRatHat:L74](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Data/HurwitzRatHat.lean#L74) — `HurwitzRatHat.injective_hRat`
- [FLT.Data.HurwitzRatHat:L90](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Data/HurwitzRatHat.lean#L90) — `HurwitzRatHat.injective_zHat`
- [FLT.Data.HurwitzRatHat:L94](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Data/HurwitzRatHat.lean#L94) — `HurwitzRatHat.canonicalForm`
- [FLT.Data.HurwitzRatHat:L96](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Data/HurwitzRatHat.lean#L96) — `HurwitzRatHat.completed_units`
- [FLT.Deformations.LiftFunctor:L117](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Deformations/LiftFunctor.lean#L117) — `Deformation.flatFunctor`
- [FLT.Deformations.Representable:L38](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Deformations/Representable.lean#L38) — `Deformation.isCorepresentable_deformationFunctor`
- [FLT.Deformations.Representable:L106](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Deformations/Representable.lean#L106) — `isCorepresentable_narrowSLiftFunctor`
- [FLT.EllipticCurve.Torsion:L46](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/EllipticCurve/Torsion.lean#L46) — `WeierstrassCurve.n_torsion_finite`
- [FLT.EllipticCurve.Torsion:L52](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/EllipticCurve/Torsion.lean#L52) — `WeierstrassCurve.n_torsion_card`
- [FLT.EllipticCurve.Torsion:L57](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/EllipticCurve/Torsion.lean#L57) — `group_theory_lemma`
- [FLT.EllipticCurve.Torsion:L75](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/EllipticCurve/Torsion.lean#L75) — `_anon_74`
- [FLT.EllipticCurve.Torsion:L109](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/EllipticCurve/Torsion.lean#L109) — `WeierstrassCurve.galoisRepresentation`
- [FLT.EllipticCurve.Torsion:L110](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/EllipticCurve/Torsion.lean#L110) — `WeierstrassCurve.galoisRepresentation`
- [FLT.EllipticCurve.Torsion:L111](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/EllipticCurve/Torsion.lean#L111) — `WeierstrassCurve.galoisRepresentation`
- [FLT.EllipticCurve.Torsion:L112](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/EllipticCurve/Torsion.lean#L112) — `WeierstrassCurve.galoisRepresentation`
- … and 45 more

### `axiom`: 3 hits in 3 files

- [FLT.Assumptions.KnownIn1980s:L79](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Assumptions/KnownIn1980s.lean#L79) — `knownin1980s`
- [FLT.Assumptions.Mazur:L105](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Assumptions/Mazur.lean#L105) — `Mazur_statement`
- [FLT.Assumptions.Odlyzko:L58](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Assumptions/Odlyzko.lean#L58) — `Odlyzko_statement`

## Duplication & Directory Alignment

- **Directory-vs-namespace outliers:** 62 files (23.4%; 5 high, 57 medium)
- **Identical-body file clones:** 1 cluster (4 redundant files)
- **Identical-signature file clusters:** 0 clusters
- **Import-only shims:** 2

## Most-Imported Modules (Top 10)

| Module | Direct Importers | Transitive Importers | Lines | Declarations |
| --- | ---: | ---: | ---: | ---: |
| [FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L1) | 9 | 40 | 59 | 4 |
| [FLT.Slop.PGL2.FiniteSubgroups.PGLBasic](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Slop/PGL2/FiniteSubgroups/PGLBasic.lean#L1) | 8 | 16 | 1,656 | 45 |
| [FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Mathlib/NumberTheory/NumberField/FiniteAdeleRing.lean#L1) | 8 | 18 | 87 | 8 |
| [FLT.NumberField.Completion.Finite](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/NumberField/Completion/Finite.lean#L1) | 8 | 33 | 80 | 8 |
| [FLT.HaarMeasure.HaarChar.AddEquiv](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/HaarMeasure/HaarChar/AddEquiv.lean#L1) | 7 | 19 | 390 | 11 |
| [FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean#L1) | 6 | 32 | 739 | 48 |
| [FLT.Mathlib.Topology.Algebra.Module.ModuleTopology](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean#L1) | 6 | 38 | 540 | 37 |
| [FLT.Deformations.RepresentationTheory.GaloisRep](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Deformations/RepresentationTheory/GaloisRep.lean#L1) | 6 | 18 | 412 | 52 |
| [FLT.AutomorphicForm.GroupTheoryStuff](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/AutomorphicForm/GroupTheoryStuff.lean#L1) | 6 | 19 | 383 | 47 |
| [FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic](https://github.com/ImperialCollegeLondon/FLT/blob/019805815d7da565ed1e9f427b6fbd0cbc9d00d3/FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean#L1) | 6 | 37 | 318 | 23 |
