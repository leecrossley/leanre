# Navier–Stokes Blow-up (Alpöge–Buckmaster)

Finite-time blow-up for Navier–Stokes (Alpöge–Buckmaster); Arb 128-bit certificate external.

## Provenance & Scope

- **Repository:** [https://github.com/tristanbuckmaster/navier-stokes](https://github.com/tristanbuckmaster/navier-stokes)
- **Pinned commit:** `ad53419de079` (`ad53419de079eb8f95f60313473374624a348546`)
- **License:** None (no license)
- **Analysis mode:** Source-level import and declaration scan (no compiled kernel export)
- **Entry module:** `Solution` (reaches **2,257 / 2,270** modules, **99.4%**)

## Scale & Composition

| Metric | Value |
| --- | ---: |
| Lean modules | 2,270 |
| Lines of code | 616,031 |
| Project import edges | 6,569 |
| Declarations (source) | 38,576 |
| Theorems / lemmas | 30,057 |
| Defs / abbrevs / instances | 7,662 |
| Inductives / structures / classes | 857 |
| Custom `axiom` declarations | 0 |
| Proof `sorry` / `admit` hits | 0 (0 files) |
| Challenge-spec `sorry` hits | 24 (10 files) |
| `decide +kernel` hits | 0 |

## Repository Notes & Caveats

- External numerical certificate caveat (README.md): the 128-bit Arb/FLINT interval-arithmetic certificate referenced by the paper is external and not included in this repository.
- Build caveat (README.md): the patched Lean package was not rebuilt after the final cell-layer patch.
- Comparator layout: challenge/statement files (`ComparatorChallenges/` / `*Challenge*.lean`) intentionally hold `sorry` placeholders separated from proof modules.

## Axioms, Incomplete Proofs, and Kernel Directives

### Challenge-spec `sorry`: 24 hits in 10 files

- [CellLayerChallenge:L7052](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L7052) — `Breakdown.CellLayerSystem.breakdownOnSpace_of_cell_system_condition`
- [CellLayerChallenge:L7073](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L7073) — `Breakdown.CellLayerSystem.breakdownOnTorus_of_cell_system_condition`
- [CellLayerChallenge:L7080](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L7080) — `Breakdown.CellLayerSystem.breakdownOnSpaceAndTorus_of_cell_system_condition`
- [CellLayerTheorems:L16](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerTheorems.lean#L16) — `Breakdown.CellLayerSystem.breakdownOnSpace_of_cell_system_condition`
- [CellLayerTheorems:L22](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerTheorems.lean#L22) — `Breakdown.CellLayerSystem.breakdownOnTorus_of_cell_system_condition`
- [CellLayerTheorems:L29](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerTheorems.lean#L29) — `Breakdown.CellLayerSystem.breakdownOnSpaceAndTorus_of_cell_system_condition`
- [CertificateChallenge:L220](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L220) — `Breakdown.certificate_orbit`
- [Challenge:L102](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L102) — `Breakdown.breakdown_on_space`
- [Challenge:L105](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L105) — `Breakdown.breakdown_on_torus`
- [Challenge:L108](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L108) — `Breakdown.breakdown_on_space_of_weak`
- [CoerciveChallenge:L530](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L530) — `Breakdown.ModeWeights.multiplier_density`
- [CoerciveChallenge:L582](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L582) — `Breakdown.ModeWeights.mode_azimuthal_gain`
- [CoerciveChallenge:L601](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L601) — `Breakdown.ModeWeights.stretch_mean_bound`
- [CoerciveChallenge:L959](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L959) — `Breakdown.PieceWeights.piece_multiplier_density`
- [ExtendedCertificateChallenge:L259](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L259) — `Breakdown.isExtendedCertificate_withUnitWeight`
- … and 9 more

## Duplication & Directory Alignment

- **Directory-vs-namespace outliers:** 3 files (0.1%; 0 high, 3 medium)
- **Identical-body file clones:** 1 cluster (1 redundant file)
- **Identical-signature file clusters:** 10 clusters (45 redundant files)
- **Import-only shims:** 5

## Most-Imported Modules (Top 10)

| Module | Direct Importers | Transitive Importers | Lines | Declarations |
| --- | ---: | ---: | ---: | ---: |
| [Breakdown.FreqTr.Realization](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L1) | 59 | 854 | 151 | 30 |
| [Breakdown.Cert.CoerciveNodes](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveNodes.lean#L1) | 43 | 785 | 765 | 66 |
| [Breakdown.FreqTr.Statements](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L1) | 43 | 1,182 | 207 | 53 |
| [Breakdown.Cert.Nodes](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L1) | 42 | 488 | 290 | 48 |
| [Breakdown.CertCell.BridgeStatements](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L1) | 41 | 456 | 716 | 71 |
| [Breakdown.CertCell.StatementDefs](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1) | 37 | 528 | 6,263 | 619 |
| [Breakdown.CertCell.AssemblyStatements](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L1) | 37 | 141 | 836 | 106 |
| [Breakdown.Cert.CoerciveRotation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveRotation.lean#L1) | 35 | 416 | 110 | 14 |
| [Breakdown.Cert.CoercivePerturbationFactsProof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoercivePerturbationFactsProof.lean#L1) | 32 | 390 | 752 | 50 |
| [Breakdown.CertCell.ShapeStatements](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L1) | 32 | 285 | 286 | 44 |
