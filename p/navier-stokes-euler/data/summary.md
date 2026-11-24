# Navier–Stokes & Euler Blow-up (OpenAI)

Lean 4 formalizations of Navier–Stokes and Euler finite-time blow-up.

## Provenance & Scope

- **Repository:** [https://github.com/openai/NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler)
- **Pinned commit:** `f9e8bc5b38b6` (`f9e8bc5b38b6e212696e8a30e3e91517af887bbd`)
- **License:** Apache-2.0
- **Analysis mode:** Source-level import and declaration scan (no compiled kernel export)
- **Entry modules:** `NavierStokes`, `Euler` (combined reach: **2,524 / 2,659** modules, **94.9%**; NavierStokes 753, Euler 1,771)

## Scale & Composition

| Metric | Value |
| --- | ---: |
| Lean modules | 2,659 |
| Lines of code | 641,332 |
| Project import edges | 6,105 |
| Declarations (source) | 52,516 |
| Theorems / lemmas | 38,531 |
| Defs / abbrevs / instances | 13,304 |
| Inductives / structures / classes | 681 |
| Custom `axiom` declarations | 0 |
| Proof `sorry` / `admit` hits | 0 (0 files) |
| Challenge-spec `sorry` hits | 4 (2 files) |
| `decide +kernel` hits | 0 |

## Repository Notes & Caveats

- Comparator layout: challenge/statement files (`ComparatorChallenges/` / `*Challenge*.lean`) intentionally hold `sorry` placeholders separated from proof modules.

## Axioms, Incomplete Proofs, and Kernel Directives

### Challenge-spec `sorry`: 4 hits in 2 files

- [ComparatorChallenges.Euler:L88](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/Euler.lean#L88) — `Euler.euler_breakdown_R3`
- [ComparatorChallenges.Euler:L184](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/Euler.lean#L184) — `Euler.exists_compact_smooth_euler_singularity`
- [ComparatorChallenges.NavierStokes:L277](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/NavierStokes.lean#L277) — `NavierStokes.Comparator.navier_stokes_breakdown_R3`
- [ComparatorChallenges.NavierStokes:L284](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/NavierStokes.lean#L284) — `NavierStokes.Comparator.navier_stokes_breakdown_periodic`

## Duplication & Directory Alignment

- **Directory-vs-namespace outliers:** 1 file (0.0%; 0 high, 1 medium)
- **Identical-body file clones:** 13 clusters (13 redundant files)
- **Identical-signature file clusters:** 14 clusters (14 redundant files)
- **Import-only shims:** 5

## Most-Imported Modules (Top 10)

| Module | Direct Importers | Transitive Importers | Lines | Declarations |
| --- | ---: | ---: | ---: | ---: |
| [Euler.EulerProof](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/Euler/EulerProof.lean#L1) | 32 | 1,793 | 20,755 | 1,239 |
| [Euler.ContinuousTimeIntegral](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/Euler/ContinuousTimeIntegral.lean#L1) | 15 | 970 | 134 | 15 |
| [NavierStokes.CorrectionStep](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/CorrectionStep.lean#L1) | 13 | 148 | 9,849 | 559 |
| [NavierStokes.R3.ProblemStatement](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/ProblemStatement.lean#L1) | 13 | 124 | 222 | 25 |
| [Euler.ParameterSobolevCoefficient](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/Euler/ParameterSobolevCoefficient.lean#L1) | 13 | 831 | 106 | 8 |
| [NavierStokes.R3.ComparisonSetup](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/ComparisonSetup.lean#L1) | 13 | 70 | 56 | 11 |
| [NavierStokes.VariableGaugeMean](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/VariableGaugeMean.lean#L1) | 12 | 235 | 3,004 | 190 |
| [NavierStokes.PhysicalStageBounds](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/PhysicalStageBounds.lean#L1) | 12 | 101 | 626 | 54 |
| [NavierStokes.ActualCycleParameters](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ActualCycleParameters.lean#L1) | 12 | 75 | 517 | 88 |
| [NavierStokes.WeightedClasses](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/WeightedClasses.lean#L1) | 12 | 378 | 517 | 45 |
