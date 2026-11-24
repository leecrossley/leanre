# Carleson

Formalization of generalized Carleson's theorem on doubling metric measure spaces.

## Provenance & Scope

- **Repository:** [https://github.com/fpvandoorn/carleson](https://github.com/fpvandoorn/carleson)
- **Pinned commit:** `f7487cc9da4d` (`f7487cc9da4d1e73f009dc0280cd5b958f3e2c78`)
- **License:** Apache-2.0
- **Analysis mode:** Source-level import and declaration scan (no compiled kernel export)
- **Entry module:** `Carleson` (reaches **125 / 127** modules, **98.4%**)

## Scale & Composition

| Metric | Value |
| --- | ---: |
| Lean modules | 127 |
| Lines of code | 50,189 |
| Project import edges | 332 |
| Declarations (source) | 3,103 |
| Theorems / lemmas | 2,599 |
| Defs / abbrevs / instances | 468 |
| Inductives / structures / classes | 36 |
| Custom `axiom` declarations | 0 |
| Proof `sorry` / `admit` hits | 3 (1 file) |
| Challenge-spec `sorry` hits | 3 (1 file) |
| `decide +kernel` hits | 0 |

## Repository Notes & Caveats

- Comparator layout: challenge/statement files (`ComparatorChallenges/` / `*Challenge*.lean`) intentionally hold `sorry` placeholders separated from proof modules.

## Axioms, Incomplete Proofs, and Kernel Directives

### Proof `sorry` / `admit`: 3 hits in 1 file

- [Carleson.ToMathlib.RealInterpolation.LorentzInterpolation:L23](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/ToMathlib/RealInterpolation/LorentzInterpolation.lean#L23) — `C_LorentzInterpolation`
- [Carleson.ToMathlib.RealInterpolation.LorentzInterpolation:L28](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/ToMathlib/RealInterpolation/LorentzInterpolation.lean#L28) — `C_LorentzInterpolation_pos`
- [Carleson.ToMathlib.RealInterpolation.LorentzInterpolation:L44](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/ToMathlib/RealInterpolation/LorentzInterpolation.lean#L44) — `exists_hasLorentzType_real_interpolation`

### Challenge-spec `sorry`: 3 hits in 1 file

- [Challenge:L420](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Challenge.lean#L420) — `classical_carleson_theorem`
- [Challenge:L437](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Challenge.lean#L437) — `metric_space_carleson`
- [Challenge:L454](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Challenge.lean#L454) — `linearized_metric_space_carleson`

## Duplication & Directory Alignment

- **Directory-vs-namespace outliers:** 2 files (1.6%; 0 high, 2 medium)
- **Identical-body file clones:** 0 clusters
- **Identical-signature file clusters:** 0 clusters
- **Import-only shims:** 0

## Most-Imported Modules (Top 10)

| Module | Direct Importers | Transitive Importers | Lines | Declarations |
| --- | ---: | ---: | ---: | ---: |
| [Carleson.TileStructure](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/TileStructure.lean#L1) | 7 | 35 | 630 | 94 |
| [Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/ToMathlib/MeasureTheory/Function/LpSeminorm/Basic.lean#L1) | 7 | 50 | 158 | 12 |
| [Carleson.ToMathlib.Misc](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/ToMathlib/Misc.lean#L1) | 6 | 82 | 801 | 87 |
| [Carleson.ToMathlib.MeasureTheory.Measure.NNReal](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/ToMathlib/MeasureTheory/Measure/NNReal.lean#L1) | 6 | 54 | 686 | 63 |
| [Carleson.Calculations](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/Calculations.lean#L1) | 6 | 30 | 357 | 29 |
| [Carleson.Defs](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/Defs.lean#L1) | 6 | 67 | 324 | 36 |
| [Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Regular](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/ToMathlib/MeasureTheory/Measure/NoAtoms/Regular.lean#L1) | 6 | 48 | 96 | 2 |
| [Carleson.ToMathlib.Distribution](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/ToMathlib/Distribution.lean#L1) | 5 | 50 | 605 | 54 |
| [Carleson.ToMathlib.HardyLittlewood](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/ToMathlib/HardyLittlewood.lean#L1) | 5 | 32 | 411 | 16 |
| [Carleson.Classical.Basic](https://github.com/fpvandoorn/carleson/blob/f7487cc9da4d1e73f009dc0280cd5b958f3e2c78/Carleson/Classical/Basic.lean#L1) | 5 | 16 | 298 | 26 |
