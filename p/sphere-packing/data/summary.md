# Sphere Packing (Viazovska E8)

Lean 4 formalization of Maryna Viazovska's 8-dimensional sphere packing theorem.

## Provenance & Scope

- **Repository:** [https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
- **Pinned commit:** `e07215872319` (`e07215872319dcadd7ced28670ae4daa13b74b8d`)
- **License:** Apache-2.0
- **Analysis mode:** Source-level import and declaration scan (no compiled kernel export)
- **Entry module:** `SpherePacking` (reaches **73 / 73** modules, **100.0%**)

## Scale & Composition

| Metric | Value |
| --- | ---: |
| Lean modules | 73 |
| Lines of code | 15,446 |
| Project import edges | 197 |
| Declarations (source) | 1,212 |
| Theorems / lemmas | 947 |
| Defs / abbrevs / instances | 261 |
| Inductives / structures / classes | 2 |
| Custom `axiom` declarations | 2 |
| `sorry` / `admit` hits | 61 (19 files) |
| `decide +kernel` hits | 2 |

## Axioms, Incomplete Proofs, and Kernel Directives

### `sorry` / `admit`: 61 hits in 19 files

- [SpherePacking.Basic.PeriodicPacking:L1220](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/Basic/PeriodicPacking.lean#L1220) — `periodic_constant_eq_constant`
- [SpherePacking.CohnElkies.LPBound:L358](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/CohnElkies/LPBound.lean#L358) — `calc_steps`
- [SpherePacking.CohnElkies.LPBound:L388](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/CohnElkies/LPBound.lean#L388) — `calc_steps`
- [SpherePacking.CohnElkies.LPBound:L392](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/CohnElkies/LPBound.lean#L392) — `calc_steps`
- [SpherePacking.CohnElkies.LPBound:L467](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/CohnElkies/LPBound.lean#L467) — `calc_steps`
- [SpherePacking.CohnElkies.Prereqs:L110](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/CohnElkies/Prereqs.lean#L110) — `PSF_Conditions`
- [SpherePacking.CohnElkies.Prereqs:L117](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/CohnElkies/Prereqs.lean#L117) — `PSF_L`
- [SpherePacking.CohnElkies.Prereqs:L133](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/CohnElkies/Prereqs.lean#L133) — `SchwartzMap.PoissonSummation_Lattices`
- [SpherePacking.ForMathlib.InvPowSummability:L270](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/ForMathlib/InvPowSummability.lean#L270) — `Summable_Inverse_Powers_of_Finite_Orbits`
- [SpherePacking.MagicFunction.PolyFourierCoeffBound:L631](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L631) — `MagicFunction.PolyFourierCoeffBound.norm_φ₀_le`
- [SpherePacking.MagicFunction.PolyFourierCoeffBound:L633](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L633) — `MagicFunction.PolyFourierCoeffBound.norm_φ₀_le`
- [SpherePacking.MagicFunction.a.Eigenfunction:L45](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/MagicFunction/a/Eigenfunction.lean#L45) — `MagicFunction.a.Fourier.perm_I₁_I₂`
- [SpherePacking.MagicFunction.a.Eigenfunction:L47](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/MagicFunction/a/Eigenfunction.lean#L47) — `MagicFunction.a.Fourier.perm_I₅`
- [SpherePacking.MagicFunction.a.Integrability.Integrability:L35](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/MagicFunction/a/Integrability/Integrability.lean#L35) — `MagicFunction.a.Integrability.Φ₁_integrableOn`
- [SpherePacking.MagicFunction.a.Integrability.Integrability:L40](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/MagicFunction/a/Integrability/Integrability.lean#L40) — `MagicFunction.a.Integrability.Φ₂_integrableOn`
- … and 46 more

### `axiom`: 2 hits in 1 file

- [SpherePacking.Tactic.Test.TendstoCont:L343](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/Tactic/Test/TendstoCont.lean#L343) — `opaqueF`
- [SpherePacking.Tactic.Test.TendstoCont:L344](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/Tactic/Test/TendstoCont.lean#L344) — `opaqueF_tendsto`

### `decide +kernel`: 2 hits in 1 file

- [SpherePacking.Basic.E8:L340](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/Basic/E8.lean#L340) — `E8Inverse_mul_E8Matrix_rat`
- [SpherePacking.Basic.E8:L455](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/Basic/E8.lean#L455) — `E8Matrix_mul_E8Matrix_transpose_rat`

## Duplication & Directory Alignment

- **Directory-vs-namespace outliers:** 6 files (8.2%; 0 high, 6 medium)
- **Identical-body file clones:** 0 clusters
- **Identical-signature file clusters:** 0 clusters
- **Import-only shims:** 0

## Most-Imported Modules (Top 10)

| Module | Direct Importers | Transitive Importers | Lines | Declarations |
| --- | ---: | ---: | ---: | ---: |
| [SpherePacking.MagicFunction.a.Basic](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/MagicFunction/a/Basic.lean#L1) | 8 | 15 | 401 | 61 |
| [SpherePacking.MagicFunction.PolyFourierCoeffBound](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L1) | 7 | 11 | 639 | 36 |
| [SpherePacking.ModularForms.Eisenstein](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/ModularForms/Eisenstein.lean#L1) | 6 | 35 | 301 | 26 |
| [SpherePacking.Basic.PeriodicPacking](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/Basic/PeriodicPacking.lean#L1) | 5 | 6 | 1,225 | 64 |
| [SpherePacking.Tactic.TendstoCont](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/Tactic/TendstoCont.lean#L1) | 5 | 32 | 450 | 1 |
| [SpherePacking.MagicFunction.IntegralParametrisations](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/MagicFunction/IntegralParametrisations.lean#L1) | 5 | 21 | 216 | 55 |
| [SpherePacking.ModularForms.DimensionFormulas](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/ModularForms/DimensionFormulas.lean#L1) | 5 | 32 | 61 | 4 |
| [SpherePacking.ModularForms.JacobiTheta.Basic](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/ModularForms/JacobiTheta/Basic.lean#L1) | 4 | 29 | 847 | 62 |
| [SpherePacking.ModularForms.FG](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/ModularForms/FG.lean#L1) | 4 | 24 | 548 | 71 |
| [SpherePacking.ModularForms.ResToImagAxis](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/e07215872319dcadd7ced28670ae4daa13b74b8d/SpherePacking/ModularForms/ResToImagAxis.lean#L1) | 4 | 37 | 541 | 55 |
