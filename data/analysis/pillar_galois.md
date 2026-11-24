# Pillar B Audit: Galois Representations & `Row0b` Engine (`galoisLocalGlobalStrong_recParameter`)

> **Target:** Pillar B (`galoisLocalGlobalStrong_recParameter`, `95,102` decls) and `recTExists` (`595` decls) at `40e56bab` (`kernel.db` `ALL` `tree_id=0`, `1,468,414` live decls); companion JSON `outputs/decomp/pillar_galois.json` (`323` nodes, `1,163` edges, `9` Horn rules, `7` claims, `18` `OPAQUE` deep nodes) `[L]`.
> **Kernel check:** `0` `sorryAx`, `0` custom axioms, `3` Mathlib `.wrapped.*` `opaque` terms, `10` benign `of_decide_eq_true` pattern hits (see [Scope & Tag Legend](README.md)).

---

## Executive Summary

- **Scale & Kernel Position [L][M]:** `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`) spans `95,102` exclusively dominated declarations (`6.48%` of `1,468,414` live decls): `78,553` `thm`, `16,012` `def`, `534` `inductive`, `3` Mathlib `.wrapped.*` `opaque` terms, `0` custom `axiom`s, `0` `sorryAx`/`ofReduceBool`, and only `10` benign `of_decide_eq_true _ _ (Eq.refl Bool true)` pattern hits (`4` in Mathlib simplicial homology, `6` in `GlobalTheory.EtC`/charpoly helpers). Its immediate dominator is `UpperTheory.FinalTheorems.everyCharacter` (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:10`).
- **Role in the Global Proof [L]:** `UpperTheory.FinalTheorems.everyCharacter_of_row` (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7`) takes a single `h : UpperTheory.GalStar.Row0b (fun h rc => UpperTheory.Zero.LLC.IsRecT h rc)` proof, packs it twice into `OpenLiteratureStatements` (`caraianiLocalGlobalDual` and `galoisRepOfPolarizedPairLit`) alongside `UpperTheory.Zero.LLC.recTExists` (`595` decls, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20`), feeds `h` into `UpperTheory.One.vwin_of_row` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`), and calls `every_character_of_literature_of_vWin`. Pillar B is the **only non-shared engine** supplying `Row0b`.
- **Two Major Architecture Findings [L][C]:**
  1. **Genuine Cohomology & Theta-Lift Descent (No Empty Axiomatic Coercion):** Contrary to misleading folder/module names like `EtaleAxioms`, `GlobalTheory.EtC` (`src/Development/AbelianVarietyTheory/Definitions/Divisors/GalMapMul.lean:82`, `PullHlComp.lean:239`) builds genuine $l$-adic étale cohomology `HQ` over Mathlib's `Scheme.etaleTopology` via injective resolutions of cyclotomic Tate-twist sheaves, and theorems like `UpperTheory.Et.e4` (`3,899` decls), `GlobalTheory.EtC.b6pic_holds`, and `UpperTheory.etaleCohomology_functorialityAxioms_hold` genuinely prove scheme cohomology properties. Pillar B builds odd-rank Galois representations in Hecke eigenspaces (`UpperTheory.Gal.Int.Geo.piece`) of Harris–Taylor unitary Shimura towers, then handles **even ranks** by lifting twice to distinct odd ranks via explicit definite-unitary theta lifts (`UpperTheory.TP.K.tLiftK`, `4,104` decls) and subtracting split character lines (`SplitLineSubtraction`).
  2. **Intentional Contract Weakenings + `junkEx` Fallback in `recTExists`:**
     - **`Row0b` / `AwayB` weakenings [L][C]:** Compared with textbook local-global compatibility, `Row0b` weakens `Row0` via `Row0.row0b` in two explicit ways: (a) `IsQpBig` (`WeightsConjBis.lean:15`) drops small residue primes $g \le 16 a^2$ when $a > 1$; (b) for non-toral places (`TmW ∧ Sqf ∧ mono0`), `AwayB.tame0` (`WeightsConjBis.lean:29`) equates characteristic polynomials **only on inertia** (`deg g = 0`) plus monodromy vanishing `mono0` (whereas full Weil–Deligne equality `x = y`, including Frobenius, holds under `Tor y ∧ y.mono0`).
     - **`recTExists` (`595` decls) is a genuine depth-zero/LCFT map + dummy fallback `junkEx` [L][C]:** `LawsT` (`IsRecTOfIsRec.lean:55`) omits $\varepsilon$-factors, omits global surjectivity, and restricts twist, central-character, duality, depth-0, and injectivity laws to `Good` (`GoodCusp` cuspidals: rank $1$, or twists of depth-zero cuspidals over $\mathbb{Q}_g$) plus `TypeLaw`. For rank $\ge 2$ outside `GoodCusp`, `UpperTheory.Zero.LLC.junkEx` (`JunkEx.lean:257`) returns a fixed wildly ramified placeholder `J n` (`¬ IsTameWD`) normalized in determinant so `LawsT` is trivially preserved without colliding with `Good` injectivity. In particular, `UpperTheory.Gal.Int.Row.mixed_of_tame` (`CharPolOfInert.lean:151`) proves by a finite-set counting / `TypeLaw` pigeonhole (`dz_of_cusp`) that `TmW (rc x) ∧ Sqf (rc x) ∧ (rc x).mono0` forces all cuspidal constituents of `x` to have depth zero (`DZ`/`Good`), so `Row0b recT` never relies on the `junkEx` branch.

---

## 1. Exact Formal Contracts (`Row0b`, `RecNotion`, `recT`, `IsRecT`, `IrrGL`, `WD`, `IsPlaceOver`)

### 1.1 Ground Field, Automorphic, and Galois Objects [L]

Every contract below is read directly from its Lean source definition:

| Symbol | Exact Formal Definition & Ground Mathlib Types [L] | Source Anchor | Verdict |
|---|---|---|---|
| `Formalism.ConjugateSelfDual.G F Ω` | `Ω ≃ₐ[F] Ω` (absolute Galois group as field automorphisms over `F`) | `src/Formalism/ConjugateSelfDual/Statement.lean:6` | Real [L] |
| `Formalism.ConjugateSelfDual.Qbar l` | `PadicAlgCl l` (algebraic closure of $\mathbb{Q}_l$) | `src/Formalism/ConjugateSelfDual/Statement.lean:8` | Real [L] |
| `Formalism.ConjugateSelfDual.IsPlaceOver A v` | `∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal` for valuation subring `A : ValuationSubring Ω` and prime ideal `v : HeightOneSpectrum (𝓞 F)` | `src/Formalism/ConjugateSelfDual/Statement.lean:20` | Real [L] |
| `GlobalTheory.PRep.IsSmooth ρ` | `∀ v : V, IsOpen {g : G | ρ g v = v}` (locally constant / open stabilizer smooth representation) | `src/Development/AbelianVarietyTheory/Definitions/Foundations/SmoothPartStable.lean:73` | Real [L] |
| `GlobalTheory.SmGL.IrrCl G` | `Quotient (IrrRep.setoid G)` where `IrrRep G` bundles `(V, AddCommGroup, Module ℂ, ρ, IsSmooth ρ, ρ.IsIrreducible)` modulo `Nonempty (σ.ρ.Equiv τ.ρ)` | `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NontrivialOfIrreducible.lean:163,183` | Real [L] |
| `GlobalTheory.LocGL.IrrGL k` | `Σ n : ℕ, IrrCl (GL (Fin n) k)` (disjoint union of isomorphism classes of smooth irreducible complex representations of $GL_n(k)$ over all $n \ge 0$) | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NonemptyEquivMultiProdOne.lean:179` | Real [L] |
| `GlobalTheory.SmGL.IsCuspidal π` | `IsSmooth π ∧ ∀ s d e, unipRad k e ≠ ⊥ → Subsingleton (Jacquet π (unipRad k e))` (all proper parabolic Jacquet modules vanish) | `src/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean:401` | Real [L] |
| `GlobalTheory.LocGL.HasSupport π s` / `IsL 𝔪 π` | Cuspidal support multiset `s : Multiset (IrrGL k)` via `IsCuspSupport` (`multiProd` subquotient), and Zelevinsky/Langlands quotient `IsCosocle π (prodIrr x hd)` over ordered `Segment k`s | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NonemptyEquivMultiProdOne.lean:352,555` | Real [L] |
| `GlobalTheory.GalOfCusp.algNorm σ` | `(IrrGL.of σ.ρ σ.smooth σ.irred).nu (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)` (unitary/Tate-shift twist $\lvert\det\rvert^{(1-a)/2}$ for C-algebraic normalization) | `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GaloisRepOfPolarizedCuspidal.lean:24` | Real [L] |
| `GlobalTheory.WeilDeligne.WDRep h V` | Finite-dim $\mathbb{C}$-vector space `V` with `ρ : Representation ℂ (Weil h) V`, `N : End ℂ V`, `IsSmooth ρ`, `∀ σ, End.IsSemisimple (ρ σ)` (Frobenius-semisimple), `IsNilpotent N`, and `ρ σ * N = q_w ^ (deg σ) • (N * ρ σ)` | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean:36` | Real [L] |
| `GlobalTheory.WeilDeligne.WD h` | `Quotient (isoSetoid h)` (isomorphism classes of finite-dimensional Frobenius-semisimple Weil–Deligne representations over `ℂ`) | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean:380` | Real [L] |
| `GlobalTheory.WeilDeligne.IsWDOf ι r x` / `wdOf` | `∃ tame l-adic character t, φ with deg φ = 1, nilpotent N` with open inertia $U \le I_w$ where $r(\sigma) = \exp(t(\sigma) N)$, and Frobenius-semisimplification yields `x`; `wdOf` chooses such `x` if one exists (`H.choose`), else trivial diagonal `WDRep` | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/WeilDeligneParamMonodromyEqZeroIff.lean:78,345,352` | Real [L] |
| `GlobalTheory.CuspRep.CuspSub E a` | Submodule `V ≤ Sm E a` of smooth adelic/archimedean functions satisfying `IsAutForm` (left $GL_a(E)$-invariant, open compact level, $K_\infty$-finite, $\mathcal{Z}(\mathfrak{g})$-finite, moderate growth), `IsCuspidal` (vanishing constant terms along rational unipotent radicals), `IsStable` under group/Lie operators, `V ≠ ⊥`, irreducible | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExpoConjOfIsCsd.lean:48,92,209` | Real [L] |
| `GlobalTheory.CuspRep.CG.IsRegAlg π` | Existence of `InfinityType E a` with `(p.1 - p.2 ∈ ℤ)` algebraic integrality, `IsRegular` (distinct weights), and conjugate symmetry matching `π.infChar τ` for all $\tau : E \hookrightarrow \mathbb{C}$ | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExpoConjOfIsCsd.lean:591`; `src/Development/AutomorphicArithmetic/IntegralCasts/AlgebraicInfinityType/InfinityType.lean:8,31` | Real [L] |
| `GlobalTheory.ContraPair.PolarizedPair π χ` | For Hecke character `χ : HChar (maximalRealSubfield E)` (`Continuous ∧ trivial on Lˣ`), infinite sign condition `χ_v(-1) = (-1)^a` plus `DualIsConjBy π (compNorm E χ)` ($\pi^\vee \otimes (\chi \circ N_{E/F}) \cong \pi^c$) | `src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DualIsConjByOne.lean:53`; `src/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean:12,19` | Real [L] |
| `Formalism.MainNotions.N.IsSSRep ρ` | `∀ W, IsInv ρ W → ∃ W', IsInv ρ W' ∧ IsCompl W W'` (complete reducibility / semisimplicity) | `src/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:1186` | Real [L] |

### 1.2 `RecNotion`, `recT`, and `IsRecT` [L]

- **`UpperTheory.GalStar.RecNotion`** (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjAlt.lean:16`):  
  `∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), (IrrGL (w.adicCompletion E) → WD h) → Prop`  
  That is, a predicate classifying what counts as a valid local Langlands correspondence map $\mathrm{Irr}(\mathrm{GL}_*(E_w)) \to \mathrm{WD}(W_{E_w})$ at every place extension $(A, w)$.
- **`UpperTheory.Gal.Int.recT`** (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean:18`):  
  `fun h rc => UpperTheory.Zero.LLC.IsRecT h rc`, where **`UpperTheory.Zero.LLC.IsRecT`** (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:74`) asserts `∃ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), LawsT a ha rc`. (See §3.2 for exact breakdown of `LawsT` vs classical LLC.)

### 1.3 Quantifiers and Every Field of `Row0b`, `PropsB`, `AboveB`, `AwayB` [L]

**`UpperTheory.GalStar.Row0b (Rc : RecNotion) : Prop`** (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69`):

- **Universal Quantifiers:**
  - Any types `(E Ω : Type)` with `[Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]`.
  - Any prime `l : ℕ` (`[Fact l.Prime]`) and field isomorphism `ι : Qbar l ≃+* ℂ` (`PadicAlgCl l ≃+* ℂ`).
  - Any rank `a : ℕ` with `1 ≤ a`, cuspidal automorphic subrepresentation `π : CuspSub E a`, and totally real Hecke character `χ : HChar (maximalRealSubfield E)` satisfying `(CG.mk π).IsRegAlg` and `PolarizedPair π χ`.
- **Existential Conclusion:**
  - There exist a Galois homomorphism `r : G E Ω →* GL (Fin a) (Qbar l)`, an integer weight shift `wt : ℤ`, and a Hodge–Tate multiset map `HT : (E →+* Qbar l) → Multiset ℤ` satisfying `PropsB Rc π ι r wt HT`.

**`UpperTheory.GalStar.PropsB`** (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:54`) — 6 fields:

1. `.cont : Continuous r` (continuous for the Krull topology on `Ω ≃ₐ[E] Ω` and `PadicAlgCl l` topology).
2. `.ss : IsSSRep r` (`r` is completely reducible).
3. `.away : ∀ w (hl : l ∉ w.asIdeal) A (h : IsPlaceOver A w) rc, Rc h rc → ∀ σ, π.IsLocComp w σ → AwayB (wdOf h hl ι r) (rc (algNorm σ))`.
4. `.weights : ∀ τ : E →+* Qbar l, (HT τ).map Int.cast = ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z => (a - 1) / 2 - z)` (links `HT τ` to the Clozel-shifted archimedean infinitesimal character of `π` via `ι`).
5. `.weights_conj : ∀ τ : E →+* Qbar l, HT (τ.comp complexConj) = (HT τ).map (wt - ·)` (conjugate-self-dual shift symmetry of Hodge–Tate weights).
6. `.above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveB Rc π ι r HT P h Bw hj` (the local bridge `Bw` embeds `E` densely into `Kw : FinExt l` over `ℚ_[l]`, restricting to places `w | l`).

**`UpperTheory.GalStar.AboveB`** (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:39`) — 2 fields (for $r|_{\mathrm{Dec}(A)}$ via `LocPrime`/`LocTied`/`LocBridge` period-ring realizations, proved unconditionally nonempty by Shared-Diamond theorems `GlobalTheory.MemLoc.exists_locPrime_tied` (`163` decls, `ExistsLocalPrimeAinf.lean:281`) and `GlobalTheory.PlaceBridge.exists_locBridge` (`FiniteDimensionalAdjoinRange.lean:303`)):

1. `.crys`: For any local component `σ` of `π` at `w`, if `SmGL.IsSpherical σ.ρ`, then `IsCrysAt P Bw (r|_{Dec A})`, `IsdRAt P Bw (r|_{Dec A})`, and `∀ τ, IsJumpsAt P Bw (r|_{Dec A}) τ (HT τ)`.
2. `.nice`: For any local component `σ` of `π` at `w`, any `rc` with `Rc h rc`, if `(rc (algNorm σ)).mono0` ($N = 0$) and **`((IsQpBig w a ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ)))`**, then `IsdRAt`, `IsPstAt`, `IsJumpsAt`, and `AwayB (wdAt P ι Bw h hj (r|_{Dec A})) (rc (algNorm σ))`.

**`UpperTheory.GalStar.AwayB x y`** (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:26`) — 3 fields comparing two `WD h` parameters `x` (Galois side) and `y := rc (algNorm σ)` (automorphic side):

1. `.dim : x.lpDim = y.lpDim`.
2. `.tor : Tor y → y.mono0 → x = y`, where `Tor y` (`WeightsConjAlt.lean:27`) means `∀ s t : Weil h, LocalGlobalAboveLAlt.Triv y ⁅s, t⁆`, i.e., $y|_{[W,W]}$ acts with characteristic polynomial `(X - 1)^dim` (`LocalGlobalOfIwahori.lean:21`, abelian Weil image) and $N = 0$ (`y.mono0`). **Under `Tor ∧ mono0`, full `WD` equality `x = y` (including Frobenius eigenvalues!) is asserted [L].**
3. `.tame0 : IsQpBig w y.lpDim → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g : Weil h, deg g = 0 → x.charPol g = y.charPol g`, where:
   - `IsQpBig w n` (`WeightsConjBis.lean:15`): `∃ g [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i ∧ (n = 1 ∨ 16 * n^2 < g)` (weakened from `Row0`'s `IsQp w` at `WeightsConjAlt.lean:20`, which omits the $g > 16 n^2$ bound).
   - `TmW y` (`WeightsConj.lean:18`): `∀ σ : G E Ω, wildInertiaValuationCondition → y.inePol σ = (X - 1) ^ y.lpDim` (trivial on wild inertia).
   - `Sqf y` (`WeightsConjAlt.lean:29`): for any topological tame generator `γ ∈ Ine A`, any root $z \in \mathbb{C}$ of `y.inePol γ` with multiplicity $\ge 2$ satisfies $z^{q_w - 1} = 1$.
   - **Critical Relaxation [L][C]:** Under `tame0`, Pillar B only proves `x.mono0` and equality of characteristic polynomials **on inertia (`deg g = 0`)** — it does **NOT** assert equality of Frobenius characteristic polynomials (`deg g = 1`) for non-toral $n \ge 2$ supercuspidals! (This originates from `LocalGlobalCompatAtIwahoriFixedPlaces` in `LocalGlobalCompatAtIwahoriFixedPlaces.lean:24-32`, which likewise outputs `inePol`/`charPol (ineIncl h t)` only.)

---

## 2. How Pillar B Constructs `Row0b recT` (Dominator Spine Walkthrough)

```
steps_holds (54,486)  ──▶  geometric_realization_of_weight_one (79,447)  ──▶  geoOne_holds (82,643) [Odd rank a, GeoOne]
                             ▲                                                    │
   [kodaira_spencer_of_weight_one (18,918), Pl.planEx_holds (3,253),             ▼
    classNumberFinite_holds (632), weight_one_geometric_realization (2,953)]      galoisLocalGlobalStrong_of_geometry_lift (8,091)
                                                                                  ├── Div.seedFinOdd_of_geoOne (908)
   tLiftK (4,104)  ──────────────────────────────────────────────────────────────▶├── Cong.congFinOdd_of_ex (644)
     [siegelWeilStd_k (2,573), weilEx_k (505), tLift_of_tools_k (799)]            ├── coreAll_of (2,694) [Even ranks via 2-lift + subtraction]
                                                                                  └── rest (3,061) ──▶ Row0 recT ──▶ Row0.row0b ──▶ Row0b recT
```

### 2.1 Complete Dominator Breakdown (`>= 500` decls down to depth `12` in `ALL`) [L]

1. **Stage A — `UpperTheory.Gal.Int.Geo.steps_holds` (`54,486` decls, `GeometricRealizationOfWeightOne.lean:20`, `StepsMain.lean:17`):**
   - Proves `Steps` (`MapInvMul.lean:19`), a 17-field package for an arbitrary smooth projective correspondence tower `H : HTower k` (`IdTower.lean:9`: scheme `Z / k` with finite étale correspondences `s, t : Y g ⟶ Z`) and Hecke character `θ : H.Γ → Qbar l`.
   - `RepEx` (`HodgeTrAt.lean:103`) realizes a continuous semisimple Galois representation `ρ` on the **Hecke eigenspace** `piece l H Ω L θ := ⨅ g, Module.End.eigenspace (hop g) (θ g)` inside $l$-adic étale cohomology `Htot l (sch.obj (H.geomZ Ω))` (`IsGrRefl.lean:54`), passing to Jordan–Hölder semisimplification (`IsGr`, `:66`, `RepMain.lean`).
   - Direct dominator children `>= 500` decls (`steps/198/output.txt` [L]):
     - `UpperTheory.Gal.Int.Geo.jumpStep_holds` (`6,094` decls): proves crystalline Hodge–Tate jump occurrence (`JumpStep`) via `htSpecGood` (`5,562`, `ClosedHT.lean:21`), `htBij` (`4,293`, Hodge surjectivity `CrystallineSemistableComparison.Onto.htBij_of` `2,294` → `parts` `2,108`), `hodgeTate_comparison_smooth_projective` (`1,046` → `hodgeTate_of_etale_side` `1,045` → `ht_of` `866`), `hodge_iso_natural_cech` (`855` → `glob_iso_c` `621` → `glob_iso` `620`), and `diagEt3_holds` (`512` → `diagEt3` `511`).
     - `UpperTheory.Et.e4` (`3,899` decls, `E4.lean:5`) → `UpperTheory.Et.EtaleTopology.top` (`3,897` decls, `EtaleTopology.lean:133`): proves étale cohomology properties of curves (`EtaleChapterEFour`: Selmer/Picard descent, Kummer sequence, spreading-out, Galois descent).
     - `UpperTheory.Gal.KunnethLefschetz.Core.inputs` (`3,827` decls, `EtSideGood.lean:38`): Künneth/diagonal/purity package including `UpperTheory.Et.purGysin` (`3,075` → `purAll` `3,036` → `intersectionNumber_baseChange` `853` → `etale_thom_isomorphism_of_thom_isomorphism` `852`).
     - `GlobalTheory.EtC.projectiveBundleFormula_vectorBundle_any_space` (`3,032` decls, axiom `D1`): via `pbf_disc` (`2,076` → `UpperTheory.Cb.etaleCohomology_projectiveBundle_formula` `1,710` → `pbf_all` `1,699`) and `pbf_of_disc` (`944` → `pbf_of_model` `776` → `GlobalTheory.EZ.ez` `514`).
     - `UpperTheory.Gal.Seam.crysStep_holds` (`2,227` decls, `Closed.lean:9`) → `crysStep_of` (`2,218`) → `matIn_holds` (`2,180`) → `vFin_holds` (`2,176`) → `etale_finiteness_of_duality` (`2,133`) → `etale_duality_trace_isomorphism` (`2,131`, `D2`).
     - `UpperTheory.Et.E2.main` (`1,841` decls, → `towers` `828`): smooth/proper local base change (`E2`) for strictly Henselian local rings.
     - `UpperTheory.Ru.crystallineComparison.phiStep` (`1,516` decls → `finAll` `1,001` → `finAll_of` `943` → `final` `941` → `top` `621`): crystalline Frobenius characteristic-polynomial / congruence propagation (`SmoothModelCrystalline.lean:13`).
     - `UpperTheory.Et.E3.main` (`1,455` decls → `n8` `1,233`): smooth base change to fraction field (`E3`).
     - `GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover` (`1,436` decls → `tateTwistCohomology_genericFibre_henselLine_subsingleton` `1,435` → `picL` `1,228` → `pic_generic_fibre_quotient_strictHenselisation_no_torsion` `1,226` → `pic_localization_strictHenselisation_no_torsion` `1,208`).
     - `CrystallineSemistableComparison.B.local_of` (`1,206` decls), `Pb.powK_ne_zero` (`1,015` → `powK_ne_zero_main` `1,014` → `powK_ne_zero_of` `602`), `UpperTheory.Et.affine_proper_base_change` (`836`, `E1`), `Pb.pSeam` (`827` → `pmap` `719` → `crystalline_deRham_firstChern_exists` `614` → `rhoSys_ex'` `583` → `rhoSys_ex` `582`), `D.out` (`737` → `out_of_rin` `646`), `etC_c2` (`637`, affine curve cohomological dimension `C2`), `Pb.LsG.ls_seq` (`631`), `KunnethLefschetz.steps_holds` (`628`), `laurentPolynomial_cohomology_strictlyHenselian_vanishing` (`561`, `C5` → `gm_cohomology_strictlyHenselian` `559` → `laurent_cohomology` `558`).

2. **Stage B — `geometric_realization_of_weight_one` (`79,447` decls) & `geoOne_holds` (`82,643` decls):**
   - **`weight_one_geometric_realization`** (`2,953` decls, `WeightOneGeometricRealization.lean:7`) proves `HolomorphicLefschetzFormula` (`HodgeTraceFromLefschetzAndGroupSide.lean:102`) via `UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence` (`2,951` → `block_fixed` `2,861` → `holomorphic_lefschetz_finiteEtale_correspondence` `2,832` → `holomorphic_lefschetz_finiteEtale_integral` `2,809` → `exists_chart_lift_of_finite_cover` `2,025`).
   - **`kodaira_spencer_of_weight_one`** (`18,918` decls) proves `KSAll` (`PackExOf.lean:93`):
     - `GlobalTheory.UPel.HT.model_nonempty` (`3,741` decls, `HarrisTaylorIntegralModelNonempty.lean:11`) constructs integral models for PEL Harris–Taylor unitary Shimura data `GlobalTheory.UPel.HT.Datum` (`NotCompactOfMEqOne.lean:13`, real division-algebra PEL tuple with symplectic form, polarization, split at $p$) via `exists_repFam_qproj` (`2,901` → `sdRep_of_coprime` `1,372`, `actRep_finite_unramified` `814`) and `smoothOfRelativeDimension` (`823` → `exists_univ_tangent` `631`).
     - `UpperTheory.Gal.LocalSmoothExtension.ksHodge_of_geo` (`3,206` decls, `KsHodgeOfGeo.lean:7`) compares holomorphic Lefschetz trace against definite unitary orbital counts (`weighted_count_definite_unitary` `1,287` → `complex_count_regular_marked_points` `720`, `ksHodge_of_inputs` `633`, `trace_definite_forms_identity` `631`).
     - `UpperTheory.Gal.FixZ.FixK_holds` (`2,616` decls → `tower_fixed_points_of_isogeny_data` `2,615` → `fixedPoints_int_base_holds` `2,376` → `GUnif_holds` `768` → `gUnif_of` `739` → `complexPoints_classify_markedPeriods` `591`).
     - `UpperTheory.Gal.Int.Geo.CovMain.mIn` (`1,285` decls → `congKS_link` `846`), `GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic` (`1,186` → `DeRham.charpoly_push_eq` `1,185` → `charpoly_push` `1,148` → `GlobalTheory.Dieu.theory` `661`), and `harrisTaylor_typeTj_isogenies_representable` (`783` → `isogeny_rep` `601` → `exists_finite_etale_trivializing_torsion_abelianScheme` `589`).
   - **`Pl.planEx_holds`** (`3,253` decls, `SpecTopHolds.lean:9`) builds CM definite unitary group setups (`exists_unitaryGroupDatum_of_vector_exponent_spectral` `829`) and prime-level Hecke scalar commutation (`specTop_holds` `1,554` → `specTopG` `1,505` → `specData` `1,316`).
   - **`GlobalTheory.classNumberFinite_holds`** (`632` decls, `ClassNumberFiniteHolds.lean:11`) proves finiteness of double cosets for closed $\mathbb{Q}$-group loci (`cf_of_isQGroup` `513`).
   - Combining these yields **`GeoOne`** (`HodgeTrAt.lean:79`): for **ODD rank $a$**, definite unitary representations `U` of elliptic type `TyEll` at $w_0 \mid l$ and lacunary weights `LacWtAt` at $v' \mid l$ admit $l$-adic cohomology representations `ρ` satisfying Eichler–Shimura `ESAt` away from $l$, `CrysAt ∧ JumpsOcc` at suitable $w \mid l$, and `PhiKilled` (crystalline Frobenius characteristic-polynomial divisibility).

3. **Stage C — `galoisLocalGlobalStrong_of_geometry_lift` (`8,091` decls, `Development.lean:30` → `galoisLocalGlobal_of_geometry_lift` `8,068`):**
   - **`Div.seedFinOdd_of_geoOne`** (`908` decls, `MainFin.lean:13`) via **`divAll_holds`** (`838` → `divOne_holds` `615` → `divSet_holds` `609` → `LateralTheory.DivDb.goal_holds` `554`): uses `DivAll` (`InsideRefl.lean:107`) to factor/divide out multiplicities from the higher-dimensional cohomological representation `ρ` of `GeoOne` (using lacunary Hodge–Tate weights and determinant/character divisibility) to extract a rank-`a` representation `r : G E Ω →* GL (Fin a) (Qbar l)` matching `FrobEig`, `CrysDRU`, and `PhiPol` for `Odd a`.
   - **`Cong.congFinOdd_of_ex`** (`644` decls, `CongFinOddOfLvLac.lean:15` → `congFinG_of_ex` `641` → `congFinG_of_step` `544`): converts lacunary weight existence into congruence conditions `CongFinOdd` on odd-rank definite unitary forms.
   - **`coreAll_of`** (`2,694` decls, `Development.lean:20`): takes `SeedFinOdd`, `CongFinOdd`, and **`tLiftK`**, runs `toCoreK` (`803` decls, `ToCoreK.lean:7`) and `TwoUpOK` (`TwoUpOKOfSteps.lean`) to extend from **ODD** ranks to **ALL** ranks (`n` even $\implies$ two lifts via `tLiftK` to odd ranks $n + t$, then `SplitLineSubtraction`), then applies `LimOddOfLimFinOdd` (`386` → `380` → `377` → `346`) and quadratic CM base-change descent (`CoreAllOfRowStarCore.lean`) to prove **`GlobalTheory.RoadU.CoreAll`** (`Ex .all ∧ ∀ c, SphericalLevelCondition .all c`).
   - **`rest`** (`3,061` decls, `Development.lean:24`): upgrades `CoreAll` into **`Row0 recT`** (`WeightsConjAlt.lean:85`) using `R1` (`galoisCompat_unlinkedSupport_of_spherical` `316` decls) and **`R2` (`localGlobalCompatAtIwahoriFixed_of_unlinked`, `2,437` decls)** → `toTor_holds` (`2,399`) → `suppBC_outright` (`2,097`, → `suppBC_holds` `1,825`, `TypeOfLblHolds.lean:141`), which uses base change along solvable/cyclic extensions + Shintani descent matching + `CharPolOfInert.mixed_of_tame` to handle toral (`Tor`) and tame-unlinked (`TmW ∧ Sqf`) Iwahori-fixed local components.
   - Finally, **`galoisRepresentations_of_thetaLift`** (`90,962` decls, `GaloisRepresentationsOfThetaLift.lean:6`) weakens `Row0 recT` to `Row0b recT` via `Row0.row0b`, and **`galoisLocalGlobalStrong_recParameter`** (`95,102` decls, `RowSrc.lean:6`) supplies `UpperTheory.TP.K.tLiftK`.

4. **Shared-Diamond Dependencies Consumed (`kernel.db` cross-pillar edges) [L]:**
   - `UpperTheory.Gal.Int.Inp.inp_holds` (`13` decls inside Pillar B, `InputsOf.lean:20`) simply bundles `11` classical/shared inputs whose proof trees lie outside Pillar B's dominator subtree (shared across Pillars A/B/C/D): e.g. `GlobalTheory.deRham_potentiallySemistable` (`2,251` decls), `PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible` (`1,256`), `GlobalTheory.automorphicFormsFiniteGL` (`1,078`), `UpperTheory.Zero.LLC.recTExists` (`595`), `GlobalTheory.MemLoc.exists_locPrime_tied` (`163`), `HodgeLocalDeRhamField.HLdR.field_outright` (`879`), `PositivityTheory.SiegelWeilFormula.Fin.whitGenEq` (`745`), `PositivityTheory.Rg.Sw.HSt.holLeadB` (`870`), `UpperTheory.ConvolutionTheory.GM.gm_of_bcfl` (`1,946`).

---

## 3. What `tLiftK` (`4,104` decls) and `recTExists` (`595` decls) Actually Build

### 3.1 `UpperTheory.TP.K.tLiftK` (`4,104` decls) — Definite Unitary Theta Lift Engine [L]

- **Formal Statement (`TLiftK`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/HalfIndexLattices/TLiftK.lean:12`, proved at `TLiftK.lean:4`):** For any CM extension $E/F$ satisfying `W.GoodK` (`SplitStab.lean:18`: CM, `HasK E`, unramified $\mathcal{O}_E/\mathcal{O}_F$, standard $\psi$, odd-prime inertness $>3$), any definite Hermitian space $X$ (`J = 1`, signature $(n, 0)$), and any definite skew-Hermitian space $W$ (`J = δ • 1`, signature $(d, 0)$) with $d \ge d_0$, given algebraic Hecke characters $\chi_X, \chi_W$ of bounded weights $d + m_W(w) \le 2 \lambda_w(k)$ and an automorphic subrepresentation $U$ of $U(X)$ of highest weight `λ`, **`tLiftK` produces a non-zero theta-lift automorphic representation $U'$ of $U(W)$ (`IsLift`, `SchurStep.lean:106`)**:
  1. `aut : IsAutRepU U'`.
  2. `wt` (`IsLiftWt`, `SchurStep.lean:103`): explicit archimedean lowest-weight Howe-duality correspondence $2 \lambda'_k = (\text{if } k < n \text{ then } 2 \lambda_k - d - m_W \text{ else } 0) + n + m_X$.
  3. `loc`: at every finite split place $v$, the split local components $(\tau, \tau')$ of $(U, U')$ satisfy `LocPair t χX χW τ τ'`.
- **Internal Proof Pipeline (`TPGHolds.lean:39,58`, `TPGTop.lean:46`) [L]:**
  - **`PositivityTheory.ThKW.S.weilEx_k`** (`505` decls, `WpSTop.lean:45`): constructs global adelic Weil representations `IsWeil` for definite unitary dual pairs $(U(X), U(W))$.
  - **`PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_k`** (`2,573` decls, `SiegelWeilFinFinal.lean:15`, → `siegelWeilStd_of_ct_k` `1,786` → `siegelWeilStd_pre_k` `1,717` → `siegelWeilStd_mid_k` `1,137` → `siegelWeilStd_of_k` `907` plus `ctSplit_of_k` `642`): proves the convergent/regularized definite unitary Siegel–Weil formula (`SiegelWeilStd_k` in `BaseKnownTheoremsS.lean:13`) equating regularized theta integrals $\int_{U(A)(F)\backslash U(A)(\mathbb{A})} \theta(g) \, dg$ to Siegel Eisenstein values.
  - **`UpperTheory.TP.tLift_of_tools_k`** (`799` decls, `TPGTop.lean:46`) & `SchurStep`: applies Rallis inner product (via Siegel–Weil + doubling `IsDbl` + Schwartz–Bruhat bump functions & tail estimates) to prove non-vanishing of the definite theta lift, and `TwoUpOKOfSteps.lean` + `SubtractOf.lean` lifts an even-rank unitary form $U(n)$ twice to odd ranks $n + t$ ($t = 2(d_0+n)+1$) with distinct character twists so `SplitLineSubtraction` isolates the original rank-$n$ Galois representation.

### 3.2 `UpperTheory.Zero.LLC.recTExists` (`595` decls) — Partial LLC + `junkEx` Proxy [L][C]

`recTExists` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20`, dominated by `everyCharacter` with `fan_in = 25`) constructs `∃ rc, IsRecT h rc` at every place extension $(A, w)$ (`h : IsPlaceOver A w`) via:

1. **`artEx`** (`ArtEx.lean`): constructs the unique local Artin reciprocity map `a : Weil h →* E_wˣ` satisfying `IsLocalArtin h a` (normalization sending geometric/arithmetic Frobenius to uniformizer, continuous, open-kernel, norm-group surjectivity via global Artin reciprocity + Chevalley units).
2. **`cuspEx`** (`320` decls, `CuspEx.lean:168`): defines the cuspidal map `r x := if GoodCusp x then r₀ x else (J x.1).lpTw (e x)`:
   - **On `GoodCusp x` (`GoodMap`, `GoodMap.lean:144` → `goodMap`, `indEx`, `parEx`):** **Genuine Local Langlands**! Here `GoodCusp x` (`IsRecTOfIsRec.lean:20`) means either `x.1 = 1` ($GL_1$, handled via `lpOfChar (χ ∘ a)`) OR `E_w ≃+* ℚ_g ∧ x is a smooth-character twist of a depth-zero cuspidal` (`fixed y₀.rep (KOne _ _) ≠ ⊥`). Over $\mathbb{Q}_g$, `parEx` / `indEx` builds genuine tame Frobenius-induced $n$-dimensional Weil representations from unramified degree-$n$ extensions `Ext h g n` matching Deligne–Lusztig / Green regular characters (`IsRegularChar`) and central characters, proving `ParTw` and `ParDual`.
   - **On `¬ GoodCusp x` (`junkEx`, `JunkEx.lean:94,257`, `55` decls):** **Deliberate dummy proxy!** For rank $n \ge 2$ outside `GoodCusp` (higher depth $\ge 1$ or non-$\mathbb{Q}_g$ base fields), `junkData` constructs ONE fixed wildly ramified irreducible $n$-dimensional Weil representation `J n` (`IsTameWD V → J ≠ V.lpTwist ξ`, using wild ramification of degree-$n$ Artin/local extensions when $g \mid n$ or ramified $g$-power extensions, normalized to unitary Frobenius eigenvalues `‖det J(σ)‖ = 1`), twisted by an unramified `expo` character `e x` solely to satisfy `absCentral`. **Notice:** `cuspEx` is **NOT** injective on `¬ GoodCusp` cuspidals!
3. **`extDual` (`123` decls) & `extInj` (`82` decls) (`RecTExists.lean:20`):** Extends `r` from cuspidals to all `IrrGL (w.adicCompletion E)` via Zelevinsky multisegments (`IsL`, `segSum`, `LanglandsExhaustionGL`), proving the full weakened contract **`LawsT a ha rc`** (`IsRecTOfIsRec.lean:55`):
   - **Dropped relative to full classical LLC (`LocalLanglandsGL.lean`):** drops $\varepsilon$-factors (`eps`) and global surjectivity (`bij`).
   - **Guarded by `Good`:** `twist`, `central`, `dual`, `depth`, and `inj : ∀ x y, Good y → rc x = rc y → x = y` are ONLY asserted when the cuspidal support constituents are all `GoodCusp` (`Good`).
   - **Added (`TypeLaw`, `IsRecTOfIsRec.lean:35`):** explicitly links tame inflation of a cuspidal Green representation $\tau$ of $GL_n(\mathbb{F}_g)$ over $E_w \cong \mathbb{Q}_g$ to `mono0` and exact tame-inertia eigenvalues $\prod_{j=0}^{n-1}(X - \theta(z^{g^j}))$.
4. **Why `Row0b recT` Does NOT Cheat via `junkEx` [L]:** In `Row0b.away` (`AwayB.tame0`) and `AboveB.nice`, `recT` is only inspected under `(IsQpBig ∧ TmW y ∧ Sqf y ∧ y.mono0)` or `(Tor y ∧ y.mono0)` where `y = rc (algNorm σ)`:
   - Under `TmW y ∧ Sqf y ∧ y.mono0` (for `IsQpBig`, hence `IsQp`), **`UpperTheory.Gal.Int.Row.mixed_of_tame`** (`CharPolOfInert.lean:151`) first proves every cuspidal constituent $c$ of `algNorm σ` satisfies `IsTameWD (rc c)`, then applies **`dz_of_cusp`** (`:114`) — a finite cardinality/pigeonhole bijection on `Lab 𝓀[k] n` using `inj` restricted to `Good`! — to **prove** `DZ c` (`GoodCusp c`). In addition, `Sqf` forces rank $\ge 2$ constituents to be pairwise non-inertially equivalent (`Mixed`), and `plainTor_of_tor` (`:97`) shows `Tor y ∧ y.mono0` forces all cuspidal constituents to have rank `1` (`GoodCusp`). Thus **`junkEx` is provably unreachable** on every representation whose eigenvalues `Row0b recT` equates!

---

## 4. Fidelity Audit (Real Math vs Proxy Structures) & `OPAQUE` Inventory

### 4.1 Per-Component Fidelity Verdict [L][C][A]

| Component | Verdict | Evidence & Nuance |
|---|---|---|
| **`Row0b` / `PropsB` / `AboveB`** | **Real Galois Rep, Narrower Scope [L][C]** | Quantifies over all CM fields, primes $l$, and regular algebraic polarized cuspidal pairs $(\pi, \chi)$; produces genuine continuous semisimple $l$-adic `r : G E Ω →* GL_a(Qbar l)` matching Hodge–Tate jumps (`LocPrime`/`LocTied`/`LocBridge` unconditionally inhabited by `exists_locPrime_tied`/`exists_locBridge`), conjugate-duality, and crystalline/$p$-st properties. Narrower than classical C–S/Caraiani because `IsQpBig` excludes small residue primes $g \le 16 a^2$ when $a > 1$ and `tame0` excludes non-toral Frobenius eigenvalues. |
| **`AwayB`** | **Genuine Toral, Inertia-Only Tame [L][C]** | `.tor` gives full `WD` equality `x = y` (including Frobenius) when `[W,W]` acts trivially and $N=0$; `.tame0` equates only `mono0` and `charPol` on `deg g = 0` inertia elements for `IsQpBig ∧ TmW ∧ Sqf ∧ mono0`. Compare Alpöge's `remark.pdf` (`[A]`, Footnote 4): confirms only the local-global cases needed for the window/trace-formula argument are proved. |
| **`IrrGL`, `WD`, `IsPlaceOver`, `CuspSub`, `PolarizedPair`** | **Faithful Formalizations [L]** | Grounded directly in Mathlib topology, valuations, Hilbert/Haar/Fréchet-style smooth module definitions, `Weil` group with degree map, Frobenius-semisimple nilpotent monodromy commutation, and vanishing cuspidal constant terms. Zero degenerate or vacuous wrappers found. |
| **`IsRecT` / `recTExists`** | **Genuine Depth-Zero/LCFT + Explicit Proxy `junkEx` [L][C]** | Does **not** formalize full local Langlands for $GL_n$ (would require wild supercuspidals / Bushnell–Kutzko types / local Langlands over arbitrary finite extensions of $\mathbb{Q}_p$). Instead proves genuine $GL_1$ LCFT + depth-zero $\mathbb{Q}_g$ LLC (`GoodCusp`) and fills `¬ GoodCusp` rank $\ge 2$ with wildly-ramified dummy `junkEx`; mathematically safe because `mixed_of_tame` proves `TmW ∧ Sqf` never lands on `¬ GoodCusp`. |
| **`GlobalTheory.EtC` (`HQ`, `Et.e4`, `b6pic_holds`, `B2`)** | **Faithful Étale Cohomology [L]** | Despite misleading historical file names (`EtaleAxioms`), `Shv R` is Mathlib `Sheaf (Scheme.etaleTopology) ...` and `HQ l E n i` is genuine $\mathbb{Q}_l \otimes \varprojlim_k H^n_{\text{ét}}(E, \mu_{l^k}^{\otimes i})$ from injective resolutions (`GalMapMul.lean:82,125`, `PullHlComp.lean:239`), with scheme proofs like `EtaleCohomologyFunctorialityAxiomsHold.lean:61`, `EtaleTopology.lean:133`, and `EtaleDescentPicardGroup.lean:250`. |
| **`tLiftK` (`4,104` decls) & `Datum` (`HTower`)** | **Real Definite Theta Lifts & PEL Shimura Data [L]** | `UPel.HT.Datum` (`NotCompactOfMEqOne.lean:13`) encodes full division-algebra/CM PEL Shimura data; `tLiftK` proves `IsLift` between definite unitary $U(X)$ and $U(W)$ via proved `weilEx_k` and `siegelWeilStd_k` (`SiegelWeilStd_k`). |

### 4.2 Explicit `OPAQUE` Inventory [L]

All `323` nodes in `outputs/decomp/pillar_galois.json` have verified `kernel.db` identity, module, line anchor, and `<= 1`-line headers. `18` deep sub-theorems/predicates (plus `< 500`-decl leaves below depth `12`) are explicitly flagged **`OPAQUE`** because their internal proof bodies or inner definitions were **not** unfolded line-by-line to Mathlib ground types:

- **Geometric/p-adic-Hodge & Étale Internals:** `CrystallineSemistableComparison.D.out` (`737` decls, Witt exact sequences), `CrystallineSemistableComparison.Pb.powK_ne_zero` (`1,015` decls), `CrystallineSemistableComparison.Pb.pSeam` (`827` decls), `CrystallineSemistableComparison.Pb.LsG.ls_seq` (`631` decls), `UpperTheory.Et.E3.main` (`1,455` decls), `UpperTheory.Et.purGysin` (`3,075` decls), `UpperTheory.Gal.KunnethLefschetz.steps_holds` (`628` decls), `GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover` (`1,436` decls), `GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing` (`561` decls), `GlobalTheory.Pst.wdPst` (inner $D_{\mathrm{pst}} \to \mathrm{WD}$ construction inside `FiniteDimensionalWdSpace.lean`).
- **Shimura Model, Lefschetz & Divisor Subsystems:** `GlobalTheory.DeRham.charpoly_push_eq` (`1,185` decls) & `GlobalTheory.Dieu.theory` (`661` decls), `GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable` (`783` decls), `UpperTheory.Gal.W2.fixedPoints_int_base_holds` (`2,376` decls), `UpperTheory.Gal.FixZ.tower_fixed_points_of_isogeny_data` (`2,615` decls), `UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence` (`2,951` decls), `LateralTheory.DivDb.goal_holds` (`554` decls).
- **Siegel–Weil Constant-Term Internals:** `PositivityTheory.SiegelWeilFormula.Act.ctSplit_of_k` (`642` decls, internal constant-term splitting proof fed into `siegelWeilStd_of_ct_k`).

---

## 5. Reproduction & Verification Receipts [L]

- `python3 leanre/leanre.py decompile validate outputs/decomp/pillar_galois.json` → `OK` (`323` nodes, `1,163` edges, `9` Horn clauses, `7` claims, `18` `OPAQUE`).
