# Statement Closure, Trusted Computing Base, and Bridge Contracts

> **Target:** `5` headline roots (`Main.lean`, `Statements.lean`), `2,570`-def statement closure, `175,187`-file compiler sweep, and top bridge contracts (`40e56bab`, `solution.ndjson.zst` `5ea74b91…244e`, `challenge.ndjson.zst` `bd484ac9…b2b9`, `mathlib4@0df444a3`, `lean4@819816b2`, `batteries@4488d40d`) · **Blueprint:** `outputs/decomp/tcb_audit.json`
> **Kernel check:** `0` `sorryAx`, `0` custom axioms, `0` project defs in `riemannHypothesis`'s `2,448`-def cone; see [the analysis index](README.md) for scope and tags.

---

## 0. Summary of Checks

| Audit Axis | Verdict | Key Quantitative Evidence (`[L]`) |
|---|---|---|
| **1. Top-5 Headline Statements (`Main.lean` + `Statements.lean` vs `Challenge.lean`)** | **CLEAN (0 specification bugs)** | All 5 root `k1n` kernel signature hashes and decoded expression ASTs match `Challenge.lean` bit-for-bit; `challenge` (`51,692`) `\` `solution[stmt_mask!=0]` (`51,687`) `= {sorryAx, Nat.lor, Nat.xor, String.mk, String.mk._proof_1}`; `solution[stmt_mask!=0] \ challenge = ∅`. Every `1 / 2` is `@HDiv.hDiv ℝ`; `[NeZero N]`, `N = 1`, `s = 0`, `s = 1`, trivial zeros, and imprimitive Euler factors are all properly handled. Scope is strictly **zeta + Dirichlet $L$-functions** (no Dedekind/Hecke/Extended RH). |
| **2. `2,570`-Definition Statement Closure (`defcone_mask != 0`)** | **CLEAN (0 shadowing, 0 custom axioms)** | Only **4 project definitions** exist in the `2,570` cone (`src/Statements.lean:3-16`), and **0** in `riemannHypothesis`'s `2,448`-definition cone! Only **4 non-Mathlib/non-Lean-core library definitions** appear (`Batteries` `RatCast`, `RatCast.ratCast`, `Rat.cast`, `List.union`). Zero `Aesop`/`Qq`/`Plausible` defs in `defcone`, zero `sorryAx`, only `[Quot.sound, Classical.choice]` (`+ propext` in `stmt_mask`). |
| **3. Compiler, Flag & Environment Hygiene (`175,187`-file sweep)** | **CLEAN for Kernel Soundness** | `autoImplicit = false`, `relaxedAutoImplicit = false`. Across all `175,187` files: **`0`** `unsafe`, `implemented_by`, `extern`, `csimp`, `meta`, `no_index`, `skipKernelTC`, `debug.*`, `sorry`/`admit`, `axiom`, `opaque`, `native_decide`, or global `notation`. Exactly `2` elaborator-only `partial def`s (`CutCptCopy.lean:41`, `OwnStruct.lean:18`); `0` exported declarations have `attrs != 0`. `0` project instances enter the `51,687` statement cone. |
| **4. Bridge Contracts & `Formalism.Gchi` Division Guard** | **0 Soundness Holes; Unused Wrapper Definitions** | **`Formalism.Gchi` (`src/Formalism/StatementOC.lean:20`) is 100% DEAD CODE** (`0` kernel decls), alongside `plugAll`/`plugWin`, `GlobalTheory.Fc.Hyps`/`DRS`, and `SmallClassNumbers/*`! All **3 live** character observables (`Formalism.HC.An.gChi`, `GlobalTheoryTheory.gChi`, `Deduction.Gchi`) explicitly guard `if χ = 1`, `Level.Gm` erases `PChar.one`, `CharFamily.adm` enforces `N = 1 ∨ χ ≠ 1`, and `poleData.lean:230-232` discharges `χ ≠ 1` division via `differentiable_LFunction` + `LFunction_apply_one_ne_zero`. `OpenLiteratureStatements` (`195` module thms) is ignored by `152` wrappers and transitively used by only `13/195`. `Nonempty (HypsAlt ...)` refutes empty-family `𝒜 := fun _ => False` via `MinkDiv → ExS → DesignExists`. |
| **5. Mathlib `0df444a3` Spot-Check (`riemannZeta`, `completedRiemannZeta`, `LFunction`)** | **CLEAN & Validated by Known-Answer Theorems** | `riemannZeta := hurwitzZetaEven 0` via Jacobi-theta Mellin `WeakFEPair`; $\zeta(0) = -1/2$, trivial zeros at $-2(n+1)$, analytic on $\mathbb{C}\setminus\{1\}$, $\sum_{n\ge 0}(n+1)^{-s}$ on $\operatorname{Re}(s)>1$, AND Mathlib's finite pole convention satisfies $\zeta(1) = (\gamma - \log 4\pi)/2 \neq 0$ (`riemannZeta_one_ne_zero`), making `s ≠ 1` doubly safe. |

### 0.1 Security Distinction: Layer-2 TCB Soundness Bugs vs. Layer-3 Intermediate Abstraction Smells

A frequent confusion when auditing machine-checked mega-proofs is treating a weak, junk-valued, or trivially-inhabited *intermediate* definition as if it could let a false headline theorem slip past the Lean kernel. Under a sound kernel with standard classical axioms (`[propext, Quot.sound, Classical.choice]`, zero `sorryAx`, zero compiler-trust axioms), **modus ponens enforces strict conservation of mathematical difficulty** `[S, M]`:

1. **Why Intermediate Vacuity Cannot Rescue a False Root (`[S]`):** Suppose the headline root has kernel type $R$ (`Mathlib.RiemannHypothesis`) and the proof factors through an intermediate contract $I$ via two kernel-checked theorems $\vdash p_1 : I$ and $\vdash p_2 : I \to R$, combined as $\vdash p_2\,p_1 : R$.
   - If the author/AI accidentally or adversarially defines $I := \top$ (trivially inhabited, e.g., `UnusedSlot72 := True`), or defines an observable with Lean's total-function junk division $z / 0 = 0$, then proving $\vdash p_1 : I$ becomes trivial — **at the exact price that $\vdash p_2 : \top \to R$ must now construct a valid proof of $R$ from nothing!**
   - Conversely, if $I$ bundles overly strong or contradictory assumptions ($\bot$), then $\vdash p_2 : \bot \to R$ becomes trivial (`False.elim`), **at the exact price that $\vdash p_1 : \bot$ becomes impossible to discharge** unless the kernel or axiom base itself is inconsistent!
   - Even if two modules declare competing local `instance` structures, the Lean kernel's `app` rule checks that the argument's inferred type is *kernel-definitionally equal* (`is_def_eq`) to the function binder's domain before accepting $p_2\,p_1$.
2. **Where Fatal Layer-2 Bugs Actually Live (`[L, M]`):** A machine-checked proof can pass independent kernels while failing to establish the classical theorem **if and only if** a defect sits inside:
   - **(a) Root Specification (`Main.lean` / `Statements.lean`):** Missing hypotheses, wrong quantifiers (`N = 1` only, `IsPrimitive` where general was claimed), integer division `(1 : ℕ) / 2 = 0`, or unguarded pole/trivial-zero vacuity;
   - **(b) Definitional TCB Closure (`defcone_mask != 0`, `2,570` decls):** A shadowed or broken definition of `riemannZeta`, `Complex`, `Real`, or `DirichletCharacter.LFunction` inside the root types' transitive definition cone; or
   - **(c) Layer-1 Kernel / Exporter / Axiom Compromise:** A bug simultaneously affecting Lean `v4.36.0`, `leanchecker-paranoid`, Rust `nanoda`, `con-leche`, and `lean4lean`, or a hidden axiom/compiler-trust primitive (`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `@[implemented_by]`).
3. **Why Auditing Layer-3 Intermediate Contracts Still Matters (`[L, M]`):**
   - *CS/RE Analogy (`[M]`):* Layer-2 TCB auditing checks the **public syscall ABI and hardware root of trust**; Layer-3 bridge-contract auditing reverse-engineers **internal microservice RPC schemas and stripped symbol names**.
   - *Where this analogy breaks (`[M]`):* In a normal C/Rust binary, an internal integer-overflow or `0/0` bug corrupts runtime memory and violates the output guarantee; in a pure Lean proof term without `unsafe`/`implemented_by`, an internal junk value `0 / 0 = 0` **cannot** corrupt the root theorem's truth, because any downstream proof step that needs $(L'/L)(1,\chi)$ to match the Mellin residue of $L(s,\chi)$ is *forced by the kernel* to prove $L(1,\chi) \neq 0$ (`poleData.lean:232`)! Instead, Layer-3 contract smells reveal **narrative/architectural deception**: dead first-draft files still imported by `Main` (`Formalism.Gchi`), dummy hypothesis plumbing (`OpenLiteratureStatements` ignored by `152/195` lemmas), or theorem names (`zarhin`, `harishChandraFinite`) whose formal contract proves a narrower special case that suffices for the downstream consumer.

---

## 1. Top-5 Headline Theorems & `2,570`-Definition Closure Audit

### 1.1 Exact Signature, Kernel-AST & Edge-Case Audit of the 5 Roots

In `src/Main.lean:4-12` (SHA-256 `017645ca…60939`) and `src/Statements.lean:3-16` (SHA-256 `79ef7ca7…47bf`), all five headline theorems are declared at root namespace (`[L]`):

| Root # | Kernel Name (`src/Main.lean` line) | `decls.id` | Kernel `k1n` Signature Hash (`[L]`) | Type Target (`fan_out_type = 1`) | Proof Dispatch (`src/Main.lean`) |
|---:|---|---:|---|---|---|
| `0` | `riemannHypothesis` (`src/Main.lean:4`) | `1468389` | `k1n:e67d3cf7e6fa39c3480c359052fb059f` | `RiemannHypothesis` (Mathlib) | `rhOfAll` |
| `1` | `riemannZeta_eq_zero_re` (`src/Main.lean:6`) | `1468392` | `k1n:407e56a49b1c5d53ff3748d49d502ad6` | `RiemannZetaZerosOnLine` (`src/Statements.lean:3`) | `rhOfAll` |
| `2` | `LFunction_ne_zero_of_half_lt_re` (`src/Main.lean:8`) | `1468394` | `k1n:ec34cbcece5fefb9714a006dcd084651` | `DirichletLNonvanishingRightOfHalf` (`src/Statements.lean:6`) | `allChi` |
| `3` | `LFunction_eq_zero_re` (`src/Main.lean:10`) | `1468408` | `k1n:95410a953e15cc866bd26d64730dcb6d` | `DirichletLZerosOnLine` (`src/Statements.lean:10`) | `claimAll.2.1` |
| `4` | `LFunction_eq_zero_re_of_isPrimitive` (`src/Main.lean:12`) | `1468413` | `k1n:381487cab282c40612019f85727b984d` | `PrimitiveDirichletLZerosOnLine` (`src/Statements.lean:14`) | `critAll` |

Decoding the raw `lean4export` v3.1.0 expression DAGs in `data/challenge.ndjson.zst` against `outputs/kernel/kernel.db` (`data/solution.ndjson.zst`) confirms every coercion, instance, and boundary condition (`[L]`):

1. **Exact Challenge-vs-Solution Equivalence (`[L]`, cross-referencing Sutherland `[C]`):**
   - `con-leche-compare` (`con-leche-compare.log:57-62`) verified all 5 root statements in `solution.ndjson` against `Challenge.lean` (`51,692` records).
   - Set-differencing `outputs/leanre.db` (`tcb_decls`, `51,692` records from `challenge.ndjson.zst`) against `outputs/kernel/kernel.db` (`stmt_mask != 0`, `51,687` records from `solution.ndjson.zst`) yields **exact mathematical closure identity** (`[L]`):
     - `Challenge \ Solution[stmt_mask!=0]` (`5` records) `= {sorryAx (axiom), Nat.lor (def), Nat.xor (def), String.mk (def), String.mk._proof_1 (thm)}` — i.e., `sorryAx` used solely in the 5 `Challenge.lean` proof stubs plus the 4 unreferenced `export-targets.txt` primitives (which are also the exact `4` dead records in `solution.ndjson.zst`, `1,468,418 - 1,468,414 = 4`).
     - `Solution[stmt_mask!=0] \ Challenge` `= ∅` (**`0` declarations**).
2. **Real Division `1 / 2` & Role of `RiemannZetaZerosOnLine._proof_1` (`[L]`):**
   - In the decoded kernel AST of `RiemannHypothesis` and all four `Statements.lean` definitions, every `1 / 2` elaborates to:
     `@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) 1 2`
     where the denominator `2 : ℝ` carries `@instOfNatAtLeastTwo Real 2 Real.instNatCast RiemannZetaZerosOnLine._proof_1`.
   - `RiemannZetaZerosOnLine._proof_1` (`decls.id = 1468390`, `stmt_mask = 30 = 2|4|8|16`) has kernel type `Nat.AtLeastTwo (1 + 1)` proved by `Nat.instAtLeastTwoHAddOfNat 1 (Nat.instNeZeroSucc 0)` (`[L]`). Because `Nat.AtLeastTwo` is a `Prop` structure (proof-irrelevant in Lean's kernel), `RiemannZetaZerosOnLine` (`src/Statements.lean:3`) and `Mathlib.RiemannHypothesis` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`) are **kernel-definitionally equal** (`example : RiemannZetaZerosOnLine = RiemannHypothesis := rfl` in Sutherland's `Audit.lean` line 35; that is why `src/Main.lean:4,6` discharges both theorems with the exact same term `rhOfAll`!). Integer-division truncation `(1 : ℕ) / 2 = 0` is completely impossible.
3. **Canonical Typeclass Instances Only (`[L]`):**
   - Every algebraic/analytic instance inside the 5 root types resolves to canonical Mathlib/Lean core instances: `Complex.instField`, `Complex.instZero`, `Complex.instOne`, `Complex.instAdd`, `Complex.instMul`, `Complex.instNeg`, `Complex.instNatCast`, `Real.instLT`, `Real.instDivInvMonoid`, `Real.instOne`, `Real.instZero`, `Real.instNatCast`, `Nat.instMulZeroClass`, and `ZMod.commRing N` (`[L]`). Zero project-defined instances appear anywhere in `stmt_mask != 0`.
4. **Domain Guard & Edge-Case Matrix (`[L, S]`):**
   - **Roots 0 & 1 (`riemannHypothesis`, `riemannZeta_eq_zero_re`):** Quantify over all `s : ℂ` with `riemannZeta s = 0`, `¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)`, and `s ≠ 1`, concluding `s.re = 1 / 2`.
     - *Trivial zeros:* As `n` ranges over `ℕ = {0, 1, 2, ...}`, `-2 * ((n : ℂ) + 1)` ranges over `{-2, -4, -6, ...}`, which are the exact trivial zeros of $\zeta(s)$ (`riemannZeta_neg_two_mul_nat_add_one` in `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:173`).
     - *Why `s = 0` needs no exclusion:* At `s = 0`, $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ has a pole canceling the pole of $\Lambda(s)$, so $\zeta(0) = -1/2 \neq 0$ (`riemannZeta_zero` in `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:151`). Thus `riemannZeta 0 = 0` is false and `s = 0` is not a zero.
     - *Pole at `s = 1`:* Mathematically $\zeta(s)$ has a simple pole of residue $1$ at $s = 1$; `s ≠ 1` explicitly excludes `1` so the statement never depends on Mathlib's total-function value `riemannZeta 1`. Even better, Mathlib proves `riemannZeta 1 = (γ - log(4 * π)) / 2 ≠ 0` (`riemannZeta_one_ne_zero` in `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:441`), so `riemannZeta 1 = 0` is already `False` even without `s ≠ 1`!
     - *Why no `0 < s.re < 1` hypothesis is needed:* Unlike textbook formulations that restrict to the critical strip $0 < \operatorname{Re}(s) < 1$, Mathlib's `RiemannHypothesis` quantifies over **all** $s \in \mathbb{C} \setminus (\{1\} \cup \{-2,-4,\dots\})$, which is **strictly stronger**: proving it also proves $\zeta(s) \neq 0$ on $\operatorname{Re}(s) \ge 1$ ($s \neq 1$, hence the Prime Number Theorem zero-free line $\operatorname{Re}(s) = 1$) and on $\operatorname{Re}(s) \le 0$ outside negative even integers!
   - **Root 2 (`LFunction_ne_zero_of_half_lt_re` / `DirichletLNonvanishingRightOfHalf`, `src/Statements.lean:6-8`):**
     `∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0`
     - *`N = 0` excluded:* `[NeZero N]` (`N ≠ 0`) blocks the degenerate ring `ZMod 0 = ℤ`, where `ZMod.LFunction` (`Mathlib/NumberTheory/LSeries/ZMod.lean:67,83`) is not even defined without `[NeZero N]`.
     - *`N = 1` edge case:* `DirichletCharacter ℂ 1` is `Unique` (`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:214`) with sole element `χ = 1`, and `LFunction_modOne_eq` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:67`) proves `LFunction χ = riemannZeta`. At `N = 1`, `χ ≠ 1` is `False`, so `(χ ≠ 1 ∨ s ≠ 1)` simplifies to `s ≠ 1`, recovering `∀ s, 1/2 < s.re → s ≠ 1 → riemannZeta s ≠ 0`.
     - *Imprimitive trivial characters (`N > 1`, `χ = 1`):* By `LFunctionTrivChar_eq_mul_riemannZeta` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:174`), for `s ≠ 1`, $L(s, \chi_0) = \zeta(s) \prod_{p \mid N} (1 - p^{-s})$, which has a simple pole at `s = 1` (guarded by `χ ≠ 1 ∨ s ≠ 1`) and Euler factors vanishing only on $\operatorname{Re}(s) = 0$ (disjoint from $\operatorname{Re}(s) > 1/2$).
     - *Non-trivial characters (`χ ≠ 1`, primitive or imprimitive):* `χ ≠ 1` satisfies `(χ ≠ 1 ∨ s ≠ 1)` **including at `s = 1`**, so Root 2 simultaneously asserts $L(1, \chi) \neq 0$ and zero-freeness on the entire half-plane $\operatorname{Re}(s) > 1/2$.
   - **Root 3 (`LFunction_eq_zero_re` / `DirichletLZerosOnLine`, `src/Statements.lean:10-12`):**
     `∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2`
     - Strictly stronger than Root 4 because it covers **all** Dirichlet characters (both primitive and imprimitive).
     - `0 < s.re` and `s.re < 1` simultaneously exclude: (i) the pole at `s = 1` (`1.re = 1`), (ii) all trivial zeros at negative integers and `s = 0` (`s.re ≤ 0`), and (iii) all imprimitive Euler-factor zeros from primes $p \mid (N / \operatorname{cond}(\chi))$, where $1 - \chi_{\text{prim}}(p) p^{-s} = 0$ implies $|p^{-s}| = p^{-\operatorname{Re}(s)} = 1$, i.e. $\operatorname{Re}(s) = 0$ (`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:7-34`).
   - **Root 4 (`LFunction_eq_zero_re_of_isPrimitive` / `PrimitiveDirichletLZerosOnLine`, `src/Statements.lean:14-16`):**
     Adds `χ.IsPrimitive` (`conductor χ = N`, `Mathlib/NumberTheory/DirichletCharacter/Basic.lean:292`). At `N = 1`, `isPrimitive_one_level_one` holds (`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:296`), recovering critical-strip RH for $\zeta(s)$.
   - **Explicit Scope Boundary:** All three GRH theorems quantify strictly over `DirichletCharacter ℂ N` (`MulChar (ZMod N) ℂ`, i.e., abelian characters over $\mathbb{Q}$). Dedekind zeta functions $\zeta_K(s)$ of non-abelian number fields, Hecke Größencharaktere, and higher-rank automorphic $L$-functions are **not** claimed (`[L, A]`).

### 1.2 Complete Unfolding of the `2,570`-Definition Statement Closure (`defcone_mask != 0`)

In `outputs/kernel/kernel.db`, `defcone_mask != 0` walks only definition-bearing dependencies (`def`, `inductive`, `opaque`, `quot`, `axiom`), pruning proof terms of theorems (`thm`) referenced inside definitions (`[L]`):

- **Per-root `defcone` sizes (`[L]`):** `riemannHypothesis`: `2,448`; `riemannZeta_eq_zero_re`: `2,448` (`+1` project `def` `RiemannZetaZerosOnLine`, `-1` Mathlib `RiemannHypothesis`); `LFunction_ne_zero_of_half_lt_re`: `2,527`; `LFunction_eq_zero_re`: `2,524`; `LFunction_eq_zero_re_of_isPrimitive`: `2,565`; **5-root union: `2,570`**.
- **Breakdown by kernel declaration kind (`2,570` total, `[L]`):**
  - `def`: `2,178`
  - `inductive`: `365`
  - `opaque`: `22` — **every single one** is a standard Mathlib compiler-hygienic wrapper (`Real.wrapped._@.Mathlib.Data.Real.Basic...` ×10, `MeasureTheory.wrapped...` ×3, `Asymptotics.wrapped...` ×2, `Complex.wrapped...` ×1, `Module.Basis.wrapped...` ×1, plus 5 top-level `wrapped._@.Mathlib.{Topology,Algebra,LinearAlgebra,Analysis}...`); **`0`** project opaques (`[L]`).
  - `quot`: `3` (`Quot`, `Quot.mk`, `Quot.lift` — Lean kernel quotient primitives).
  - `axiom`: `2` (`Quot.sound` `id=530`, `Classical.choice` `id=1044`; `propext` `id=133` enters only inside theorem proofs in `stmt_mask != 0`). **`0` `sorryAx`**, **`0` `Lean.ofReduceBool`**, **`0` `Lean.trustCompiler`** (`[L]`).

Cross-matching all `2,570` declarations against `decl_module` and the pinned source checkouts `data/corpora/{lean4,batteries,mathlib4}` yields a **complete enumeration of every non-Mathlib, non-Lean-core declaration in the `2,570` cone — there are ONLY 8 in total** (`[L]`):

1. **Project-Defined Declarations (`4` total — `0` in `riemannHypothesis`'s `2,448`-def cone! `[L]`):**
   - `RiemannZetaZerosOnLine` (`id=1468391`, `def`, `defcone_mask=2`, `src/Statements.lean:3`)
   - `DirichletLNonvanishingRightOfHalf` (`id=1468393`, `def`, `defcone_mask=4`, `src/Statements.lean:6`)
   - `DirichletLZerosOnLine` (`id=1468395`, `def`, `defcone_mask=8`, `src/Statements.lean:10`)
   - `PrimitiveDirichletLZerosOnLine` (`id=1468409`, `def`, `defcone_mask=16`, `src/Statements.lean:14`)
2. **`Batteries` Library Declarations (`batteries@4488d40d`, `4` total, `[L]`):**
   - `RatCast` (`id=658`, `inductive`, `defcone_mask=31`, `Batteries/Classes/RatCast.lean:11`) — standard rational cast typeclass `ℚ → α`.
   - `RatCast.ratCast` (`id=667`, `def`, `defcone_mask=31`, `Batteries/Classes/RatCast.lean:11`) — projection of `RatCast`.
   - `Rat.cast` (`id=668`, `def`, `defcone_mask=31`, `Batteries/Classes/RatCast.lean:19`) — standard `@[coe]` wrapper around `RatCast.ratCast`.
   - `List.union` (`id=7537`, `def`, `defcone_mask=31`, `Batteries/Data/List/Basic.lean:94`) — standard `BEq`-based list union used in finset/multiset plumbing.
3. **All Other `lake-manifest.json` Third-Party Packages (`Aesop`, `Qq`, `Plausible`, `ProofWidgets`, `Cli`, `ImportGraph`, `LeanSearchClient`):** **`0` declarations** in the `2,570` `defcone` (`[L]`). (In the wider `51,687`-declaration `stmt_mask` theorem closure, `Batteries.*` contributes `42` declarations, `Aesop.*` contributes `1` helper lemma, and the other 6 packages contribute `0`.)
4. **Remaining `2,562` Declarations (`[L]`):** Strictly **Lean 4 Core** (`lean4@819816b2`: `588` source-matched `Init`/`Std`/`Lean` definitions + `5` kernel `axiom`/`quot` primitives + core auto-generated recursors/instances) and **Mathlib** (`mathlib4@0df444a3`, including all `17` `_private.Mathlib.{Data,Analysis}.*` private helpers). Zero custom or shadowed `riemannZeta` or `DirichletCharacter.LFunction` constants exist anywhere in the cone (`[L]`).

---

## 2. Project Compiler, Build Flag & Environment Audit

### 2.1 Toolchain, Manifest & `lakefile.toml` Configuration

- **`lean-toolchain` (`SHA-256 3aac669c…db71`):** Pinned to `leanprover/lean4:v4.33.1` (`819816b2`, `[L]`).
  - *Kernel CVE / Soundness Posture (`[C]` via Deicyde `verification_NOTES.md`):** Lean `v4.33.1` includes the critical kernel fixes of `4.32.2`–`4.33.1` (`#14576` wrong-structure projection proving `False`, `#14806` `is_def_eq` cache, `#14807` `is_prop`, `#14582` non-uniform inductives, `#14838` RC overflow, `#14833` GMP `6.3.0`), while predating the `v4.34.1` C++ runtime memory-safety fixes (`#15241`, `#15289`). Because `solution.ndjson` has been independently re-checked by Lean `v4.36.0` (`leanchecker-paranoid`), Rust `nanoda` (no Lean C++ runtime), `con-leche --compare` (patched for mutual reflexive inductives), and `lean4lean` on `.olean`s, C++ runtime soundness bugs in `v4.33.1` are mitigated across independent implementations (`[C, L]`).
- **`lakefile.toml` (`SHA-256 b831ad8c…ec4c`, `[L]`):**
  - `autoImplicit = false` (`line 7`) and `relaxedAutoImplicit = false` (`line 8`) globally prevent accidental implicit universal quantification of misspelled identifiers (a classic Lean vacuity bug where `∀ ( typo : α ), ...` silently binds a fresh variable!).
  - `maxSynthPendingDepth = 3` (`line 9`), `pp.unicode.fun = true` (`line 10`), `maxHeartbeats = 4000000` (`line 11`), `moreLeanArgs = ["--tstack=400000"]` (`line 4`), plus `synthInstance.maxHeartbeats = 400000` on `GroundTheoryFields` (`line 41`) — purely resource/elaborator search budgets with zero effect on kernel typing rules.
  - Single direct dependency: `mathlib` at `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`, `[L]`).

### 2.2 Whole-Corpus (`175,187`-File) Flag, Metaprogramming & Instance Sweep

A parallel lexical sweep across all `175,187` `.lean` files (`17,374,215` lines) cross-checked against `outputs/kernel/kernel.db` (`1,468,418` exported records) establishes (`[L]`):

| Feature / Construct | Source Hits (`files`) | Kernel Export (`kernel.db`) | Security Assessment (`[L]`) |
|---|---:|---:|---|
| `unsafe`, `@[implemented_by]`, `@[extern]`, `@[csimp]` | **`0`** (`0`) | **`0`** (`attrs & 1 = 0`) | **CLEAN:** Zero runtime C/FFI substitution or `unsafe` casts. |
| `debug.skipKernelTC`, `debug.*`, `no_index` | **`0`** (`0`) | **`0`** | **CLEAN:** Kernel typechecking never bypassed; zero `no_index` pattern tricks. |
| `sorry`, `admit`, `sorryAx`, `axiom`, `opaque`, `meta` | **`0`** (`0`) | `3` `Init` axioms, `91` Mathlib opaques, **`0` project** | **CLEAN:** Zero project axioms, zero project opaques, zero `sorryAx`. |
| `native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler` | **`0`** (`0`) | **`0`** (`flags & 36 = 0`) | **CLEAN:** All computational proofs (`decide +kernel`) reduce inside the kernel (`F_REFL_TRUE` `129,492`, `F_OF_DECIDE` `472`), never trusting compiled code. |
| `partial def` | **`2`** (`2`) | **`0`** (`attrs & 2 = 0`) | **CLEAN:** Located at `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:41` (`go`) and `src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:18` (`copyAt`). Both are elaboration-time `MetaM`/`CoreM` helpers; every term they emit via `addDecl` or `g.assign` is kernel-checked and exported as a total `thm`/`def`. |
| Global `notation` / `infix` / `prefix` / `postfix` | **`0`** (`0`) | N/A (elaborator) | **CLEAN:** All `1,722` notation rules (`952` files) are strictly `local` or `scoped`; `Statements.lean` imports only `Mathlib` so zero project notations are in scope for the headline statements. |
| `set_option autoImplicit` / `relaxedAutoImplicit` | `11,203` (`10,743`) | N/A | **CLEAN:** **100%** of occurrences are `set_option autoImplicit false` (`0` set `true`; `0` mention `relaxedAutoImplicit`). |
| `set_option allowUnsafeReducibility true` | `37` (`~30`) | Erased at kernel | **BENIGN:** Used in p-adic Hodge (`IsCrisP.lean:49`, `BcrisOneSubFrobeniusSurjective.lean:98`) & spherical-orbit proofs to unfold `@[irreducible]` defs during elaboration. The Lean kernel ignores `@[irreducible]` attributes during `is_def_eq`. |
| `set_option backward.isDefEq.respectTransparency false` (and `.types false`) | `1,877` + `87` | Erased at kernel | **BENIGN:** Elaborator-only unification flag; kernel `is_def_eq` always uses full delta-reduction transparency. |
| `set_option quotPrecheck false` / `hygiene false` | `7` / `31` | Erased at kernel | **BENIGN:** `quotPrecheck` is a pre-elaboration lint on `Quot.lift` (kernel still checks `Quot.lift` proof obligations); `hygiene false` affects local tactic binder naming inside 20 proof files. |
| `set_option maxHeartbeats` / `maxRecDepth` | `55,792` / `34` | Erased at kernel | **BENIGN:** Ranges up to `maxHeartbeats 64000000` (`1` file) and `maxHeartbeats 0` (unlimited, `4` files), plus `maxRecDepth 1000000` (`1` file). Affects compile time only. |
| `noncomputable section` / `noncomputable def` + `classical` | `78,044` + `8,609` / `38,372` | `Classical.choice` (`279` fan-in) | **EXPECTED:** Standard classical analytic math over `ℝ`/`ℂ` (`Mathlib`'s `riemannZeta` and `LFunction` are themselves `noncomputable` and use `Classical.choice` in `defcone_mask`). |
| Custom `instance` (`7,538` global, `600` local, `798` `attribute [instance]`, `50,672` `attribute [local instance]`, `459` `attribute [-instance]`, `40` `linter.overlappingInstances=false`) | `59,507` directives | **`0`** project instances in `stmt_mask != 0` | **CLEAN FOR TCB:** `attribute [-instance]` (e.g., `Matrix.normedAddCommGroup` in `InducedSectionSmooth.lean:265`) and custom instances (`instModuleComplex`, `instAlgebraComplex`) operate on project-defined structures (`HeckeAlgebra`, `SobolevSpace`, `FibreSpace`) or locally suppress competing Mathlib matrix norms. None enter `Statements.lean` (which imports only `Mathlib`), and kernel `is_def_eq` forbids cross-file instance mismatches on shared bridges. |
| `open private ... from ...` | `220` (`157`) | `_private.*` (`82,799` live) | **BENIGN:** Bypasses module visibility (`private`), which is an elaborator namespace convention; kernel checks every `_private.*` declaration identically to public ones. |

### 2.3 `Supplements/Kernels/*` & Dead Import-Hub Stratigraphy

Inspecting `src/Supplements/Kernels/` reveals an instructive split between the **module import graph** and the **live kernel proof graph** (`[L]`):
- `src/Main.lean:2` imports `Supplements.Kernels.MainTheoremsAll` (`src/Supplements/Kernels/MainTheoremsAll.lean:1-2`, `0` live kernel decls), which imports `Supplements.Kernels.MainTheoremsCritical` (`src/Supplements/Kernels/MainTheoremsCritical.lean:1-4`, `0` live kernel decls) plus four files under `src/Development/AutomorphicArithmetic/AutomorphicVarieties/SmallClassNumbers/` (`CorGKOf.lean`, `ClassNumberThree.lean`, `LenEqZeroIff.lean`, `OnePoint.lean`).
- All **four** `SmallClassNumbers/*` modules contribute **`0` live kernel declarations** to `solution.ndjson.zst` (`[L]`): they prove standalone side results (`UpperTheory.V.SmallClassNumbers.bound` on cyclotomic $\mathrm{Sha}$ lengths and `onePoint`, `[L]`) that were wired into `MainTheoremsAll` so `lake build Main` would typecheck them, even though none of the 5 theorems in `Main.lean` reference them! (Specifically, `OnePoint.lean:7` executes `attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain ...` in `Main`'s import environment, which has zero effect on `Main.lean`'s 5 statements because `Statements.lean` is compiled *before* `MainTheoremsAll` and `Main.lean` uses canonical `Mathlib` types only `[L]`.)
- Only `src/Supplements/Kernels/MainTheorems.lean:7-16` contributes live declarations (`4` theorems: `allChi`, `rhOfAll`, `claimAll`, `critAll`, `[L]`).

---

## 3. Top Bridge-Contract, Junk-Value & Witnessing Audit

### 3.1 Complete Verified Bridge from `Main.lean` to `everyCharacter` (`58,857` Decls Outside `allChi`)

The `58,857` live declarations outside `allChi`'s dominator subtree (`1,468,414 - 1,409,557 = 58,857`, `[L]`) consist solely of `Mathlib`/`Lean` library Closure (`~58.8k` decls) plus **9 tiny, fully-read project theorems** that reduce all 5 headline statements cleanly to `UpperTheory.EveryCharacter` (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13-14`, `[L]`):

1. **Identity of `UpperTheory.EveryCharacter` (`id=51576`, `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13-14`):**
   ```lean
   def UpperTheory.EveryCharacter : Prop := ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
   ```
   This is **token-for-token identical** to `DirichletLNonvanishingRightOfHalf` (`src/Statements.lean:6-8`) and `Claim.HalfPlane` (`src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean:3-4`, `[L]`). Hence `LFunction_ne_zero_of_half_lt_re := allChi` (`src/Main.lean:8`) is a zero-step definitional match! *(Note: `UpperTheory.FinalTheorems.riemannHypothesis` in `MainConclusion.lean:13` and all of `RiemannHypothesisOfEveryCharacter.lean` have **`0` live kernel declarations** — `Main.lean` routes through `rhOfAll` instead `[L]`.)*
2. **`rhOfAll` → `Formalism.VW.rh_of_every` → `Formalism.VW.rh_of_right` (`Roots 0 & 1`):**
   - `Formalism.VW.rh_of_every` (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:29-32`) instantiates `h : UpperTheory.EveryCharacter` at `N = 1`, `χ = (1 : DirichletCharacter ℂ 1)`, `Or.inr hs1` (`s ≠ 1`), and rewrites via Mathlib's `LFunction_modOne_eq` to obtain `∀ s, 1/2 < s.re → s ≠ 1 → riemannZeta s ≠ 0` (`[L]`).
   - `Formalism.VW.rh_of_right` (`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5-61`) proves `Mathlib.RiemannHypothesis` by trichotomy on `s.re` vs `1 / 2`: for `s.re > 1/2` it applies `hz` directly; for `s.re < 1/2` it rules out `s = 0` via `riemannZeta_zero` ($\zeta(0) = -1/2 \neq 0$), applies `riemannZeta_one_sub` at `1 - s` (`1/2 < (1 - s).re`, `1 - s ≠ -n` for `n : ℕ`), and shows $2(2\pi)^{-(1-s)} \Gamma(1-s) \cos(\pi(1-s)/2) \zeta(1-s) \neq 0$ because any zero of $\cos(\pi(1-s)/2)$ forces $s = -2k$ with $k \ge 1$, contradicting the non-trivial-zero hypothesis `¬∃ n : ℕ, s = -2 * (n + 1)` (`[L, S]`).
3. **`critAll` → `Formalism.VW.critLine` (`Root 4` — Primitive Strip GRH):**
   - `Formalism.VW.critLine` (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:11-27`) handles `0 < s.re < 1` (`s ≠ 0`, `s ≠ 1`): if `s.re < 1/2`, it converts `LFunction χ s = 0` into `completedLFunction χ s = 0` via `LFunction_eq_completed_div_gammaFactor` + `gammaFactor_ne_zero` (`Gammaℝ_ne_zero_of_re_pos`), reflects to `completedLFunction χ⁻¹ (1 - s) = 0` via Mathlib's `IsPrimitive.completedLFunction_one_sub`, divides by `gammaFactor χ⁻¹ (1 - s)`, and contradicts `h N χ⁻¹ (1 - s)` (`[L, S]`).
4. **`claimAll.2.1` → `Claim.strip` (`Root 3` — General / Imprimitive Strip GRH):**
   - `Claim.strip` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:59-74`) handles arbitrary `[NeZero N]` and arbitrary `χ : DirichletCharacter ℂ N` on `0 < s.re < 1`: for `s.re < 1/2`, `prim_zero` (`lines 23-34`) strips the finite product $\prod_{p \in N.\text{primeFactors}} (1 - \chi_{\text{prim}}(p) p^{-s})$ via `LFunction_changeLevel` (proving `‖χ_prim(p) * p^(-s)‖ ≤ p^(-s.re) < 1` for `s.re > 0` in `factor_ne_zero`, `lines 7-21`), reflects `χ.primitiveCharacter` via `prim_reflect` (`lines 42-57`), and contradicts `h χ.conductor χ.primitiveCharacter⁻¹ (1 - s)` (`[L, S]`).

### 3.2 Resolution of the `Formalism.Gchi` Division-by-`LFunction χ 1` Question

Initial static recon (`02_re_and_tooling_strategy.md`) flagged `Formalism.Gchi` in `src/Formalism/StatementOC.lean:20-21` because its definition divides by `DirichletCharacter.LFunction χ 1` without an `if χ = 1` guard:
```lean
def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ := Schi χ x + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re * x
```
Kernel-exact tracing in `outputs/kernel/kernel.db` resolves this completely (`[L]`):

1. **`Formalism.Gchi` Is 100% Dead Stratigraphy (`[L]`):**
   - Querying `decls` for module `Formalism.StatementOC` returns **only two declarations**: `Formalism.Sz` (`id=137703`) and `Formalism.Gz` (`id=137704`, `35` dependents).
   - **`Formalism.Gchi` (`StatementOC.lean:20`), `Formalism.Schi` (`:17`), `OCStep` (`:23`), `OCStepUpper` (`:31`), `OCAvg` (`:39`), `OCAvgUpper` (`:52`), and `RiemannHypothesisOfLowerBounds` (`:65`) are ALL DEAD (`0` kernel declarations in `solution.ndjson.zst`)!** They belong to an abandoned early formulation in `StatementOC.lean`.
2. **All Three LIVE Character Observables Explicitly Guard `if χ = 1` (`[L]`):**
   The live proof replaces `Formalism.Gchi` with three complex-valued observables equated by `UpperTheory.Comparison₂.gChi_eq` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/GChiEq.lean:16-36`):
   - **`Formalism.HC.An.gChi`** (`id=137795`, `19` dependents, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:23-24`):
     ```lean
     def gChi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ := if χ = 1 then ((G y : ℝ) : ℂ) else sumLamChi χ y + (y : ℂ) * logDerivativeAtOne χ
     ```
   - **`Formalism.MainNotions.GlobalTheoryTheory.gChi`** (`id=108130`, `15` dependents, `src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/FiltrationCocycleLiftCriterion.lean:24-25`) — identical `if χ = 1` guard.
   - **`Deduction.Gchi`** (`src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean:15-19`) — branches on `if χ = 1` to use `- y * Real.log y + (1 + γ) * y` instead of `deriv (LFunction χ) 1 / LFunction χ 1`.
3. **Triple Defense Against `0 / 0 = 0`, Non-Differentiability & Imprimitive `χ = 1` (`[L, S]`):**
   - **Guard 1 (`Level.Nt` erasure):** In `Formalism.HC.Level.Gm` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:32,38`), `Gm y := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re` sums over `Λ.Nt := Λ.KEPT.erase PChar.one`, explicitly stripping the trivial primitive character (`ψ.χ = 1` iff `ψ = PChar.one` by `PChar.of_one`, `:70`).
   - **Guard 2 (`CharFamily.adm`):** `Deduction.CharFamily` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean:24-32`) carries field `adm : ∀ i, N i = 1 ∨ χ i ≠ 1`, blocking imprimitive trivial characters (`N > 1, χ = 1`, whose von Mangoldt sum omits primes dividing $N$), discharged in `src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelFamily.lean:19-25` from `ψ.prim`.
   - **Guard 3 (Dirichlet's $L(1,\chi) \neq 0$ & Entirety in `poleData_char`):** In `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean:145-240`, `poleData_char` splits on `by_cases hχ : χ = 1`:
     - In the `χ = 1` (`N = 1`) branch (`lines 146-229`), it defines the entire function `g := Function.update (fun s => (s - 1) * riemannZeta s) 1 1`, proves `deriv g 1 = γ` via Mathlib's `tendsto_riemannZeta_sub_one_div`, and uses Mathlib's `riemannZeta_one_ne_zero` (`line 196`).
     - In the `χ ≠ 1` branch (`lines 230-239`), it explicitly passes **`DirichletCharacter.differentiable_LFunction hχ`** (guaranteeing `deriv (LFunction χ) 1` is a genuine complex derivative, not junk `0`) and **`DirichletCharacter.LFunction_apply_one_ne_zero hχ`** (Mathlib's theorem that $L(1,\chi) \neq 0$ for $\chi \neq 1$, guaranteeing the denominator in `deriv (LFunction χ) 1 / LFunction χ 1` is strictly non-zero!).
   - **Sub-check on `An.logDerivativeAtOne` (`Analytic.lean:11-12`):** `logDerivativeAtOne χ := deriv (LFunction χ) 1 / LFunction χ 1` is unguarded in its `def`; at `χ = 1`, `LFunction 1` has a simple pole at `1`, so Mathlib's non-differentiable `deriv` returns `0` and `0 / LFunction 1 1 = 0`. However, every live consumer (`HostAddCharCompatible` in `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean:18-20` under `ψ ≠ 0`, and `EAtH.bdL` in `ExplicitFormulaErrorOfHostConditions.lean:150-151` over `θ ∈ H.Bounded Λ.KEPT` which excludes `PChar.one ∈ Λ.KEPT`) evaluates `logDerivativeAtOne` exclusively on primitive characters with `χ ≠ 1` (`[L]`).

### 3.3 Audit of Top Spine Contracts, Dead Twins & Witnessing Tricks

| Contract / Declaration | Live ID (`ALL` `subtree`) | Anchor (`data/rh_mirror/`) | Read Status & Verdict (`[L]`) | Audit Notes |
|---|---:|---|---|---|
| `Supplements.Kernels.MainTheorems.allChi` (`allChi`) | `1468387` (`1,409,557`) | `src/Supplements/Kernels/MainTheorems.lean:7` | `READ` / `wrapper` | Direct 1-line alias for `UpperTheory.FinalTheorems.everyCharacter` retaining `96.0%` of the live proof. |
| `UpperTheory.FinalTheorems.everyCharacter` | `1468386` (`1,409,556`) | `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:10` | `READ` / `real` | Applies `everyCharacter_of_row` to `galoisLocalGlobalStrong_recParameter` (`95,102` decls); owns the `331,598`-decl shared diamond (`110,898` non-trunk direct dominator children). |
| `UpperTheory.FinalTheorems.everyCharacter_of_row` | `1373283` (`982,855`) | `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7` | `READ` / `real` | Takes `(h : Row0b fun h rc => IsRecT h rc)` and calls `every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)`. |
| `UpperTheory.LiteratureTheorems.OpenLiteratureStatements` | `85112` (`1`) | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215` | `READ` / `wrapper` | **Architectural smell (Layer 3, non-fatal):** 3-field `Prop` structure (`caraianiLocalGlobalDual : Row`, `localLanglandsExists : RecTExists`, `galoisRepOfPolarizedPairLit : Row`). Fields 1 and 3 have **identical type** `UpperTheory.One.M.Row` (defeq to `Row0b IsRecT`) and receive the **exact same term `h`**. Across all **`195`** theorems in `EveryCharacterOfLiteratureOfVWin.lean` (`199` module decls in `kernel.db`), **`152` ignore `O` syntactically**, `39` forward `O` (`30` into dead ends that never project `O`, `9` reaching a projection), and **only `4` directly project a field of `O`** (`local_langlands_recT_exists_of_literature`, `pair_u_of_literature`, `carU_local_global_of_literature`, `literature_automorphy`) — so **`182 / 195` (`93.3%`) are completely independent of `O`** (`13 / 195` use `O` transitively)! *(Kernel trap note: in `kernel.db`, all `198` module dependents show `edges.kind = 3` (`both`) because `(fun O : OpenLiteratureStatements => body)` retains `OpenLiteratureStatements` in `lam.type` even when `bvar 0` is unused!)* |
| `UpperTheory.GalStar.Row0b` | `84296` (`1`) | `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69` | `PARTIAL` / `proxy` | Asserts that for any CM number field `E`, prime `l`, `ι : Qbar l ≃+* ℂ`, `a ≥ 1`, regular algebraic `π : CuspSub E a` polarized with `χ`, there exists `(r : G E Ω →* GL (Fin a) (Qbar l), wt, HT)` satisfying `PropsB` (`cont`, `ss`, `away`, `weights`, `weights_conj`, `above`). **Tailored weakening noted:** `AwayB` (`lines 26-31`) weakens unramified/tame local-global compatibility to primes split over $\mathbb{Q}_g$ with **`16 * a^2 < g` (`IsQpBig`, `line 15`)** plus `TmW`/`Sqf`/`mono0` or `Tor` guards (`Row0.row0b`, `line 84`). Nested `CuspSub`, `WD`, `LocBridge`, `IsPstAt` are **`OPAQUE`** (delegated to `galois`). |
| `UpperTheory.Zero.LLC.IsRecT` & `RecTExists` | `85109` (`1`) & `85111` (`1`) | `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:76` | `PARTIAL` / `proxy` | `IsRecT h rc := ∃ a ha, LawsT a ha rc`. **Tailored weakening noted:** in `LawsT` (`lines 55-73`), `twist`, `central`, `dual`, `inj`, and `depth` are restricted to `Good x` (`lines 20-24`: supercuspidal support having rank `1` or rational $\mathbb{Q}_g$ depth-zero `KOne`-fixed twists), plus `TypeLaw` (`line 35`). Nested `IrrGL`, `Segment`, `WD` are **`OPAQUE`** (delegated to `galois`). |
| `UpperTheory.Top.VWin` | `85495` (`2`) | `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49` | `PARTIAL` / `real` | `∀ ψ : PChar, VWinAt ψ 401`. Unfolds cleanly through `VWinAt`, `VAt`, `PageN`, `WinPair` (`q % 8 = 3`, `d % 16 = 7`, odd primes `p ≤ Y^(eps/5)` dividing `d + 1`), `IsChiField` (subfields of `CyclotomicField N ℚ` cut out by `ψ.val a = 1` and Jacobi symbols), and `VVle` bounding `∑_{l ∈ S} log l * ∑_{1 ≤ e < ⌊x^401⌋₊} shaLen(ld l, e) ≤ exp(x^eps / 2)`. Only leaf `Formalism.GaloisCohomology.LData` / `shaLen` remains **`OPAQUE`** (delegated to `window`). |
| `Formalism.HC.ZeroFreeAll` & `UpperTheory.Top.imprimitive` | `137018` (`1`) & `137555` (`1`) | `ExplicitFormulaErrorOfHostConditions.lean:18` & `Imprimitive.lean:5` | `READ` / `real` | `ZeroFreeAll` asserts `∀ (ψ : PChar) (s : ℂ), 1/2 < s.re → LFunction ψ.χ s ≠ 0` (**without** `s ≠ 1`!). Why isn't `ψ = PChar.one, s = 1` a contradiction? Because at `N = 1, χ = 1, s = 1`, `LFunction 1 1 = riemannZeta 1 ≠ 0` holds in Mathlib (`riemannZeta_one_ne_zero`, used in `poleData.lean:196`)! Then `imprimitive` (`Imprimitive.lean:5-35`) lifts `ZeroFreeAll` to `UpperTheory.EveryCharacter` (adding `(χ ≠ 1 ∨ s ≠ 1)` because `LFunction_changeLevel` requires `χ_prim ≠ 1 ∨ s ≠ 1` when `N > 1`!). |
| `GlobalTheory.Fc.HypsAlt`, `DefiniteSideCondition`, `Closed`, `LinkN` | `132551` (`1`), `137013` (`1`), `107824` (`1`), `132560` (`1`) | `ThirdPlaceSeries/{Hyps.lean:22, DefiniteSideCondition.lean:25}`, `ParamsHeightRankConstant.lean:159`, `GlobalTheoremInputs.lean:45` | `HypsAlt`/`DefiniteSideCondition`/`LinkN`: **`OPAQUE`**; `Closed`: `READ` | **Dead twins caught (`[L]`):** `UpperTheory.Top.plugAll`/`plugWin` (`EveryCharacter.lean:8,16`), `GlobalTheory.Fc.Hyps` (`APerTw.lean:23`), and `GlobalTheory.Fc.DRS` (`DRS.lean:21`) are **100% DEAD (`0` kernel decls)** — replaced on the live spine by `every_character_of_green_v_win`/`zero_free_all_of_green_v_win` (`TopPlug.lean:12-18`), `HypsAlt`, and `DefiniteSideCondition`! Deep nested fields (`D7`, `FamP`, `SizeData₂`, `BundleCondition`, `RowsU`) are flagged **`OPAQUE`** (delegated to `theta`). |

#### Non-Vacuity Check: Could `Nonempty (HypsAlt ...)` Be Vacuously Inhabited by `𝒜 := fun _ => False`?

Because almost every field of `HypsAlt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22-91`) quantifies over `(Fm : FamP eps) (hc : 𝒜 Fm)` or `Closed (D3 3 𝒜) ...`, a classic Lean witnessing exploit would instantiate `𝒜 := fun _ => False` so all universal fields hold vacuously (`False.elim`)! Tracing the consumer chain (`TopPlug.lean:14-15` → `ShapeOf.lean:24-32` → `TopShape.lean:33-55` → `ZeroFreeAllOfTopG.lean:26-34`) proves **why this exploit is impossible** (`[L]`):
1. `HypsAlt` carries field `hEx : MinkDiv → UpperTheory.Top.ExS 𝒜 cT` (`Hyps.lean:26`), where `ExS 𝒜 cT` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExS.lean:10-12`) asserts `∀ la > 1, ∀ G : FReq, HostExW la G.req → DesignChoices (WithTw fun Fm => 𝒜 Fm ∧ G.cls la Fm) 3 cT`.
2. In `UpperTheory.Top.shape_closed_link_n_of_green` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:50-51`), `designExists_of_tuSize_aux4n_litThin` discharges `MinkDiv` internally (`fun hM => hEx hM la G hla hH`) to produce `hE : DesignExists (fun Fm => 𝒜 Fm ∧ G.cls la Fm) ...`.
3. Unfolding `Formalism.MainNotions.DesignExists` (`src/Formalism/SharpRestriction/ParamsHeightRankConstant.lean:187-190`) reveals an **explicit existential witness requirement**:
   `∃ ε0 > 0, ∀ eps ∈ (0, ε0], ∀ K : TransportedAlt, ∃ (Fm : FamP eps) (CH : ℝ), 𝒜 Fm ∧ G.cls la Fm ∧ 0 ≤ CH ∧ Fm.Large K CH ∧ ...`
   Setting `𝒜 := fun _ => False` at `eps = ε0` and `G = GChi ψ` (`ZeroFreeAllOfTopG.lean:30`, fed by `supplyChi ψ (hV ψ)`) would require `∃ Fm, False`, which is unprovable! Conversely, `DesignExists` produces concrete families `Fm` with arbitrarily large constant thresholds `Fm.Large K CH`, ensuring `Closed 𝒞 P` (`ParamsHeightRankConstant.lean:159-161`) is discharged non-vacuously. *(Minor artifact noted `[L]`: `FamP.Large` at `ParamsHeightRankConstant.lean:139` contains a harmless vestigial conjunct `∧ True ∧` where a deleted `K.t` list check once sat.)*

---

## 4. Independent Spot-Check of Pinned Mathlib `0df444a3` Definitions

All three core analytic number theory definitions were inspected directly in `data/corpora/mathlib4/` at commit `0df444a360eaa60ab8c11dca51a86af692955474` (`[L, S]`):

1. **`completedRiemannZeta` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:68`, `kid=51209`):**
   - Defined as `def completedRiemannZeta (s : ℂ) : ℂ := completedHurwitzZetaEven 0 s`, which unfolds (`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:297-298`) to `((hurwitzEvenFEPair 0).Λ (s / 2)) / 2` — half the Mellin continuation `WeakFEPair.Λ` (`kid=31296`, built on entire `WeakFEPair.Λ₀` `kid=31295` minus polar parts `1/s` and `1/(1-s)`) of the periodic Jacobi theta kernel `evenKernel 0 x = re(jacobiTheta₂ 0 (I * x))` (`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:65-93`).
   - *Pinned validation theorems (`[L]`):* `differentiable_completedZeta₀` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:90`), `differentiableAt_completedZeta` away from `0, 1` (`:94`), `completedRiemannZeta_one_sub : Λ(1 - s) = Λ(s)` (`:106`), `completedRiemannZeta_residue_one` (`:111`), and `completedZeta_eq_tsum_of_one_lt_re` (`:192`).
2. **`riemannZeta` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:121`, `kid=51211`):**
   - Defined as `def riemannZeta := hurwitzZetaEven 0`, unfolding (`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:583-585`) to:
     `Function.update (fun s ↦ completedHurwitzZetaEven 0 s / Gammaℝ s) 0 (-1 / 2)`
   - *Pinned validation theorems & pole/zero behavior (`[L]`):*
     - **Dirichlet series on `Re(s) > 1`:** `zeta_eq_tsum_one_div_nat_add_one_cpow` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:214`) proves `riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s` (independent of `0 ^ s` conventions!).
     - **Analytic continuation on `ℂ \ {1}`:** `differentiableAt_riemannZeta` (`:139`) and `analyticOn_riemannZeta` (`:146`) establish holomorphicity on `{1}ᶜ` — by identity of analytic continuation on the connected domain `ℂ \ {1}`, this **uniquely** pins down `riemannZeta s` for every `s ≠ 1`!
     - **Value at `s = 0` & trivial zeros:** `riemannZeta_zero : riemannZeta 0 = -1 / 2` (`:151`, continuous across `0` via `differentiableAt_update_of_residue`); `riemannZeta_neg_two_mul_nat_add_one` (`:173`) proves `riemannZeta (-2 * (n + 1)) = 0` via the poles of `Gammaℝ` (`div_zero`).
     - **Functional equation & pole at `s = 1`:** `riemannZeta_one_sub` (`:178`), `riemannZeta_residue_one` (`:242`), `tendsto_riemannZeta_sub_one_div` (`Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:342`), and `riemannZeta_one : riemannZeta 1 = (γ - log (4 * π)) / 2` (`:418`) with `riemannZeta_one_ne_zero : riemannZeta 1 ≠ 0` (`:441`).
3. **`DirichletCharacter.LFunction` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:61`, `kid=51575`):**
   - Under `[NeZero N]`, defined as `ZMod.LFunction χ s` (`Mathlib/NumberTheory/LSeries/ZMod.lean:83-84`):
     `N ^ (-s) * ∑ j : ZMod N, χ j * hurwitzZeta (toAddCircle j) s`
   - *Pinned validation theorems (`[L]`):*
     - **Dirichlet series on `Re(s) > 1`:** `LFunction_eq_LSeries` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:75`) proves `LFunction χ s = LSeries (χ ·) s = ∑' n : ℕ, χ n / n ^ s` for `1 < s.re`.
     - **Analyticity & uniqueness:** `differentiableAt_LFunction` (`:92`, for `s ≠ 1 ∨ χ ≠ 1`) and `differentiable_LFunction` (`:98`, entire on `ℂ` whenever `χ ≠ 1`), uniquely determining $L(s, \chi)$ on $\mathbb{C}$ (for $\chi \neq 1$) and $\mathbb{C} \setminus \{1\}$ (for $\chi = 1$).
     - **Consistency with `riemannZeta`, level-change & functional equation:** `LFunction_modOne_eq` (`:67`), `LFunction_changeLevel` (`:150`), `LFunctionTrivChar_eq_mul_riemannZeta` (`:174`), `LFunction_eq_completed_div_gammaFactor` (`:259`), and `IsPrimitive.completedLFunction_one_sub` (`:284`).

---

## 5. Reproduction Commands

```bash
# Validate schema & kernel-exact node/edge/anchor integrity of outputs/decomp/tcb_audit.json
python3 leanre/leanre.py decompile validate outputs/decomp/tcb_audit.json
```
