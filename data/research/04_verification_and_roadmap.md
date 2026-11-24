# Reference Counts and Verification Scope

Reference figures pinned across this repository (verified by [the consistency scanner](../verify/r3_audit.py)):

- **No global "automorphy lifting":** The [announcement note](https://alpo.ge/remark.pdf) uses "theta lifts" and "natively automorphic" rather than "automorphy lifting". Taylor–Wiles patching appears locally inside Pillar C (`VWin`).
- **Dirichlet-only GRH:** [Statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Statements.lean#L3-L16) defines RH for $\zeta(s)$ and GRH for **Dirichlet $L$-functions** over $\mathbb{Q}$ only. Extended RH (Dedekind zeta / Hecke $L$-functions) is not claimed.
- **Line & file counts:** `175,187` `.lean` files and `17,374,215` physical lines (`wc -l`, `1,030,531,854` B, `0` comments) at the [pinned community mirror](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) (formerly `Deicyde/riemann-hypothesis`). Every file ends with `\n`; the `17,549,402` count reported by `drew2apps` adds one empty trailing element per file from `split('\n')` (`17,374,215 + 175,187`).
- **Export declaration counts** (always attributed to checker and archive):
  - `1,468,418` folded JSON records (`con-leche` on Sutherland's MIT export; `1,468,414` live + `4` dead primitives).
  - `1,484,733` unpacked environment constants (`nanoda` via `nasqret` on the same MIT export: `+1` mutual inductive type + `8,342` ctors + `7,972` recursors).
  - `1,484,729` unpacked constants (`nanoda` on Elliot Arledge's independent export).
- **Kernel-exact dead code & timeouts:** `28,904` of `175,187` modules contribute `0` decls to `solution.ndjson.zst` (`28,471` unused modules, `2,358,861` lines). `Formalism.Gchi` and `DyadicPrimeIntervals.Run1..4` (4 of 5 `lean4lean` default-fuel timeouts) are dead; `ChebyshevPrimeBounds.SmallLoop` (`9/9` decls via `PI.PC.loop_run._proof_1_1`) is live.
- **Separate Nov 20 claims:** Alpöge and Claude's Lean 4 formalization is unrelated to Alessandro Masullo's ~940-page non-Lean manuscript released the same day.
- **Licensing constraint:** This repository tracks zero `.lean` files or multi-line proof bodies because `lean.tar.gz` ships without a license. Tracked artifacts contain only identifiers, structural edges, hashes, counts, and fair-use ≤1-line headers.

## Epistemic layers and provenance

### Four epistemic layers

1. **Layer 1 — Kernel validity (syntactic soundness):** Independent kernels (`Lean v4.33.1`, `leanchecker`, Rust `nanoda`, `con-leche --compare`, `lean4lean`) accept the exported terms with zero `sorryAx`, zero custom axioms, and only `[propext, Classical.choice, Quot.sound]` *(PASS as of 2026-11-21)*.
2. **Layer 2 — Specification fidelity (semantic TCB):** Formal statement types and their `2,570`-definition closure encode the classical RH and Dirichlet-GRH statements without vacuous hypotheses or broken coercions *(zero specification bugs found in [the TCB dossier](../analysis/tcb_and_contracts.md))*.
3. **Layer 3 — Human mathematical intelligibility:** Reverse-engineering the 17.37M-line DAG into an auditable architecture separating core math from boilerplate *(in progress; `leanre` instruments this layer)*.
4. **Layer 4 — Institutional / peer consensus:** Published scrutiny by analytic number theorists and Clay Mathematics Institute adjudication *(open; outside the scope of `leanre`)*.

### Provenance tags

Longer technical dossiers in `analysis/` tag non-trivial claims with explicit source markers:

- **`[L]` Machine-extracted:** Verified directly against pinned `.lean` sources (`40e56bab`), `solution.ndjson.zst`, `challenge.ndjson.zst`, or deterministic `leanre` scripts.
- **`[A]` Author note claim:** Asserted in the [announcement note](https://alpo.ge/remark.pdf), whose Footnote 4 notes that parts paraphrase an AI summary *"which might make zero sense."*
- **`[C]` Third-party report:** Reported by named community verifiers or readers (`Sutherland`, `Deicyde`, `nasqret`, `jae-63`, `drew2apps`, `keithadler`, `rgrossharv`), not re-executed here.
- **`[S]` Standard published math:** Established textbook or paper result independent of this archive.
- **`[M]` Model / heuristic label:** CS/RE analogy, toy model, or AI-draft overlay, kept off-by-default and paired with where the analogy breaks.

### Synthetic demos vs. extracted telemetry

Hand-authored maps and synthetic DAGs carry permanent labels (`HAND-AUTHORED CONCEPT MAP` / `SIMULATION — SYNTHETIC WIRING`) to distinguish them from data extracted deterministically from commit `40e56bab` or archive digests (`9631b4f0…9c7fc` / `5ea74b91…244e`).

### Numerical conventions in toy models

- Explicit-formula demos distinguish $\psi(x)$ and `Formalism.Gz x` from $\pi(x)$, include main terms ($-\log 2\pi$ and trivial-zero tails), pair conjugate zeros and functional-equation quadruples $(\beta \pm i\gamma, 1-\beta \pm i\gamma)$, and distinguish amplitudes $2x^\beta/|\rho|$ ($\psi$) from $2x^\beta/|\rho(\rho-1)|$ (`Gz`).
- Finite-field analogies over $\mathbb{F}_p$ list where they break over $\mathbb{Q}$ (no Frobenius map, Archimedean place, infinitely many zeros).
- Displayed zeta zero heights and classical bounds are taken verbatim from published tables and papers.
