# Mathematical Background and Proof Overview

Mathematical exposition of the Riemann Hypothesis, Dirichlet-only GRH cryptographic implications, and the top observable $G_z(x)$ (epistemic scope in [reference counts & verification scope](04_verification_and_roadmap.md)).

## 1. Three Ways to Read RH

1. Function zeros: $\zeta(s) = \sum n^{-s}$, analytically continued to $\mathbb{C} \setminus \{1\}$, vanishes at $-2, -4, -6, \dots$ (trivial zeros). RH states every other zero has $\operatorname{Re} s = \frac12$. Mathlib's `RiemannHypothesis` (referenced directly by [`riemannHypothesis`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4)) encodes this directly.
2. Prime-counting error: with Chebyshev's $\psi(x) = \sum_{p^k \le x} \log p$, the prime number theorem gives $\psi(x) \sim x$; RH is equivalent to $\psi(x) = x + O(\sqrt{x}\log^2 x)$.
3. Spectrum of waves: the Riemann–von Mangoldt explicit formula
   $$\psi(x) = x - \sum_\rho \frac{x^\rho}{\rho} - \log(2\pi) - \tfrac12\log(1 - x^{-2})$$
   writes each zero $\rho = \beta + i\gamma$ as a wave $x^\beta e^{i\gamma\log x}$ in $\log x$. Functional-equation symmetry pairs $\beta + i\gamma$ with $1 - \beta + i\gamma$, so $\beta = \frac12$ is optimal; any off-line zero creates a growing mode $x^\beta$ that eventually dominates $\sqrt{x}$. The Fourier analogy is informal: the transform is in $\log x$, $\sum_\rho x^\rho/\rho$ converges only conditionally, and $\sqrt{x}$ hides log factors.

### Why 165 Years of Attacks Stalled

| Line of Attack | Best Result | Bottleneck |
|---|---|---|
| Zero-free region near $\operatorname{Re} s = 1$ | Vinogradov–Korobov (1958): $\sigma > 1 - c/(\log t)^{2/3+\varepsilon}$ | Shrinks to $0$ as $t \to \infty$; no fixed-width strip proved classically. |
| Proportion of zeros on the line | Selberg (1942), Levinson (1974), Conrey (1989): $\approx 5/12$ | Mollifier methods hit a ceiling well below $100\%$. |
| Numerical verification | Platt–Trudgian (2021): all zeros to height $\gamma \le 3\cdot 10^{12}$ | A rogue zero at $\beta = 0.6, \gamma = 3\cdot 10^{12}$ only exceeds $\sqrt{x}$ beyond $x \approx 10^{122}$ in $\psi(x)$ ($2x^\beta/\gamma$) and beyond $x \approx 10^{233}$ in `Gz(x)` ($2x^\beta/\gamma^2$ vs band $0.0462\sqrt{x}$). |
| Hilbert–Pólya / Weil positivity | Random-matrix statistics (Montgomery 1973); Weil quadratic form $W \ge 0$ (1952) | No operator or geometric source of positivity found over $\mathbb{Z}$. |
| Finite-field analogue | Hasse (1933), Weil (1940s), Stepanov (1969), Deligne (1974) | Relies on Frobenius $x \mapsto x^q$ (missing over $\mathbb{Q}$). |
| Pure analysis | — | Impossible: Davenport–Heilbronn has a functional equation and off-line zeros, lacking an Euler product. |

The de Bruijn–Newman constant satisfies $\Lambda \ge 0$ (Rodgers–Tao 2020) and RH $\iff \Lambda \le 0$.

## 2. Cryptography Impact of Dirichlet-Only GRH

A proof of RH or GRH breaks no cryptosystem (RSA, ECC, and lattices already assumed it). What becomes unconditional depends on **which** GRH was formalized — here, **Dirichlet $L$-functions only** ([statement definitions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Statements.lean#L6-L16)):

| Computational Result | Hypothesis Needed | Covered Here? |
|---|---|---|
| Miller deterministic primality test: bases $\le 2\ln^2 n$ (Miller 1976, Bach 1990) | Dirichlet GRH | **Yes** |
| Smallest quadratic non-residue mod $p$ is $< 2\ln^2 p$ (deterministic Tonelli–Shanks, Bach 1990) | Dirichlet GRH | **Yes** |
| Primes in arithmetic progressions with $\sqrt{x}$ error; least prime $\equiv a \pmod q \ll (\varphi(q)\log q)^2$ | Dirichlet GRH | **Yes** |
| Class-group generator bound $\le 12\ln^2\lvert\Delta\rvert$ general / $6\ln^2\lvert\Delta\rvert$ quadratic (Bach 1990; index calculus, CSIDH-style class groups) | **Hecke / Dedekind** GRH | **No** |
| Artin's primitive-root conjecture (Hooley 1967) | **Non-abelian Dedekind** GRH | **No** |
| Expansion of *ordinary* elliptic-curve isogeny graphs (Jao–Miller–Venkatesan 2009; supersingular graphs are Ramanujan unconditionally) | **CM Hecke** GRH | **No** |

## 3. Top Observable `Gz(x)` & Proof Intuition

The proof's top ramp-weighted prime sum is defined in [`Gz`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/StatementOC.lean#L11-L13):
$$G_z(x) = \sum_{n \le x} \Lambda(n)\left(\frac{x}{n} - 1\right) - x\log x + (1 + \gamma)x$$
Its explicit formula (derived from $(-\zeta'(s)/\zeta(s))\cdot x^s/(s(s-1))$) is:
$$G_z(x) = \log(2\pi) - \sum_\rho \frac{x^\rho}{\rho(\rho - 1)} - \sum_{n \ge 1} \frac{x^{-2n}}{2n(2n+1)}$$
Unlike $\psi(x)$, the zero sum converges **absolutely**, the trivial-zero tail is bounded by $(1 - \ln 2)/x^2 < 0.31/x^2$, and under RH $|G_z(x) - \log(2\pi)| \le (2 + \gamma - \log 4\pi)\sqrt{x} \approx 0.046191\,\sqrt{x}$. Note: [`Formalism.Gchi`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/StatementOC.lean#L20) is dead code; all 3 live character observables guard $\chi = 1$.

### Architectural Summary (Top to Bottom)

1. Endpoints reduce through the functional-equation bridge (`58,857` decls, `31` project) to [`allChi`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Supplements/Kernels/MainTheorems.lean#L7) (nonvanishing on $\operatorname{Re} s > \frac12$).
2. A one-sided upper bound $\mathrm{Gm}_\Lambda(y) \le y^\theta$ holding only on arbitrarily late multiplicative windows $[Y, Y^{3/2}]$ forces zero-freeness on $\operatorname{Re} s > \theta$ (see [the explicit-formula trace](../analysis/explicit_formula_bridge.md)).
3. Over $\mathbb{F}_q$, Stepanov bounds points with a degree budget (degree $D$ vanishing to order $m$ at each point gives $\le D/m$ points). Over $\mathbb{Z}$, $\log|N| \ge \sum_p v_p(N)\log p$ swaps degree for log-size and vanishing order for $p$-adic valuation (Chebyshev 1850 used $\binom{2n}{n} < 4^n$). The [announcement note](https://alpo.ge/remark.pdf) sketches chaining $m \approx \sqrt{x}$ theta lifts between totally definite unitary groups to balance error costs $x/m + m$ via Bost's slope inequality. Where the analogy breaks: `solution.ndjson.zst` contains `0` Stepanov auxiliary-polynomial or sixfold-`GL₅` hits; the live proof instead uses `ThetaIntegralsAgree`, `ColumnChain`, `Behrend`, and `VWin` (see [the contract and gap audit](../analysis/deep_followup_audit.md)).
4. Pillar B (`Row0b`, `95,102` decls), Pillar C ([`VWin`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L49), `92,705` decls, 100% unfolded to Mathlib), Pillar D (`SelfIntersectionVolumeEstimates`, `80,720` decls), and all `3` fields of `OpenLiteratureStatements` are proved inside the archive without axioms.

| Branch | Role in the Proof | Source |
|---|---|---|
| Analytic number theory | `Gz(x)` explicit formula, localized Landau criterion | `solution.ndjson` + classical |
| Automorphic forms / theta lifts | `ColumnChain`, `ThetaIntegralsAgree`, `LocalMatching`, definite unitary groups | `solution.ndjson` + author note |
| Arakelov geometry | `SelfIntersectionVolumeEstimates`, Moriwaki bigness, Bost slope | `solution.ndjson` + author note |
| Iwasawa theory / Galois cohomology | `VWin` (`Ш¹` length bound), Kato Euler systems, `Sp(4)`/`U(3)`, Taylor–Wiles patching | `solution.ndjson` + author note |
| Langlands program | Odd-rank étale Galois reps (`Row0b`), `tLiftK`, `recTExists` | `solution.ndjson` |
| Additive combinatorics | Behrend thick host (`hostThickExists`, `15` live decls) | `solution.ndjson` + author note |

## 4. Interactive Diagrams and Blueprints

For kernel-extracted architecture diagrams of the declaration graph, see the [Diagrams](#circuit) tab; for node-by-node contract summaries across the `999` largest dominator subtrees, see [Blueprints](#blueprints).
