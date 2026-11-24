# Proof-Graph Analysis Methods and Tooling

`leanre` analyzes large Lean 4 proofs like stripped binaries; for extracted outputs, see [kernel extraction](../docs/KERNEL.md), [signature-matching indexing (IDA FLIRT analogue)](../docs/FLIRT.md), [the TCB audit](../analysis/tcb_and_contracts.md), and [the whole-proof synthesis](../analysis/SYNTHESIS.md).

## 1. Framing a Mega-Proof as a Stripped Binary

| Artifact | Size | RE Analogue | Questions It Answers |
|---|---|---|---|
| Source tree (`src/`) | `175,187` files, `1.03` GB, `17,374,215` lines, `0` comments | Decompiler output with misleading symbol names | Module import graph, text clones, lexical red flags, signatures. |
| `solution.ndjson.zst` (`lean4export` v3.1.0) | `61.57` GB unpacked (`7.7` GB `.zst`), `1,468,418` folded records / `1,484,733` constants | Stripped, linked binary (only what the 5 roots reach) | Exact declaration graph (`114,115,002` typed edges), term sizes, exact dead-code complement (`28,904` zero-kernel files). |
| `challenge.ndjson.zst` | `351` MB unpacked (`47` MB `.zst`), `51,692` records | Public interface spec + linked definitions | Semantic TCB of the 5 headline statements (`2,570` definitions). |
| Checker logs | KB | Profiler traces | Kernel hot spots (`decide +kernel`, copy macros). |
| [Announcement note](https://alpo.ge/remark.pdf) | 4 pages | Vendor marketing sheet | Author intent and timeline (author notes parts paraphrase an AI summary). |

Derived corpus metrics: `99.2` lines/file, `6.06` keyword decls/file, `16.4` lines/decl, `59.3` B/line; `~60×` elaboration blow-up (`61.57` GB / `1.03` GB); statement surface is `3.52%` of proof surface (`51,692 / 1,468,418` `con-leche` folded records). All `175,187` files end with `\n` (`17,549,402` in `drew2apps` adds one empty element per file via `split('\n')`).

### Why proof graphs differ from call graphs

1. **A proof graph is an AND-graph.** Deleting any reachable lemma breaks typechecking, so naive min-cut over all nodes is ill-posed. Graph structure instead surfaces **encapsulation boundaries**: statements whose retained dominator mass is large behind a short signature.
2. **Type edges vs. value edges answer different questions.** Following `type` references from the five roots yields the **WHAT** closure (`51,692` records, `2,570` defs — Layer 2 TCB). Following `type + value` yields the **WHY** closure (`1,468,414` live records — Layer 3 architecture).
3. **Dependency-injection signatures hide logic from the call graph.** In [MainConclusion](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L7-L11), `everyCharacter_of_row` takes `Row0b` as a hypothesis argument and `everyCharacter` discharges it one level up. A constant-reference graph shows producer and consumer as siblings; extracting Horn clauses (`A ∧ B ⟹ C`) from Prop-typed binders recovers the logical spine.
4. **Folders and names are untrusted input.** Directory paths (`AbelianVarietyTheory`) and namespaces (`GlobalTheory.T.*`, which contains `38,194` 1-node renaming wrappers) act like an obfuscated symbol table.

## 2. Static-Analysis Passes ("Ghidra for Lean")

| Pass | RE Analogue | Method & Implemented Status |
|---|---|---|
| **Streaming export loader** | Disassembler / loader | Rust `leanre/kernel-rs/` streams `solution.ndjson.zst` in ~8.5 min at `12.3` GiB peak RSS (`0` discrepancy vs `con-leche` and `nanoda`), folding `_proof_*` / `match_*` auxes as needed ([kernel docs](../docs/KERNEL.md)). |
| **Per-root reachability** | Dead-code stripping | Separates the `58,857`-decl bridge outside `allChi` from the `1,409,557`-decl core and identifies `28,904` zero-kernel files (`28,471` unused files, `2.36M` lines). |
| **Dominators & retained mass** | Heap-profiler retained size | Cooper–Harvey–Kennedy immediate dominators on the live DAG yield the trunk, fork, 4 pillars, and `331,598`-decl shared diamond ([whole-proof synthesis](../analysis/SYNTHESIS.md)). |
| **Horn skeleton & discharge map** | Data-flow over function pointers | Extracts `Prop` hypothesis → conclusion rules (`Row0b ⟹ VWin`, `Green ∧ VWin ∧ Hyps ⟹ ZeroFreeAll`) and flags unused hypothesis binders (`152/195` `*_of_literature` theorems ignore `O`, `OpenImageCondition` `0/62`, `LiteratureCMHypothesis` `0/11`). |
| **Signature hashing & matching index** | IDA FLIRT (signature-matching index) / BinDiff | Merkle DAG type hashes (`k1n`/`k1a`) + header fingerprinting separate `16` bulk folder remappings (`125,598` modules) from `20,692` misfiles (`84.21%` extreme-outlier precision) and match against `312,849` signatures from 7 Apache-2.0 Lean corpora ([signature-matching index](../docs/FLIRT.md), [corpus matching](../docs/FLIRT_TIER2.md)). |
| **Checker-log profiling** | Hot-spot profiler | `con-leche` slowest 5: `lam_copy` (`55.2s`), `sigSpan_copy` (`40.3s`), `PI.PC.loop_run._proof_1_1` (`35.1s`, live from `SmallLoop`), `factorial_ladder_one_forty_one._proof_1_1` (`25.0s`), `PrimeRecip.table_ok._proof_1_1` (`17.2s`). |
| **Bypass taint & junk-value lint** | Taint / UB analysis | Tracks `kexactB`, `kcopy`, `CutCptCopy`, and `decide +kernel` (`14` live files) through `kernel.db`; checks total-function divisions (`Formalism.Gchi` is dead code; all 3 live `gChi` defs guard `χ = 1`). |

## 3. Ten-Layer TCB Threat Model

The realistic adversary is misplaced confidence: overstating what the theorems say at the top, or overstating checker independence at the bottom.

| # | Layer | Failure Mode | Verified Status |
|---|---|---|---|
| 0 | **Reader's model** | Assuming Extended RH or confusing with Masullo's draft. | Strictly **Dirichlet $L$-functions** over $\mathbb{Q}$; no Dedekind or higher-rank $L$-functions. |
| 1 | **Statement text** | Vacuous hypothesis or `ℕ` division bug. | 5 roots match `Challenge.lean` bit-for-bit; `1/2` is `@HDiv.hDiv ℝ`; `RiemannZetaZerosOnLine = RiemannHypothesis` by `rfl`. |
| 2 | **Definitional closure** | Broken Mathlib definition deep in the spec. | `2,570` defs in 5-root cone (`0` project defs inside `riemannHypothesis`'s `2,448`-def cone); spot-checked `riemannZeta`, `completedRiemannZeta`, `LFunction` in `mathlib4@0df444a3`. |
| 3 | **Elaboration** | Shadowed notation or implicit coercions. | `autoImplicit = false`, `0` global notations, `Challenge.lean` compared at kernel-term level. |
| 4 | **Axioms** | Hidden assumption (`sorryAx`, `ofReduceBool`, custom). | Strictly `[propext, Classical.choice, Quot.sound]`; `0` custom axioms. |
| 5 | **Kernel** | Runtime soundness bug (`v4.33.1` predates `v4.34.1` `#15241`/`#15289`). | Mitigated by non-Lean kernels (`nanoda`, `con-leche`) plus `lean4lean` and `leanchecker`. |
| 6 | **Exporter & shared spec** | Export-based checkers share `lean4export`. | Diversity is **2 artifact paths** (`lean4export` vs `.olean`) × multiple kernels, not 5 fully independent stacks. |
| 7 | **Metaprogramming** | Elaborator-bypass tactics (`kexactB`, `kcopy`, `CutCptCopy`). | Kernel still checks every emitted term; `0` hits of `unsafe`, `implemented_by`, `extern`, `skipKernelTC`, `native_decide`. |
| 8 | **Build pipeline** | Arbitrary build-time code execution; non-reproducible `.olean`s. | Sandboxed builds (`podman --network none`); only `76,968/175,187` `.olean` hashes match across builds (`51/51` sampled diffs have identical proof terms). Trust export replays, not `.olean` hashes. |
| 9 | **Supply chain** | Tampered Mathlib, toolchain, or archive. | `121,742` dependency files match official copies; pin joined archive SHA-256 (`9631b4f0…9c7fc`). |

## 4. Inspection Protocol

1. Query `kernel.db` first for questions answered deterministically (liveness, dominators, axioms, Horn edges).
2. Read `def`/`structure`/`theorem` headers before proof bodies, and avoid treating declaration names as evidence of mathematical content.
3. Separate claims by falsifiability: structural claims go to graph checks, paraphrases to Lean equivalence checks, and mathematical identifications to expert review.
4. Strip project identifiers against a Mathlib/Lean allowlist (`507,623` tokens) and compare blinded vs. unblinded labels. Adding 1–2-hop kernel contract unfolding raised blinded agreement on concrete domains `48.1% → 63.0%` (with zero identifier leaks).
5. Key portable JSONL annotations by `(name, sighash)` so notes survive simplification and renames ([annotation packs spec](../docs/ANNOTATION_PACKS.md)).

## 5. Synthetic Graph Validation Findings

The synthetic graph harness (`prototypes/sim_proof_re.py`) validated graph algorithms against brute-force oracles (`786` dominator, `786` articulation-point, `1,230` bridge, and `213` min-cut checks; `0` failures) before scaling to the real export:

- Undirected articulation points fail on proof graphs (`44` guarding ≥10 nodes vs `23,557` directed dominators at full scale); directed dominators are required.
- High path-flow centrality finds plumbing (`188/200` top nodes retain `<0.5%` of the proof); rank chapters by retained dominator mass, not fan-in.
- Single dominators capture the main branches, then flatten into a long tail (`39.5%` at `k = 3,000`), matching the real export where `331,598` live decls (`22.6%`) sit inside the shared diamond under `everyCharacter`.
- The raw source tree is `1.03` GB (`17.37M` lines); restricting bulk static passes to declaration headers and kernel signatures cuts reading volume by roughly an order of magnitude while reserving manual reading for the spine.
