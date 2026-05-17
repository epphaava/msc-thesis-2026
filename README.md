# Matching algorithm based on derivatives of regular expressions

**Author:** Epp Haavasalu  
**Supervisor:** Hendrik Maarand  
**Institution:** Tallinn University of Technology

## Summary

This repository contains a Lean 4 formalization of the thesis. The thesis develops a derivative-based framework for regular expression matching with positional information and lookahead, using structured words instead of classical strings. The main deliverable is a left-to-right algorithm that computes all valid match end positions for a fixed start position in one pass. Definitions, derivative laws, syntactic derivatives, nullability, and correctness results are mechanized in Lean.

## Where things live

| Thesis | Lean |
|--------|------|
| Ch. 3 Semantics | [`Thesis/Semantics/`](Thesis/Semantics/) — [guide](Thesis/guides/Chapter_3_Semantics.md) |
| Ch. 4 Syntax | [`Thesis/Syntax/`](Thesis/Syntax/) — [guide](Thesis/guides/Chapter_4_Syntax.md) |
| Ch. 5 Algorithm | [`Thesis/Algorithm.lean`](Thesis/Algorithm.lean) — [guide](Thesis/guides/Chapter_5_Algorithm.md) |

Each chapter guide lists definitions, theorems, and examples from the paper with their Lean names and files.

Definition numbers in Lean comments match the thesis where marked (e.g. `-- Definition 3.2.1`).

## Building

Requires [Lean 4](https://lean-lang.org/). The version is pinned in [`lean-toolchain`](lean-toolchain).

**Recommended:** install [elan](https://github.com/leanprover/elan), then from the repository root:

```bash
lake update
lake build
```

This checks the main formalization (Ch. 3–5) and the examples in [`Thesis/Examples.lean`](Thesis/Examples.lean).

Optional:

```bash
lake build Thesis.Extra
```

**Editor:** [VS Code](https://code.visualstudio.com/) with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4). Step-by-step setup: [Lean 4 installation guide](https://lean-lang.org/lean4/doc/setup.html).

**CI:** GitHub Actions runs `lake build` on every push and pull request.
