# Chapter 5 — Matching algorithm

[← Back to README](../../README.md)

---

## 5.1 Implementation

**Definition 5.1.1** — Bounded match positions $\mathrm{matchesUpTo}(S, n)$

| | |
|---|---|
| Lean | `Algorithm.matchesUpTo` |
| File | [`Algorithm.lean`](../Algorithm.lean) |

**Definition 5.1.2** — Matching algorithm $\mathrm{findAllMatches}(r, w)$

| | |
|---|---|
| Lean | `Algorithm.findAllMatches` |
| File | [`Algorithm.lean`](../Algorithm.lean) |

**Theorem 5.1.1** — Correctness of the matching algorithm  
$n \in \mathrm{findAllMatches}(r,w) \Leftrightarrow \mathrm{nullable}_n$ ⟦$\mathrm{x}D_w$ r⟧ (for $n \le |w|$)

| | |
|---|---|
| Lean | `algorithm_correctness` |
| File | [`Algorithm.lean`](../Algorithm.lean) |


---

## 5.3 Example

| | |
|---|---|
| File | [`Examples.lean`](../Examples.lean) |
