# Chapter 4 — Syntax

Lean directory: [`../Syntax/`](../Syntax/)

[← Back to README](../../README.md)

---

## 4.1 Denotational semantics of expressions

**Definition 4.1.1** — Expression syntax

| | |
|---|---|
| Lean | `Expr` |
| File | [`Syntax/Expressions.lean`](../Syntax/Expressions.lean) |

**Definition 4.1.2** — Denotational semantics ⟦·⟧

| | |
|---|---|
| Lean | `sem` |
| File | [`Syntax/Expressions.lean`](../Syntax/Expressions.lean) |

---

## 4.2 Expression derivatives

**Definition 4.2.1** — Expression derivatives $D_a$, $D^{\mathrm{\rhd}}_a$

| | |
|---|---|
| Lean | `D`, `DLA` (mutual) |
| File | [`Syntax/Derivatives.lean`](../Syntax/Derivatives.lean) |


**Theorem 4.2.1** — Correctness of expression derivatives  
⟦$D_a$ r⟧ = $\mathrm{der}_a$ ⟦r⟧ and ⟦$D^{\mathrm{\rhd}}_a$ r⟧ = $\mathrm{der}^{\mathrm{\rhd}}_a$ ⟦r⟧

| Part | Lean | File |
|------|------|------|
| Match derivative | `der_correct` | [`Syntax/DerivativeCorrectness.lean`](../Syntax/DerivativeCorrectness.lean) |
| Lookahead derivative | `derLA_correct` | same |


**Definition 4.2.2** — Iterated derivatives $D_w$, $D^{\mathrm{\rhd}}_w$

| | |
|---|---|
| Lean | `D_word`, `DLA_word` |
| File | [`Syntax/Derivatives.lean`](../Syntax/Derivatives.lean) |

**Theorem 4.2.2** — Correctness of iterated derivatives

| Part | Lean | File |
|------|------|------|
| Match | `der_word_correct` | [`Syntax/DerivativeCorrectness.lean`](../Syntax/DerivativeCorrectness.lean) |
| Lookahead | `derLA_word_correct` | same |


**Definition 4.2.3** — Existential derivative $\mathrm{x}D_a r = D_a r + D^{\mathrm{LA}}_a r$

| | |
|---|---|
| Lean | Inline: `(D a r) + (DLA a r)` inside `xD` |
| File | [`Syntax/Derivatives.lean`](../Syntax/Derivatives.lean) |

**Definition 4.2.4** — Iterated existential derivative \(\mathrm{x}D_w\)

| | |
|---|---|
| Lean | `xD` |
| File | [`Syntax/Derivatives.lean`](../Syntax/Derivatives.lean) |


**Theorem 4.2.3** — Correctness of existential derivatives  
⟦$\mathrm{x}D_w$ r⟧ = $\mathrm{xder}_w$ ⟦r⟧

| | |
|---|---|
| Lean | `xder_correct` |
| File | [`Syntax/DerivativeCorrectness.lean`](../Syntax/DerivativeCorrectness.lean) |

---

## 4.3 Expression nullability

**Definition 4.3.1** — Expression nullability $\mathrm{N}(r)$

| | |
|---|---|
| Lean | `N` |
| File | [`Syntax/Nullability.lean`](../Syntax/Nullability.lean) |
| Status | ✓ |

*Auxiliary operators (part of Def. 4.3.1):* `MatchSet`, `matchesOfPlus` ($\cdot_N$), `matchesOfLA` ($\rhd_N$), `matchesOfStep` ($\uparrow_N$), and corresponding helpers for $\cup,\cap,\setminus,{}^*$.

**Theorem 4.3.1** — Correctness of nullability  
$n \in N(r) \Leftrightarrow \mathrm{nullable}_n$ ⟦r⟧

| | |
|---|---|
| Lean | `nullability_correct` |
| File | [`Syntax/NullabilityCorrectness.lean`](../Syntax/NullabilityCorrectness.lean) |
