# Chapter 3 — Semantics

Lean directory: [`../Semantics/`](../Semantics/)

[← Back to guide index](../../README.md)

---

## 3.1 Languages of structured words

**Definition 3.1.1** — Structured words  
\(W = (\Sigma^+ \times \Sigma^*) \uplus (\mathbb{N} \times \Sigma^*)\).

| | |
|---|---|
| Lean | `Word` |
| File | [`Semantics/StructuredWords.lean`](../Semantics/StructuredWords.lean) |

---

## 3.2 Language derivatives

**Definition 3.2.1** — Match derivative $\mathrm{der}_a$

| | |
|---|---|
| Lean | `der` |
| File | [`Semantics/Derivatives.lean`](../Semantics/Derivatives.lean) |

**Definition 3.2.2** — Lookahead derivative $\mathrm{der}^{\rhd}_a$

| | |
|---|---|
| Lean | `derLA` |
| File | [`Semantics/Derivatives.lean`](../Semantics/Derivatives.lean) |

**Lemma 3.2.1** — $\mathrm{der}_a (\mathrm{der}^{\rhd}_a L) = \empty$

| | |
|---|---|
| Lean | `der_derLA_empty` |
| File | [`Semantics/Derivatives.lean`](../Semantics/Derivatives.lean) |

**Definition 3.2.3** — Iterated derivatives $\mathrm{der}_w$ and  $\mathrm{der}^{\rhd}_w$

| | |
|---|---|
| Lean | `der_word`, `derLA_word` |
| File | [`Semantics/Derivatives.lean`](../Semantics/Derivatives.lean) |
| Status | ✓ |

**Definition 3.2.4** — Indexed nullability $\mathrm{nullable}_n$

| | |
|---|---|
| Lean | `nullable_n` |
| File | [`Semantics/Derivatives.lean`](../Semantics/Derivatives.lean) |

**Theorem 3.2.1** — Derivative characterization of membership

| Part | Lean | File |
|------|------|------|
| (1) $(x,y) \in L \Leftrightarrow \mathrm{nullable}_{\|y\|}(\mathrm{der}^{\rhd}_y(\mathrm{der}_x L))$ | `membership_inl_iff_nullable` | [`Semantics/DerivativeAcceptance.lean`](../Semantics/DerivativeAcceptance.lean) |
| (2) $(n,y) \in L \Leftrightarrow \mathrm{nullable}_{n+\|y\|}(\mathrm{der}^{\rhd}_y L)$ | `membership_inr_iff_nullable` | same |

**Definition 3.2.5** — Existential derivative $xder_a$

| | |
|---|---|
| Lean | `xder` |
| File | [`Semantics/Derivatives.lean`](../Semantics/Derivatives.lean) |


**Theorem 3.2.2** — Existential derivative and indexed nullability

| | |
|---|---|
| Lean | `xder_nullable_iff` |
| File | [`Semantics/DerivativeAcceptance.lean`](../Semantics/DerivativeAcceptance.lean) |

---

## 3.3 Language operators

**Definition 3.3.1** — Structured concatenation $\mathrm{wc}$

| | |
|---|---|
| Lean | `wc` |
| File | [`Semantics/Operators.lean`](../Semantics/Operators.lean) |

**Definition 3.3.2** — Language operators

| Operator (thesis) | Lean | File |
|-------------------|------|------|
| $\emptyset$ | `empty` / `∅` | [`Semantics/Operators.lean`](../Semantics/Operators.lean) |
| $\mathrm{I}$ | `unit` / `I` | same |
| $\mathrm{T}$ | `top` / `T` | same |
| $\mathrm{Symb}(a)$ | `symb` / `#` | same |
| $\cup, \ \cap, \ \setminus, \ \cdot \ , \ {}^*$ | `union`, `intersection`, `complement`, `concat`, `star` | same |
| $\mathrm{LA}$ | `la` / `▷` | same |
| $\mathrm{Step}$ | `step` / `▹` | same |

---

## 3.4 Derivative laws for structured languages

**Proposition 3.4.1** — Derivative laws for structured languages

| | |
|---|---|
| Lean | All identities in namespace `DerLaws` |
| File | [`Semantics/DerivativeLaws.lean`](../Semantics/DerivativeLaws.lean) |

All match- and lookahead-derivative laws from the proposition are proved in that file.

---

## 3.5 Algebraic properties of structured languages

**Proposition 3.5.1** — Basic algebraic laws (equations (3.1)–(3.15))

| Eq. | Law (informal) | Lean |
|-----|----------------|------|
| (3.1) | Union associativity | `union_assoc` |
| (3.2) | Union commutativity | `union_comm` |
| (3.3) | Union idempotence | `union_idempotent` |
| (3.4) | Union identity | `union_identity` |
| (3.5) | Intersection associativity | `intersection_assoc` |
| (3.6) | Intersection commutativity | `intersection_comm` |
| (3.7) | Intersection idempotence | `intersection_idempotent` |
| (3.8) | $T \cap L = L$ | `intersection_top` |
| (3.9) | $L \setminus \emptyset = L$ | `complement_empty` |
| (3.10) | $L \setminus L = \emptyset$ | `complement_self` |
| (3.11) | $L \setminus T = \emptyset$ | `complement_top` |
| (3.12)–(3.13) | Concatenation distributivity | `concat_distrib_union_left`, `concat_distrib_union_right` |
| (3.14) | $\emptyset \cdot L = L \cdot \emptyset = \emptyset$ | `empty_concat_left`, `empty_concat_right` |
| (3.15) | $L^* = I \cup L \cdot L^*$ | `star_unfold` |

| | |
|---|---|
| File | [`Semantics/AlgebraicLaws.lean`](../Semantics/AlgebraicLaws.lean) |

**Proposition 3.5.2** — Basic properties of $\mathrm{Step}$

| Part | Lean | File |
|------|------|------|
| (3.16) monotonicity | `step_motonicity` | [`Semantics/AlgebraicLaws.lean`](../Semantics/AlgebraicLaws.lean) |
| (3.17) non-idempotence | `step_non_idempotence` | same |

**Proposition 3.5.3** — Left identity $ \ \mathrm{I} \cdot L = L$

| | |
|---|---|
| Lean | `concat_left_identity` |
| File | [`Semantics/AlgebraicLaws.lean`](../Semantics/AlgebraicLaws.lean) |

**Proposition 3.5.4** — Failure of right identity

| | |
|---|---|
| Lean | `concat_right_identity_failure` |
| File | [`Semantics/AlgebraicLaws.lean`](../Semantics/AlgebraicLaws.lean) |

**Proposition 3.5.5** — Restricted right identity on $W_0$

| | |
|---|---|
| Lean | `concat_right_identity_restricted₁`, `concat_right_identity_restricted₂` |
| File | [`Semantics/AlgebraicLaws.lean`](../Semantics/AlgebraicLaws.lean) |

**Proposition 3.5.6** — Restricted associativity on $W_0$

| | |
|---|---|
| Lean | `concat_assoc_restricted` |
| File | [`Semantics/AlgebraicLaws.lean`](../Semantics/AlgebraicLaws.lean) |

**Theorem 3.5.1** — Structured language decomposition on $W_0$

| | |
|---|---|
| Lean | `structuredLanguage_decomposition` |
| File | [`Semantics/Decomposition.lean`](../Semantics/Decomposition.lean) |
