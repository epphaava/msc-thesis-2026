import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators

namespace AlgebraicLaws

open StructuredWords
open Operators

-- Proposition 3.5.1 (Basic algebraic laws).

-- Equation (3.1)
theorem union_assoc (K L M : Lang α) : K ∪ (L ∪ M) ≐ (K ∪ L) ∪ M := by intro w; simp [union, or_assoc]

-- Equation (3.2)
theorem union_comm (K L : Lang α) : K ∪ L ≐ L ∪ K := by intro w; simp [union, or_comm]

-- Equation (3.3)
theorem union_idempotent (L : Lang α) : L ∪ L ≐ L := by intro w; simp [union]

-- Equation (3.4)
theorem union_identity (L : Lang α) : L ∪ ∅ ≐ L := by intro w; simp [empty, union]

-- Equation (3.5)
theorem intersection_assoc (K L M : Lang α) : K ∩ (L ∩ M) ≐ (K ∩ L) ∩ M := by
  intro w; simp [intersection, and_assoc]

-- Equation (3.6)
theorem intersection_comm (K L : Lang α) : K ∩ L ≐ L ∩ K := by
  intro w; simp [intersection, and_comm]

-- Equation (3.7)
theorem intersection_idempotent (L : Lang α) : L ∩ L ≐ L := by intro w; simp [intersection]

-- Equation (3.8)
theorem intersection_top (L : Lang α) : T ∩ L ≐ L := by intro w; simp [top, intersection]

-- Equation (3.9)
theorem complement_empty (L : Lang α) : (L // ∅) ≐ L := by intro w; simp [empty, complement]

-- Equation (3.10)
theorem complement_self (L : Lang α) : (L // L) ≐ ∅ := by intro w; simp [complement, empty]

-- Equation (3.11)
theorem complement_top (L : Lang α) : (L // T) ≐ ∅ := by intro w; simp [top, complement, empty]

-- Equation (3.12)
theorem concat_distrib_union_left (p q r : Lang α) : p • (q ∪ r) ≐ (p • q) ∪ (p • r) := by
  intro w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩
      cases hy with
      | inl hy => left; exact ⟨x, y, hx, hy, hc⟩
      | inr hy => right; exact ⟨x, y, hx, hy, hc⟩
    . intro h
      cases h with
      | inl h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, hx, Or.inl hy, hc⟩
      | inr h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, hx, Or.inr hy, hc⟩
  | Sum.inr (n, v) =>
    constructor
    . intro ⟨x, y, hx, hy, ⟨n', x_sub, y_sub⟩⟩
      cases hy with
      | inl hy => left; exact ⟨x, y, hx, hy, ⟨n', x_sub, y_sub⟩⟩
      | inr hy => right; exact ⟨x, y, hx, hy, ⟨n', x_sub, y_sub⟩⟩
    . intro h
      cases h with
      | inl h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, hx, Or.inl hy, hc⟩
      | inr h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, hx, Or.inr hy, hc⟩

-- Equation (3.13)
theorem concat_distrib_union_right (p q r : Lang α) : (p ∪ q) • r ≐ (p • r) ∪ (q • r) := by
  intro w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩
      cases hx with
      | inl hx => left; exact ⟨x, y, hx, hy, hc⟩
      | inr hx => right; exact ⟨x, y, hx, hy, hc⟩
    . intro h
      cases h with
      | inl h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, Or.inl hx, hy, hc⟩
      | inr h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, Or.inr hx, hy, hc⟩
  | Sum.inr (n, v) =>
    constructor
    . intro ⟨x, y, hx, hy, ⟨n', x_sub, y_sub⟩⟩
      cases hx with
      | inl hx => left; exact ⟨x, y, hx, hy, ⟨n', x_sub, y_sub⟩⟩
      | inr hx => right; exact ⟨x, y, hx, hy, ⟨n', x_sub, y_sub⟩⟩
    . intro h
      cases h with
      | inl h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, Or.inl hx, hy, hc⟩
      | inr h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, Or.inr hx, hy, hc⟩

-- Equation (3.14)
theorem empty_concat_left (L : Lang α) : ∅ • L ≐ ∅ := by
  intro w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; simp [empty] at hx
    . intro h; simp [empty] at h
  | Sum.inr (n, v) =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; simp [empty] at hx
    . intro h; simp [empty] at h

theorem empty_concat_right (L : Lang α) : L • ∅ ≐ ∅ := by
  intro w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; simp [empty] at hy
    . intro h; simp [empty] at h
  | Sum.inr (n, v) =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; simp [empty] at hy
    . intro h; simp [empty] at h

-- Equation (3.15)
theorem star_unfold (l  : Lang α) :  l* ≐ I ∪ (l • l*) := by
  intro w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    . intro h
      cases h with
      | inConcat x y w hx hy hc => right; exact ⟨x, y, hx, hy, hc⟩
    . intro h
      cases h with
      | inl h => simp [unit] at h
      | inr h =>
        obtain ⟨x, y, hx, hy, hc⟩ := h
        cases hc with
        | inl h => obtain ⟨n, x_sub, y_sub⟩ := h; subst x y; trivial
        | inr h =>
          cases h with
          | inl h =>
            obtain ⟨x_sub, y_sub⟩ := h;
            exact star_help.inConcat (l := l) x y (Sum.inl ((hd, tl), v)) hx hy (by rw [x_sub, y_sub]; simp [wc])
          | inr h =>
            obtain ⟨xs, z, zs, htl, hx, hy⟩ := h; subst tl x y;
            exact star_help.inConcat (l := l) (Sum.inl ((hd, xs), z :: zs ++ v)) (Sum.inl ((z, zs), v)) (Sum.inl ((hd, xs ++ z :: zs), v)) hx hy (Or.inr (Or.inr ⟨xs, z, zs, rfl, rfl, rfl⟩ ))
  | Sum.inr (n, v) =>
    constructor
    . intro h
      cases h with
      | inUnit w h => left; trivial
      | inConcat x y w hx hy hc =>
        obtain ⟨n', x_sub, y_sub⟩ := hc; subst x y
        right; exact ⟨(Sum.inr (n + n', v)), (Sum.inr (n, v)), hx, hy, ⟨n', rfl, rfl⟩⟩
    . intro h
      cases h with
      | inl h => exact star_help.inUnit (l := l) n v
      | inr h =>
        obtain ⟨x, y, hx, hy, ⟨n', _, _⟩⟩ := h; subst x y;
        cases hy with
        | inUnit w h => exact star_help.inUnit (l := l) n v
        | inConcat x' y' w' hx' hy' hc' => obtain ⟨n'', x_sub, y_sub⟩ := hc'; subst y'; exact hy'


-- Proposition 3.5.2 (Basic properties of Step).

-- Equation (3.16)
theorem step_motonicity (L K : Lang α) : L ⊆ K → ▹L ⊆ ▹K := by
  intro h w
  match w with
  | Sum.inl ((hd, tl), v) => simp [step]
  | Sum.inr (n, v) => intro ⟨k, hn, hl⟩; exact ⟨k, hn, h (Sum.inr (k, v)) hl⟩

-- Equation (3.17)
theorem step_non_idempotence : ∃ L : Lang α, ¬ ▹▹L ≐ ▹L := by
  refine ⟨T, ?_⟩
  intro h
  have h₁ := h (Sum.inr (1, []))
  simp [step, top] at h₁


-- Proposition 3.5.3 (Left identity).
theorem concat_left_identity (L : Lang α) : I • L ≐ L  := by
  intro w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩
      cases hc with
      | inl h => obtain ⟨_, _, _⟩ := h; subst y; exact hy
      | inr h =>
        cases h with
        | inl h => obtain ⟨_, _⟩ := h; subst x; simp [unit] at hx
        | inr h => obtain ⟨_, _, _, _, _, _⟩ := h; subst x; simp [unit] at hx
    . intro h; exact ⟨(Sum.inr (0, hd :: tl ++ v)), Sum.inl ((hd, tl), v), by simp [unit], h, Or.inl ⟨0, rfl, rfl⟩⟩;
  | Sum.inr (n, v) =>
    cases n with
    | zero =>
      constructor
      . intro h; obtain ⟨_, y, _, hy, _, _, _⟩ := h; subst y; exact hy
      . intro h; exact ⟨(Sum.inr (0, v)), Sum.inr (0, v), by simp [unit], h, ⟨0, rfl, rfl⟩⟩
    | succ n =>
      constructor
      . intro ⟨_, y, _, hy, n', _, _⟩; subst y; exact hy
      . intro h; exact ⟨(Sum.inr (n + 1 + n.succ, v)), Sum.inr (n.succ, v), by simp [unit], h, ⟨n.succ, rfl, rfl⟩⟩


-- Proposition 3.5.4 (Failure of right identity).
theorem concat_right_identity_failure : ∃ (L : Lang α) (w : Word α), ¬ ((L • I) w = L w) := by
  let l : Lang α := fun w =>
    match w with
    | Sum.inr (n, _) => 0 < n
    | _ => False
  refine ⟨l, Sum.inr (0, []), ?_⟩
  intro h
  have h₁: (l • I) (Sum.inr (0, [])) := by exact ⟨Sum.inr (1, []), Sum.inr (0, []), by simp [l], by simp [unit], ⟨1, rfl, rfl⟩⟩
  have h₂ : ¬ l (Sum.inr (0, [])) := by simp [l]
  simp [h₁] at h; contradiction


-- Proposition 3.5.5 (Restricted identity law).
theorem concat_right_identity_restricted₁ (L : Lang α) : L ⊆ (T // step T) →  (I • L) ≐ (L • I)  := by
  intro lang_h w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩
      cases hc with
      | inl h => obtain ⟨_, _, y_sub⟩ := h; exact ⟨y, Sum.inr (0, v), hy, by simp [unit], Or.inr (Or.inl ⟨by rw [y_sub], rfl⟩)⟩
      | inr h =>
        cases h with
        | inl h => obtain ⟨_, _⟩ := h; subst x; simp [unit] at hx
        | inr h => obtain ⟨_, _, _, _, _, _⟩ := h; subst x; simp [unit] at hx
    . intro ⟨x, y, hx, hy, hc⟩
      cases hc with
      | inl h => obtain ⟨_, _, _⟩ := h; subst y; simp [unit] at hy
      | inr h =>
        cases h with
        | inl h => obtain ⟨x_sub, y_sub⟩ := h; exact ⟨Sum.inr (0, hd :: tl ++ v), x, by simp [unit], hx, Or.inl ⟨0, rfl, by rw [x_sub]⟩⟩
        | inr h =>
          obtain ⟨_, _, _, _, _, y_sub⟩ := h
          rw [y_sub] at hy; simp [unit] at hy
  | Sum.inr (n, v) =>
    cases n with
    | zero =>
      constructor
      . intro ⟨x, y, hx, hy, ⟨n, x_sub, y_sub⟩⟩; exact ⟨y, Sum.inr (0, v), hy, by simp [unit], ⟨0, y_sub, rfl⟩⟩
      . intro ⟨x, y, hx, hy, ⟨n, x_sub, y_sub⟩⟩; refine ⟨Sum.inr (0 + n, v), x, by simp [unit], hx, ⟨n, rfl, ?_⟩⟩
        cases n with
        | zero => exact x_sub
        | succ n => have := lang_h x hx; rw [x_sub] at this; simp [complement, step, top] at this
    | succ n =>
      simp [subset] at lang_h
      simp [concat, wc]
      constructor
      . intro ⟨_, _, h, _⟩; have := lang_h (Sum.inr (n.succ, v)) h; simp [complement, step, top] at this
      . intro ⟨x, hx, _, n', _⟩; have := lang_h x hx; subst x; simp [complement, step, top] at this

theorem concat_right_identity_restricted₂ (L : Lang α) : L ⊆ T // (step T) →  (I • L) ≐ L  := by
  intro lang_h w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩
      cases hc with
      | inl h => obtain ⟨_, _, y_sub⟩ := h; rw [y_sub] at hy; exact hy
      | inr h =>
        cases h with
        | inl h => obtain ⟨_, _⟩ := h; subst x; simp [unit] at hx
        | inr h => obtain ⟨_, _, _, _, _, _⟩ := h; subst x; simp [unit] at hx
    . intro h; exact ⟨Sum.inr (0, hd :: tl ++ v), Sum.inl ((hd, tl), v), by simp [unit], h, Or.inl ⟨0, rfl, rfl⟩⟩
  | Sum.inr (n, v) =>
    cases n with
    | zero =>
      constructor
      . intro ⟨_, y, _, hy, ⟨_, _, y_sub⟩⟩; rw [y_sub] at hy; exact hy
      . intro h; refine ⟨Sum.inr (0, v), Sum.inr (0, v), by simp [unit], h, ⟨0, rfl, rfl⟩⟩
    | succ n =>
      simp [subset] at lang_h
      simp [concat, wc]
      constructor
      . intro ⟨_, _, h, _⟩; have := lang_h (Sum.inr (n.succ, v)) h; simp [complement, step, top] at this
      . intro h; have := lang_h (Sum.inr (n.succ, v)) h; simp [complement, step, top] at this


-- Proposition 3.5.6 (Restricted associativity).
theorem concat_assoc_restricted (P Q R : Lang α) : ([P, Q, R] ⊆ (T // step T))  →  P • (Q • R) ≐ (P • Q) • R := by
  simp [subsetAll]
  intro hp hq hr w
  simp [subset] at hp hq hr
  match hw : w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    . intro ⟨x, yz, hx, hyz, hc₁⟩
      obtain ⟨y, z, hy, hz, hc₂⟩ := hyz
      cases hc₁ with
      | inl hc₁ =>
        obtain ⟨n', x_sub, _⟩ := hc₁; subst yz;
        cases n' with
        | zero =>
          cases hc₂ with
          | inl hc₂ =>
            obtain ⟨n', y_sub, z_sub⟩ := hc₂;
            cases n' with
            | zero =>
              refine ⟨x, z, ?_ , hz, Or.inl ⟨0, x_sub, z_sub⟩⟩
              exact ⟨x, y, hx, hy, by rw [x_sub, y_sub]; exact ⟨0, rfl, rfl⟩⟩
            | succ n' => have := hq y; subst y; simp [complement, top, step] at this; contradiction
          | inr hc₂ =>
            cases hc₂ with
            | inl hc₂ =>
              obtain ⟨y_sub, z_sub⟩ := hc₂;
              refine ⟨y, z, ?_ , hz, Or.inr (Or.inl ⟨y_sub, z_sub⟩)⟩
              exact ⟨x, y, hx, hy, by rw [y_sub]; exact (Or.inl ⟨0, x_sub, rfl⟩)⟩
            | inr hc₂ =>
              obtain ⟨as, b, bs, _, y_sub, z_sub⟩ := hc₂; subst tl
              refine ⟨y, z, ?_ , hz, Or.inr (Or.inr ⟨as, b, bs, rfl, y_sub, z_sub⟩)⟩
              exact ⟨x, y, hx, hy, by rw [x_sub, y_sub]; exact (Or.inl ⟨0, by simp, rfl⟩)⟩
        | succ n' => have := hp x; subst x; simp [complement, top, step] at this; contradiction
      | inr hc₁ =>
        cases hc₁ with
        | inl hc₁ =>
          obtain ⟨x_sub, _⟩ := hc₁; subst yz;
          obtain ⟨n', y_sub, z_sub⟩ := hc₂
          cases n' with
          | zero =>
            refine ⟨x, z, ?_ , hz, Or.inr (Or.inl ⟨x_sub, z_sub⟩)⟩
            exact ⟨x, y, hx, hy, by rw [x_sub, y_sub]; exact (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
          | succ n' => have := hq y; subst y; simp [complement, top, step] at this; rw [Nat.zero_add] at hy; contradiction
        | inr hc₁ =>
          obtain ⟨as, b, bs, htl, x_sub, yz_sub⟩ := hc₁
          rw [← htl] at hw ⊢
          subst yz_sub
          cases hc₂ with
          | inl hc₂ =>
            obtain ⟨n', y_sub, z_sub⟩ := hc₂;
            cases n' with
            | zero =>
              refine ⟨x, z, ?_ , hz, Or.inr (Or.inr ⟨as, b, bs, rfl, x_sub, z_sub⟩)⟩
              exact ⟨x, y, hx, hy, by simp [x_sub, y_sub, wc]⟩
            | succ n' => have := hq y; subst y; simp [complement, top, step] at this; contradiction
          | inr hc₂ =>
            cases hc₂ with
            | inl hc₂ =>
              obtain ⟨y_sub, z_sub⟩ := hc₂
              refine ⟨Sum.inl ((hd, as ++ b :: bs), v), z, ⟨x, y, hx, hy, ?_⟩, hz, Or.inr (Or.inl ⟨rfl, z_sub⟩)⟩
              rw [x_sub, y_sub]; exact Or.inr (Or.inr ⟨as, b, bs, rfl, rfl, rfl⟩)
            | inr hc₂ =>
              obtain ⟨cs, d, ds, hbs, y_sub, z_sub⟩ := hc₂
              refine ⟨Sum.inl ((hd, as ++ b :: cs), d :: ds ++ v), z, ⟨x, y, hx, hy, ?_⟩, hz, ?_⟩
              . rw [x_sub, y_sub, ← hbs]; exact Or.inr (Or.inr ⟨as, b, cs, rfl, by simp [List.append_assoc], rfl⟩)
              . rw [z_sub, ← hbs]; exact Or.inr (Or.inr ⟨as ++ b :: cs, d, ds, by simp [List.append_assoc], rfl, rfl⟩)
    . intro ⟨xy, z, hxy, hz, hc₁⟩
      obtain ⟨x, y, hx, hy, hc₂⟩ := hxy
      cases hc₁ with
      | inl hc₁ =>
        obtain ⟨n', xy_sub, z_sub⟩ := hc₁
        rw [xy_sub] at hc₂; obtain ⟨n₁, x_sub, y_sub⟩ := hc₂
        cases n₁ with
        | zero => exact ⟨x, z, hx, ⟨y, z, hy, hz, by rw [y_sub, z_sub]; exact Or.inl ⟨n', rfl, rfl⟩⟩, Or.inl ⟨n', x_sub, z_sub⟩⟩
        | succ n₁ => have := hp x hx; rw [x_sub] at this; simp [complement, top, step] at this
      | inr hc₁ =>
        cases hc₁ with
        | inl hc₁ =>
          obtain ⟨xy_sub, z_sub⟩ := hc₁
          rw [xy_sub] at hc₂
          cases hc₂ with
          | inl hc₂ =>
            obtain ⟨n', x_sub, y_sub⟩ := hc₂
            cases n' with
            | zero => exact ⟨x, y, hx, ⟨y, z, hy, hz, by rw [z_sub, y_sub]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, Or.inl ⟨0, x_sub, y_sub⟩⟩
            | succ n' => have := hp x hx; rw [x_sub] at this; simp [complement, top, step] at this
          | inr hc₂ =>
            cases hc₂ with
            | inl hc₂ =>
              obtain ⟨x_sub, y_sub⟩ := hc₂
              exact ⟨x, z, hx, ⟨y, z, hy, hz, by rw [y_sub, z_sub]; exact ⟨0, rfl, rfl⟩⟩, Or.inr (Or.inl ⟨x_sub, z_sub⟩)⟩
            | inr hc₂ =>
              obtain ⟨as, b, bs, htl, x_sub, y_sub⟩ := hc₂
              exact ⟨x, y, hx, ⟨y, z, hy, hz, by rw [z_sub, y_sub]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, by rw [x_sub, y_sub]; exact Or.inr (Or.inr ⟨as, b, bs, htl, rfl, rfl⟩)⟩
        | inr hc₁ =>
          obtain ⟨as, b, bs, htl, x_sub, z_sub⟩ := hc₁; subst xy
          cases hc₂ with
          | inl hc₂ =>
            obtain ⟨n', x_sub, y_sub⟩ := hc₂
            cases n' with
            | zero => exact ⟨x, Sum.inl ((hd, tl), v), hx, ⟨y, z, hy, hz, by rw [y_sub, z_sub]; exact Or.inr (Or.inr ⟨as, b, bs, htl, rfl, rfl⟩)⟩, Or.inl ⟨0, by simp [←htl]; exact x_sub, rfl⟩⟩
            | succ n' => have := hp x hx; rw [x_sub] at this; simp [complement, top, step] at this
          | inr hc₂ =>
            cases hc₂ with
            | inl hc₂ =>
              obtain ⟨x_sub, y_sub⟩ := hc₂
              refine ⟨x, z, hx, ?_, Or.inr (Or.inr ⟨as, b, bs, htl, x_sub, z_sub⟩)⟩
              exact ⟨y, z, hy, hz, by rw [z_sub, y_sub]; exact Or.inl ⟨0, rfl, rfl⟩⟩
            | inr hc₂ =>
              obtain ⟨cs, d, ds, has, x_sub, y_sub⟩ := hc₂
              refine ⟨x, Sum.inl ((d, ds ++ b :: bs), v), hx, ?_, ?_⟩
              . exact ⟨y, z, hy, hz, by rw [y_sub, z_sub]; exact Or.inr (Or.inr ⟨ds, b, bs, rfl, rfl, rfl⟩)⟩
              . rw [x_sub]
                exact Or.inr (Or.inr ⟨cs, d, ds ++ b :: bs, by rw [←htl, ←has]; simp, by simp [List.append_assoc], rfl⟩)
  | Sum.inr (n, v) =>
    constructor
    . intro ⟨x, yz, hx, ⟨y, z, hy, hz, hc₂⟩ , ⟨n', x_sub, _⟩⟩; subst yz
      cases n with
      | zero =>
        cases n' with
        | zero =>
          obtain ⟨n'', y_sub, z_sub⟩ := hc₂
          cases n'' with
          | zero => exact ⟨x, z, ⟨x, y, hx, hy, by rw [x_sub]; exact ⟨0, rfl, y_sub⟩⟩, hz, ⟨0, x_sub, z_sub⟩⟩
          | succ n'' => have := hq y hy; rw [y_sub] at this; simp [complement, top, step] at this
        | succ n' => have := hp x hx; rw [x_sub] at this; simp [complement, top, step] at this
      | succ n' => have := hp x hx; rw [x_sub] at this; simp [complement, top, step] at this
    . intro ⟨xy, z, ⟨x, y, hx, hy, hc₂⟩, hz, ⟨n', _, z_sub⟩⟩; subst xy
      cases n with
      | zero =>
        obtain ⟨n'', x_sub, y_sub⟩ := hc₂
        cases n' with
        | zero =>
          cases n'' with
          | zero => exact ⟨x, z, hx, ⟨y, z, hy, hz, by rw [y_sub, z_sub]; exact ⟨0, rfl, rfl⟩⟩, ⟨0, x_sub, z_sub⟩⟩
          | succ n'' => have := hp x hx; rw [x_sub] at this; simp [complement, top, step] at this
        | succ n' => have := hp x hx; rw [x_sub] at this; simp [complement, top, step] at this
      | succ n => have := hr z hz; rw [z_sub] at this; simp [complement, top, step] at this

end AlgebraicLaws
