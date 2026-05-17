import Thesis.Syntax.Expressions
import Thesis.Syntax.Derivatives
import Thesis.Syntax.Nullability
import Thesis.Syntax.NullabilityCorrectness
import Thesis.Semantics.Derivatives
import Thesis.Semantics.DerivativeLaws

namespace DerCorrect

open Expr
open ExprDerivatives
open NullabilityCorrect
open DerCorrect
open DerLaws
open StructuredWords
open Operators

mutual
/-- Theorem 4.2.1 (match derivative): `⟦D_a r⟧ = der_a ⟦r⟧`. -/
theorem der_correct {α} [DecidableEq α] (a : α) (r : Expr α) : (der a (sem r) ) ≐ (sem (D a r) ) := by
  intro w
  match r with
  | .empty => rw [D, sem, der_empty a]
  | .unit => rw [D, sem, sem, der_unit a]
  | .top => rw [sem, D, der_top a, sem, sem, sem, sem]
  | .symbol x =>
    by_cases h : x = a
    · rw [sem, D, der_symb_match x a h]
      simp [sem, complement, step, unit, h]
    · rw [sem, D, der_symb_no_match x a h]
      simp [sem, empty, if_neg (Ne.symm h)]
  | .plus r₁ r₂ =>
    rw [D, sem, sem, der_union a (sem r₁) (sem r₂)]
    rw [union, union, der_correct a r₁, der_correct a r₂]
  | .intersection r₁ r₂ =>
    rw [D, sem, sem, der_intersection a (sem r₁) (sem r₂)]
    rw [intersection, intersection, der_correct a r₁, der_correct a r₂]
  | .complement r₁ r₂ =>
    rw [D, sem, sem, der_complement a (sem r₁) (sem r₂)]
    rw [complement, complement, der_correct a r₁, der_correct a r₂]
  | .mult r₁ r₂ =>
    rw [sem, der_concat a (sem r₁) (sem r₂)]
    rw [D, sem, sem, sem]
    constructor
    · intro h; cases h with
      | inl h =>
        rw [concat] at h; obtain ⟨x, y, hx, hy, hc⟩ := h
        left; rw [concat]
        exact ⟨x, y, (der_correct a r₁ x).mp hx, hy, hc⟩
      | inr h =>
        rw [concat] at h; obtain ⟨x, y, hx, hy, hc⟩ := h
        right; rw [concat]
        exact ⟨x, y, (derLA_correct a r₁ x).mp hx, (der_correct a r₂ y).mp hy, hc⟩
    · intro h; cases h with
      | inl h =>
        rw [concat] at h; obtain ⟨x, y, hx, hy, hc⟩ := h
        left; rw [concat]
        exact ⟨x, y, (der_correct a r₁ x).mpr hx, hy, hc⟩
      | inr h =>
        rw [concat] at h; obtain ⟨x, y, hx, hy, hc⟩ := h
        right; rw [concat]
        exact ⟨x, y, (derLA_correct a r₁ x).mpr hx, (der_correct a r₂ y).mpr hy, hc⟩
  | .star r =>
    rw [sem, D, sem, sem, der_star a (sem r)]
    constructor
    · intro h; rw [concat] at h; obtain ⟨x, y, hx, hy, hc⟩ := h
      rw [concat]; exact ⟨x, y, (der_correct a r x).mp hx, hy, hc⟩
    · intro h; rw [concat] at h; obtain ⟨x, y, hx, hy, hc⟩ := h
      rw [concat]; exact ⟨x, y, (der_correct a r x).mpr hx, hy, hc⟩
  | .la r => exact der_la a (sem r) w
  | .step r => rw [D, sem, sem, der_step a]

/-- Theorem 4.2.1 (lookahead derivative): `⟦D▷_a r⟧ = der▷_a ⟦r⟧`. -/
theorem derLA_correct {α} [DecidableEq α] (a : α) (r : Expr α) :
  derLA a (sem r) ≐ sem (DLA a r) := by
  intro w
  match r with
  | .empty => rw [DLA, sem, derLA_empty a]
  | .unit => rw [DLA, sem, derLA_unit a, sem, sem]
  | .top => rw [DLA, sem, derLA_top a, sem, sem]
  | .symbol x =>
    rw [DLA, sem, sem, derLA_symb x a]
  | .plus r₁ r₂ =>
    rw [DLA, sem, sem, derLA_union a (sem r₁) (sem r₂)]
    rw [union, union, derLA_correct a r₁, derLA_correct a r₂]
  | .intersection r₁ r₂ =>
    rw [DLA, sem, sem, derLA_intersection a (sem r₁) (sem r₂)]
    rw [intersection, intersection, derLA_correct a r₁, derLA_correct a r₂]
  | .complement r₁ r₂ =>
    rw [DLA, sem, sem, derLA_complement a (sem r₁) (sem r₂)]
    rw [complement, complement, derLA_correct a r₁, derLA_correct a r₂]
  | .mult r₁ r₂ =>
    rw [sem, (derLA_concat a (sem r₁) (sem r₂))]
    rw [DLA,sem]
    constructor
    . intro h; obtain ⟨x, y, hx, hy, hc⟩ := h
      exact ⟨x, y, ((derLA_correct a r₁) x).mp hx, ((derLA_correct a r₂) y).mp hy, hc⟩
    . intro h; obtain ⟨x, y, hx, hy, hc⟩ := h
      exact ⟨x, y, ((derLA_correct a r₁) x).mpr hx, ((derLA_correct a r₂) y).mpr hy, hc⟩
  | .star r =>
    rw [DLA, sem, sem, derLA_star a (sem r), sem, sem]
    rw [union, union, derLA_correct a r]
  | .la r =>
    rw [DLA, sem, sem, derLA_la a (sem r), sem]
    match w with
    | Sum.inl ((hd, tl), v) => simp [step]
    | Sum.inr (n, v) =>
      cases n with
      | zero => simp [step, la]
      | succ n =>
        cases n with
        | zero =>
          cases v with
          | nil =>
            simp [step, la]
            exact der_correct a r (Sum.inr (0, []))
          | cons y ys =>
            simp [step, la]
            exact der_correct a r (Sum.inl ((y, ys), []))
        | succ n => simp [step, la]
  | .step r =>
    rw [DLA, sem, sem, derLA_step a (sem r)]
    match w with
    | Sum.inl _ => simp [step]
    | Sum.inr (n, v) =>
      simp [step]
      constructor
      . intro ⟨n', hn, h⟩; exact ⟨n', hn, by rw [←derLA_correct a r]; exact h⟩
      . intro ⟨n', hn, h⟩; exact ⟨n', hn, by rw [derLA_correct a r]; exact h⟩
end

-- Theorem 4.2.2 (iterated derivatives vs `der_word` / `derLA_word`).
theorem der_word_correct {α} [DecidableEq α] (w : List α) (r : Expr α) : (der_word w (sem r)) ≐ (sem (D_word w r)) := by
  induction w generalizing r with
  | nil => intro u; simp [der_word, D_word]
  | cons whd wtl ih =>
    intro u
    simp only [der_word, D_word]
    have hder := der_correct whd r
    have der_word_congr :
        ∀ (tl : List α) (l₁ l₂ : Lang α), l₁ ≐ l₂ → ∀ u : Word α, der_word tl l₁ u ↔ der_word tl l₂ u := by
      intro tl l₁ l₂ h
      induction tl generalizing l₁ l₂ with
      | nil => intro v; exact h v
      | cons y ys ih₂ =>
        intro u'; simp [der_word]
        have : der y l₁ ≐ der y l₂ := by
          intro v
          cases v with
          | inl uv => obtain ⟨⟨hd, tl⟩, v⟩ := uv; exact h (Sum.inl ((y, hd :: tl), v))
          | inr nv =>
            cases nv with | mk n v =>
            cases n with
            | zero => exact h (Sum.inl ((y, []), v))
            | succ n => simp [der]
        exact ih₂ (der y l₁) (der y l₂) this u'
    exact Iff.trans (der_word_congr wtl (der whd (sem r)) (sem (D whd r)) hder u) (ih (D whd r) u)

theorem derLA_word_correct {α} [DecidableEq α] (w : List α) (r : Expr α) :
    (derLA_word w (sem r)) ≐ (sem (DLA_word w r)) := by
  induction w generalizing r with
  | nil => intro u; simp [derLA_word, DLA_word]
  | cons whd wtl ih =>
    intro u
    simp only [derLA_word, DLA_word]
    have hderLA := derLA_correct whd r
    have derLA_word_congr :
        ∀ (tl : List α) (l₁ l₂ : Lang α), l₁ ≐ l₂ → ∀ u : Word α, derLA_word tl l₁ u ↔ derLA_word tl l₂ u := by
      intro tl l₁ l₂ h
      induction tl generalizing l₁ l₂ with
      | nil => intro v; exact h v
      | cons y ys ih₂ =>
        intro u'
        simp [derLA_word]
        have : derLA y l₁ ≐ derLA y l₂ := by
          intro v
          cases v with
          | inl _ => simp [derLA]
          | inr nv =>
            cases nv with | mk n ys =>
            cases n with
            | zero => simp [derLA]
            | succ n => exact h (Sum.inr (n, y :: ys))
        exact ih₂ (derLA y l₁) (derLA y l₂) this u'
    exact Iff.trans (derLA_word_congr wtl (derLA whd (sem r)) (sem (DLA whd r)) hderLA u) (ih (DLA whd r) u)


/-- Theorem 4.2.3 — correctness of the existential derivative: `⟦xD_w r⟧ = xder_w ⟦r⟧`. -/
theorem xder_correct {α} [DecidableEq α] (s : List α) (r : Expr α) : (xder s (sem r)) ≐ (sem (xD s r) ) := by
  induction s generalizing r with
  | nil => intro w; simp [xder, xD]
  | cons a tl ih =>
    intro w
    have : ((der a (sem r)) ∪ (derLA a (sem r))) ≐ (sem ((D a r) + (DLA a r))) := by
      intro u
      simp [sem, union, der_correct a r u, derLA_correct a r u]
    have hcongr := xder_congr tl ((der a (sem r)) ∪ (derLA a (sem r))) (sem ((D a r) + (DLA a r))) this
    exact trans (hcongr w) (ih ((D a r) + (DLA a r)) w)

end DerCorrect
