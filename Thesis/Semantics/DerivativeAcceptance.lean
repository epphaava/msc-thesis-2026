import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace DerAccept

open StructuredWords


theorem der_word_iff {α} (L : Lang α) (hd : α) (tl : List α) (v : List α) :
    der_word (hd :: tl) L (Sum.inr (0, v)) ↔ L (Sum.inl ((hd, tl), v)) := by
  induction tl generalizing hd L v with
  | nil => simp [der_word, der]
  | cons y ys ih => exact ih (der hd L) y v

theorem derLA_word_iff {α} (L : Lang α) (u : List α) (n : Nat) (ys : List α) :
    derLA_word u L (Sum.inr (u.length + n, ys)) ↔ L (Sum.inr (n, u ++ ys)) := by
  induction u generalizing L n ys with
  | nil => simp [derLA_word]
  | cons a as ih =>
    have := ih (derLA a L) (1 + n) ys
    simp [Nat.add_assoc, Nat.one_add, derLA] at ⊢ this
    exact this

-- Theorem 3.2.1 (Derivative characterization of membership).
theorem membership_inl_iff_nullable (L : Lang α) (x : NEList α) (y : List α) :
    L (Sum.inl (x, y)) ↔ nullable_n (derLA_word y (der_word (toList x) L)) y.length := by
  cases x with | mk hd tl =>
    rw [nullable_n, toList]
    have hla := derLA_word_iff (der_word (hd :: tl) L) y 0 []
    have hder := der_word_iff L hd tl y
    simp at hla
    exact hder.symm.trans hla.symm

theorem membership_inr_iff_nullable (L : Lang α) (n : Nat) (y : List α) :
    L (Sum.inr (n, y)) ↔ nullable_n (derLA_word y L) (y.length + n) := by
  simp only [nullable_n]
  have := (derLA_word_iff L y n []).symm
  simp only [List.append_nil] at this
  exact this


/-- Theorem 3.2.2 — existential derivative and indexed nullability. -/
theorem xder_nullable_iff {α} (L : Lang α) (w : List α) (n : Nat) :
    nullable_n (xder w L) n ↔
      (∃ x : NEList α, ∃ y : List α, w = toList x ++ y ∧ y.length = n ∧ L (Sum.inl (x, y)))
      ∨ (∃ k : Nat, k + w.length = n ∧ L (Sum.inr (k, w))) := by
  induction w generalizing L n with
  | nil =>
    simp only [xder, nullable_n, List.length]
    constructor
    · intro h
      right
      exact ⟨n, rfl, h⟩
    · rintro (⟨x, y, hw, _, _⟩ | ⟨k, hk, hL⟩)
      · cases x with
        | mk xh xt =>
          simp [toList] at hw
      · simp at hk
        subst hk
        exact hL
  | cons hd tl ih =>
    simp only [xder, List.length]
    rw [ih (der hd L ∪ derLA hd L)]
    constructor
    . intro h
      cases h with
      | inl h =>
        left; obtain ⟨x, y, htl, hy, hunion⟩ := h
        refine ⟨(hd, toList x), y, by simp [toList] at ⊢ htl; trivial, hy, ?_⟩
        cases hunion with
        | inl hder => cases x with | mk x xs => simp [der, toList] at hder ⊢; exact hder
        | inr hderLA => simp [derLA] at hderLA
      | inr h =>
        obtain ⟨k, hk, hunion⟩ := h
        cases k with
        | zero =>
          cases hunion with
          | inl hder => left; exact ⟨(hd, []), tl, by simp [toList], by rw [Nat.zero_add] at hk; exact hk, hder⟩
          | inr hderLA => simp [derLA] at hderLA
        | succ k =>
          cases hunion with
          | inl hder => simp [der] at hder
          | inr hderLA => right; exact ⟨k, by rw [Nat.succ_add_eq_add_succ] at hk; exact hk, hderLA⟩
    . intro h
      cases h with
      | inl h =>
        obtain ⟨x, y, hw, hy, h⟩ := h
        cases x with | mk x xs =>
          cases xs with
          | nil => right; simp [toList] at hw; exact ⟨0, by rw [hw.2, Nat.zero_add]; exact hy, by rw [hw.1, hw.2]; exact Or.inl h⟩
          | cons xshd xstl => left; simp [toList] at hw; exact ⟨(xshd, xstl), y, by simp [toList] at ⊢ hw; exact hw.2, hy, by rw [hw.1]; exact Or.inl h⟩
      | inr h => obtain ⟨k, hk, h⟩ := h; right; exact ⟨k.succ, by rw [Nat.succ_add_eq_add_succ]; exact hk, Or.inr h⟩

