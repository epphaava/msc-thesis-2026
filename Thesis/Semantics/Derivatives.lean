import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators

open StructuredWords
open Operators

-- Definition 3.2.1 (Match derivative).
def der {α} (a : α) (l : Lang α) : Lang α := λ u =>
  match u with
  | Sum.inl ((hd, tl), v) => l (Sum.inl ((a, hd :: tl), v))
  | Sum.inr (n , v) =>
    match n with
    | 0 => l (Sum.inl ((a, []), v))
    | _ => False

-- Definition 3.2.2 (Lookahead derivative).
def derLA (a : α) (l : Lang α) : Lang α := λ u =>
  match u with
  | Sum.inr (.succ n, ys) => l (Sum.inr (n, a :: ys))
  | _ => False

-- Definition 3.2.3 (Iterated derivatives).
def der_word {α} (u : List α) (l : Lang α) : Lang α :=
  match u with
  | [] => l
  | a :: u => der_word u (der a l)

def derLA_word (u : List α) (l : Lang α) : Lang α :=
  match u with
  | [] => l
  | a :: u => derLA_word u (derLA a l)

/-- Definition 3.2.4 (Indexed nullability). -/
def nullable_n (l : Lang α) (n: Nat) : Prop :=
  l (Sum.inr (n, []))

-- Definition 3.2.5 (Existential derivative).
def xder (u : List α) (l : Lang α) : Lang α :=
  match u with
  | [] => l
  | hd :: tl => xder tl ((der hd l) ∪ (derLA hd l))


-- Lemma 3.2.1.
theorem der_derLA_empty (L : Lang α) : der a (derLA a L) ≐ ∅ := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [der, derLA, empty]
  | inr w => cases w with | mk n v => cases n <;> simp [der, derLA, empty]

/-- Helper for Theorem 4.2.3 (`xder_correct`). -/
theorem xder_congr {α} (s : List α) (l₁ l₂ : Lang α) : l₁ ≐ l₂ → xder s l₁ ≐ xder s l₂ := by
  intro h
  induction s generalizing l₁ l₂ with
  | nil => simp [xder]; trivial
  | cons a tl ih =>
    have hder : der a l₁ ≐ der a l₂ := by
      intro u; match u with
      | Sum.inl ((hd, tl), v) => exact h (Sum.inl ((a, hd :: tl), v))
      | Sum.inr (n, v) =>
        cases n with
        | zero => exact h (Sum.inl ((a, []), v))
        | succ n => simp [der]
    have hderLA : derLA a l₁ ≐ derLA a l₂ := by
      intro u; match u with
      | Sum.inl ((hd, tl), v) => simp [derLA]
      | Sum.inr (n, v) =>
        cases n with
        | zero => simp [derLA]
        | succ n => simp [derLA]; exact h (Sum.inr (n, a :: v))
    have hunion : (der a l₁ ∪ derLA a l₁) ≐ (der a l₂ ∪ derLA a l₂) := by
      intro u; simp [union, hder u, hderLA u]
    exact ih (der a l₁ ∪ derLA a l₁) (der a l₂ ∪ derLA a l₂) hunion
