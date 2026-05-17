import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace NullabilityLaws

open StructuredWords
open Operators

theorem nullable_n_empty : ¬ nullable_n (∅ : Lang α) n := by rw [nullable_n, empty]; trivial

theorem nullable_n_unit (n : Nat) : nullable_n (I : Lang α) n := by cases n <;> simp [nullable_n, unit]

theorem nullable_n_top : nullable_n (T : Lang α) n := by rw [nullable_n, top]; trivial

theorem nullable_n_symb (a : α) : ¬ nullable_n (#a : Lang α) n := by simp [nullable_n, symb]

theorem nullable_n_union (l k : Lang α) n : nullable_n (k ∪ l) n ↔ (nullable_n k n) ∨ (nullable_n l n) := by simp [nullable_n, union]

theorem nullable_n_intersection : nullable_n (k ∩ l) n ↔ nullable_n k n ∧ nullable_n l n := by rw [nullable_n, intersection]; rfl

theorem nullable_n_diff : nullable_n (k // l) n ↔ nullable_n k n ∧ ¬ nullable_n l n := by rw [nullable_n, complement]; rfl

theorem nullable_n_mult : nullable_n (k • l) n ↔ nullable_n l n ∧ (∃ n', nullable_n k (n+n')) := by
  rw [nullable_n, concat];
  constructor
  . intro ⟨x, y, hx, hy, ⟨n', _, _⟩⟩; subst x y; exact ⟨hy, ⟨n', hx⟩⟩
  . intro ⟨hl, n', hk⟩; refine ⟨(Sum.inr (n+n', [])), (Sum.inr (n, [])), hk, hl, ⟨n', rfl, rfl⟩⟩

theorem nullable_n_la : nullable_n (la l) n ↔ n = 0 ∧ nullable_n l 0 := by
  cases n with
  | zero => simp [nullable_n, la]
  | succ n' => simp [nullable_n, la]

theorem nullable_n_star (l : Lang α) (n : Nat) : nullable_n (l*) n := by
  rw [nullable_n, star]
  exact star_help.inUnit (l := l) n []

theorem nullable_n_step : nullable_n (▹l) (n + 1) ↔ nullable_n l n := by simp [nullable_n, step]
