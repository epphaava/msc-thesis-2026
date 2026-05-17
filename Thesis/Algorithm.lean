import Thesis.Syntax.Nullability
import Thesis.Syntax.Derivatives
import Thesis.Semantics.Derivatives
import Thesis.Syntax.NullabilityCorrectness

namespace Algorithm

open Expr
open ExprDerivatives
open NullabilityCorrect

/-- Definition 5.1.1 — bounded match positions as implemented (`matchesUpTo`). -/
def matchesUpTo (m : MatchSet) (n : Nat) : List Nat :=
  match m with
  | .inl included => included.filter (fun k => Nat.ble k n)
  | .inr excluded => (List.range (n + 1)).filter (fun k => !(List.elem k excluded))

-- Definition 5.1.2 (Matching algorithm).
def findAllMatches [DecidableEq α] (r : Expr α) (w : List α) : List Nat := matchesUpTo (N (xD w r)) w.length

def matchSetMembership (m : MatchSet) (n : Nat) : Prop :=
  match m with
  | .inl included => n ∈ included
  | .inr excluded => n ∉ excluded

theorem matchesUpTo_iff (m : MatchSet) (w : List α) (k : Nat) :
    k ∈ Algorithm.matchesUpTo m w.length ↔ k ∈ m ∧ k ≤ w.length := by
  cases m with
  | inl included =>
    simp only [Algorithm.matchesUpTo, Membership.mem]
    constructor
    · intro h
      rcases List.mem_filter.mp h with ⟨hi, hb⟩
      exact ⟨hi, Nat.le_of_ble_eq_true hb⟩
    · rintro ⟨hi, hk⟩
      refine List.mem_filter.mpr ⟨hi, ?_⟩
      simp [Nat.ble_eq, hk]
  | inr excluded =>
    simp only [Algorithm.matchesUpTo, Membership.mem]
    constructor
    · intro h
      rcases List.mem_filter.mp h with ⟨hr, hb⟩
      refine ⟨?_, Nat.lt_succ_iff.mp (List.mem_range.mp hr)⟩
      intro hk
      have he : List.elem k excluded = true := List.elem_eq_true_of_mem hk
      cases h : List.elem k excluded <;> simp_all
    · rintro ⟨hnd, hk⟩
      refine List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_iff.mpr hk), ?_⟩
      cases h : List.elem k excluded
      · simp
      · exact False.elim (hnd (List.mem_of_elem_eq_true h))

-- Theorem 5.1.1 — correctness of `findAllMatches` / `matchesUpTo` vs semantic nullability
theorem algorithm_correctness [DecidableEq α] (r : Expr α) (w : List α) (n : Nat) :
    n ∈ findAllMatches r w ↔ nullable_n (sem (xD w r)) n ∧ n ≤ w.length := by
  simp only [findAllMatches]
  rw [matchesUpTo_iff]
  simp only [nullability_correct]

end Algorithm
