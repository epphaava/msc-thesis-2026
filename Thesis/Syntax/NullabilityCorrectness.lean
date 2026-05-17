import Thesis.Syntax.Expressions
import Thesis.Syntax.Nullability
import Thesis.Semantics.NullabilityLaws

namespace NullabilityCorrect

open Expr
open NullabilityLaws
open Operators

theorem not_mem_filter_iff (n : Nat) (l : List Nat) (p : Nat → Bool) : n ∉ List.filter p l ↔ p n = false ∨ n ∉ l := by
  constructor
  · intro h
    by_cases hn : n ∈ l
    · by_cases hpn : p n = true
      · exfalso; exact h (List.mem_filter.mpr ⟨hn, hpn⟩)
      · cases h : p n <;> simp [h] at hpn ⊢
    · exact Or.inr hn
  · intro h₁ h₂
    cases h₁ with
    | inl h₁ => have := (List.mem_filter.mp h₂).2; simp [this] at h₁
    | inr h₁ => exact h₁ ((List.mem_filter.mp h₂).1)


-- Theorem 4.3.1 — Correctness of nullability
theorem nullability_correct [DecidableEq α] (r : Expr α) (n : Nat) : n ∈ N r ↔ nullable_n (sem r) n := by
  induction r generalizing n with
  | empty => simp [nullable_n, sem, empty, N, Membership.mem]; exact List.not_mem_nil
  | unit => simp [nullable_n, sem, unit, N, Membership.mem]; exact List.not_mem_nil
  | top => simp [nullable_n, sem, top, N, Membership.mem]; exact List.not_mem_nil
  | symbol x => simp [nullable_n, sem, symb, N, Membership.mem]; exact List.not_mem_nil
  | plus r₁ r₂ ih₁ ih₂ =>
    cases hr₁ : N r₁ with
    | inl included₁ =>
      cases hr₂ : N r₂ with
      | inl included₂  =>
        simp [nullable_n, sem, union, N, Membership.mem, matchesOfPlus, hr₁, hr₂]
        constructor
        . intro h
          cases List.mem_append.mp h with
          | inl h₁ => exact Or.inl ((ih₁ n).mp (by rw [hr₁]; exact h₁))
          | inr h₂ => exact Or.inr ((ih₂ n).mp (by rw [hr₂]; exact h₂))
        . intro h
          cases h with
          | inl h₁ => exact List.mem_append.mpr (Or.inl (by have := (ih₁ n).mpr h₁; rw [hr₁] at this; exact this))
          | inr h₂ => exact List.mem_append.mpr (Or.inr (by have := (ih₂ n).mpr h₂; rw [hr₂] at this; exact this))
      | inr excluded₂ =>
        simp [nullable_n, sem, union, N, matchesOfPlus, hr₁, hr₂]
        simp [Membership.mem, hr₁, hr₂] at ih₁ ih₂
        constructor
        · intro h
          cases (not_mem_filter_iff n excluded₂ (fun m => !decide (m ∈ included₁))).mp h with
          | inl h =>
            have hin : n ∈ included₁ := by
              by_cases hdec : decide (n ∈ included₁)
              . exact (decide_eq_true_iff.mp hdec)
              . simp [hdec] at h
            exact Or.inl ((ih₁ n).mp hin)
          | inr h => exact Or.inr ((ih₂ n).mp h)
        · intro hl hr
          cases hl with
          | inl hl =>
            have h₁ := (ih₁ n).mpr hl
            have h₂ := (List.mem_filter.mp hr).2; simp at h₂
            contradiction
          | inr hl => exact ((ih₂ n).mpr hl) ((List.mem_filter.mp hr).1)
    | inr excluded₁ =>
      cases hr₂ : N r₂ with
      | inl included₂  =>
        simp [nullable_n, sem, union, N, Membership.mem, matchesOfPlus, hr₁, hr₂]
        simp [Membership.mem, hr₁, hr₂] at ih₁ ih₂
        constructor
        · intro h
          cases (not_mem_filter_iff n excluded₁ (fun m => !decide (m ∈ included₂))).mp h with
          | inl h =>
            have hin : n ∈ included₂ := by
              by_cases hdec : decide (n ∈ included₂)
              . exact (decide_eq_true_iff.mp hdec)
              . simp [hdec] at h
            exact Or.inr ((ih₂ n).mp hin)
          | inr h => exact Or.inl ((ih₁ n).mp h)
        · intro hl hr
          cases hl with
          | inl h₁ => exact ((ih₁ n).mpr h₁) ((List.mem_filter.mp hr).1)
          | inr h₂ =>
            have := (ih₂ n).mpr h₂
            have := (List.mem_filter.mp hr).2; simp at this
            contradiction
      | inr excluded₂ =>
        simp [nullable_n, sem, union, N, Membership.mem, matchesOfPlus, hr₁, hr₂]
        simp [Membership.mem, hr₁, hr₂] at ih₁ ih₂
        constructor
        · intro h
          cases (not_mem_filter_iff n excluded₁ (fun m => decide (m ∈ excluded₂))).mp h with
          | inl hdec => exact Or.inr ((ih₂ n).mp (decide_eq_false_iff_not.mp hdec))
          | inr hn => exact Or.inl ((ih₁ n).mp hn)
        · intro hl hf
          cases hl with
          | inl hl => exact ((ih₁ n).mpr hl) ((List.mem_filter.mp hf).1)
          | inr hl =>
              have := (ih₂ n).mpr hl
              have := Iff.mp (@decide_eq_true_iff (n ∈ excluded₂) _) (List.mem_filter.mp hf).2
              contradiction
  | intersection r₁ r₂ ih₁ ih₂ =>
    cases hr₁ : N r₁ with
    | inl included₁ =>
      cases hr₂ : N r₂ with
      | inl included₂ =>
        simp [nullable_n, sem, intersection, N, Membership.mem, matchesOfIntersection, hr₁, hr₂] at ih₁ ih₂ ⊢
        constructor
        · intro h
          have h := List.mem_filter.mp h
          exact ⟨(ih₁ n).mp h.1, (ih₂ n).mp (by simp at h; exact h.2)⟩
        · intro h
          have : decide (n ∈ included₂) = true := decide_eq_true_iff.mpr ((ih₂ n).mpr h.2)
          exact List.mem_filter.mpr ⟨(ih₁ n).mpr h.1, this⟩
      | inr excluded₂ =>
        simp [nullable_n, sem, intersection, N, Membership.mem, matchesOfIntersection, hr₁, hr₂] at ih₁ ih₂ ⊢
        constructor
        · intro h
          have h := List.mem_filter.mp h
          exact ⟨(ih₁ n).mp h.1, (ih₂ n).mp (by simp at h; exact h.2)⟩
        · intro h
          refine List.mem_filter.mpr ⟨((ih₁ n).mpr h.1), ?_⟩
          by_cases hx : n ∈ excluded₂
          · have := (ih₂ n).mpr h.2; contradiction
          · simp at hx ⊢; exact hx
    | inr excluded₁ =>
      cases hr₂ : N r₂ with
      | inl included₂ =>
        simp [nullable_n, sem, intersection, N, Membership.mem, matchesOfIntersection, hr₁, hr₂] at ih₁ ih₂ ⊢
        constructor
        · intro h
          have h := List.mem_filter.mp h
          exact ⟨(ih₁ n).mp (by simp at h; exact h.2), (ih₂ n).mp h.1⟩
        · intro h
          refine List.mem_filter.mpr ⟨((ih₂ n).mpr h.2), ?_⟩
          by_cases hx : n ∈ excluded₁
          · have := (ih₁ n).mpr h.1; contradiction
          · simp at hx ⊢; exact hx
      | inr excluded₂ =>
        simp [nullable_n, sem, intersection, N, Membership.mem, matchesOfIntersection, hr₁, hr₂] at ih₁ ih₂ ⊢
        constructor
        · intro h; have h : ¬ (n ∈ excluded₁ ++ excluded₂) := h
          simp [List.mem_append] at h
          exact ⟨(ih₁ n).mp h.1, (ih₂ n).mp h.2⟩
        · intro h hn
          cases List.mem_append.mp hn with
          | inl hn₁ => exact ((ih₁ n).mpr h.1) hn₁
          | inr hn₂ => exact ((ih₂ n).mpr h.2) hn₂
  | complement r₁ r₂ ih₁ ih₂ =>
    cases hr₁ : N r₁ with
    | inl included₁ =>
      cases hr₂ : N r₂ with
      | inl included₂ =>
        simp [nullable_n, sem, complement, N, Membership.mem, matchesOfComplement, hr₁, hr₂] at ih₁ ih₂ ⊢
        constructor
        · intro h; have h := List.mem_filter.mp h
          have hnot : n ∉ included₂ := by
            intro hmem
            have h2 : (!decide (n ∈ included₂)) = true := h.2
            simp [hmem] at h2
          exact ⟨(ih₁ n).mp h.1, fun hs => hnot ((ih₂ n).mpr hs)⟩
        · intro h
          have : (!decide (n ∈ included₂)) = true := by
            by_cases hmem : n ∈ included₂
            · exact False.elim (h.2 ((ih₂ n).mp hmem))
            · simp [hmem]
          exact List.mem_filter.mpr ⟨(ih₁ n).mpr h.1, this⟩
      | inr excluded₂ =>
        simp [nullable_n, sem, complement, N, Membership.mem, matchesOfComplement, hr₁, hr₂] at ih₁ ih₂ ⊢
        constructor
        · intro h
          have h := List.mem_filter.mp h
          have hmem : n ∈ excluded₂ := decide_eq_true_iff.mp h.2
          exact ⟨(ih₁ n).mp h.1, fun hs => ((ih₂ n).mpr hs) hmem⟩
        · intro h
          refine List.mem_filter.mpr ⟨((ih₁ n).mpr h.1), ?_⟩
          by_cases hx : decide (n ∈ excluded₂) = true
          · exact hx
          · have hnot : ¬n ∈ excluded₂ := by
              intro hm
              exact hx (decide_eq_true_iff.mpr hm)
            have := h.2 ((ih₂ n).mp hnot)
            contradiction
    | inr excluded₁ =>
      cases hr₂ : N r₂ with
      | inl included₂ =>
        simp [nullable_n, sem, complement, N, Membership.mem, matchesOfComplement, hr₁, hr₂] at ih₁ ih₂ ⊢
        constructor
        · intro h
          have h : ¬ (n ∈ excluded₁ ++ included₂) := h
          simp [List.mem_append] at h
          exact ⟨(ih₁ n).mp h.1, fun hs => h.2 ((ih₂ n).mpr hs)⟩
        · intro h hn
          cases List.mem_append.mp hn with
          | inl hn₁ => exact ((ih₁ n).mpr h.1) hn₁
          | inr hn₂ => exact h.2 ((ih₂ n).mp hn₂)
      | inr excluded₂ =>
        simp [nullable_n, sem, complement, N, Membership.mem, matchesOfComplement, hr₁, hr₂] at ih₁ ih₂ ⊢
        constructor
        · intro h
          have h := List.mem_filter.mp h
          exact ⟨(ih₁ n).mp (by simp at h; exact h.2), fun hs => ((ih₂ n).mpr hs) h.1⟩
        · intro h
          refine List.mem_filter.mpr ⟨?_, ?_⟩
          · by_cases hx : n ∈ excluded₂
            · exact hx
            · have := h.2 ((ih₂ n).mp hx); contradiction
          · have := (ih₁ n).mpr h.1; simp [this]
  | mult r₁ r₂ ih₁ ih₂ =>
    cases hr₁ : N r₁ with
    | inl included₁ =>
      cases hr₂ : N r₂ with
      | inl included₂  =>
        simp [nullable_n, sem, N, Membership.mem, matchesOfMult, hr₁, hr₂]
        constructor
        . intro h
          have h := List.mem_filter.mp h
          obtain ⟨n₁, hn₁, hn⟩ := (List.any_eq_true.mp h.2); simp at hn
          have h₂ := (ih₂ n).mp (by rw [hr₂]; exact h.1)
          have h₁ := (ih₁ n₁).mp (by rw [hr₁]; exact hn₁)
          exact ⟨(Sum.inr (n₁, [])), (Sum.inr (n, [])), h₁, h₂, ⟨n₁-n, by rw [Nat.add_sub_cancel' hn], rfl⟩⟩
        . intro ⟨w₁, w₂, ⟨hsem₁, hsem₂, ⟨n', n₁_sub, n_sub⟩⟩⟩; subst w₁ w₂
          have h₂ := (ih₂ n).mpr hsem₂
          have h₁ := (ih₁ (n + n')).mpr hsem₁
          exact List.mem_filter.mpr ⟨by rw [hr₂] at h₂; exact h₂, (by rw [hr₁] at h₁; exact List.any_eq_true.mpr ⟨n + n', h₁, by simp⟩)⟩
      | inr excluded₂ =>
        simp [nullable_n, sem, N, matchesOfMult, hr₁, hr₂]
        simp [Membership.mem, hr₁, hr₂] at ih₁ ih₂
        constructor
        · intro h
          cases hmax : included₁.max? with
          | none => simp [hmax, Membership.mem] at h; cases h
          | some max =>
            have hmem : n ∈ List.filter (fun n => !decide (n ∈ excluded₂)) (List.range (max + 1)) := by rw [hmax, Membership.mem] at h; exact h
            obtain ⟨n_leq_max, hn⟩ := List.mem_filter.mp hmem; simp at n_leq_max hn
            have h₂ := (ih₂ n).mp hn
            have hmax := (List.max?_eq_some_iff.mp hmax).1
            have h₁ := (ih₁ max).mp hmax
            refine ⟨(Sum.inr (max, [])), (Sum.inr (n, [])), h₁, h₂, ⟨max - n, by rw [Nat.add_sub_of_le (Nat.le_of_lt_add_one n_leq_max)], rfl⟩⟩
        · intro  ⟨w₁, w₂, ⟨h₁, h₂, ⟨n', n₁_sub, n_sub⟩⟩⟩; subst w₁ w₂
          have hn := (ih₂ n).mpr h₂
          have hn' : n + n' ∈ included₁ := (ih₁ (n + n')).mpr h₁
          cases hmax : included₁.max? with
          | none => have := (List.max?_eq_none_iff.mp hmax); simp [this] at hn'
          | some max =>
            have n_leq_max := trans (Nat.le_add_right n n') ((List.max?_eq_some_iff.mp hmax).2 _ hn')
            have nrange := List.mem_range.mpr (Nat.lt_succ_iff.mpr n_leq_max)
            have hdec : decide (n ∈ excluded₂) = false := decide_eq_false_iff_not.mpr hn
            have hfilter : n ∈ List.filter (fun n => !decide (n ∈ excluded₂)) (List.range (max + 1)) := List.mem_filter.mpr ⟨nrange, by simp [hdec]⟩
            rw [Membership.mem]; exact hfilter
    | inr excluded₁ =>
      cases hr₂ : N r₂ with
      | inl included₂  =>
        simp [nullable_n, sem, N, Membership.mem, matchesOfMult, hr₁, hr₂]
        simp [Membership.mem, hr₁, hr₂] at ih₁ ih₂
        constructor
        · intro h
          have h₂ := (ih₂ n).mp h
          have h₁ : ∃ n', nullable_n (sem r₁) (n + n') := by
            cases hmax : excluded₁.max? with
            | none =>
              have := List.max?_eq_none_iff.mp hmax
              have : ¬ (n + 0) ∈ excluded₁ := by simp [this]
              exact ⟨0, (ih₁ (n + 0)).mp this⟩
            | some max =>
              have hnot : ¬ (n + (max + 1)) ∈ excluded₁ := by
                intro h
                have h₁ := ((List.max?_eq_some_iff.mp hmax).2) _ h
                have h₂ := Nat.lt_of_lt_of_le (Nat.lt_succ_self max) (Nat.le_add_left (max + 1) n)
                exact Nat.not_lt_of_ge h₁ h₂
              exact ⟨max + 1, (ih₁ (n + (max + 1))).mp hnot⟩
          exact ⟨(Sum.inr (n + h₁.choose, [])), (Sum.inr (n, [])), h₁.choose_spec, h₂, ⟨h₁.choose, rfl, rfl⟩⟩
        · intro ⟨w₁, w₂, ⟨h₁, h₂, ⟨_, _, _⟩⟩⟩; subst w₁ w₂
          exact (ih₂ n).mpr h₂
      | inr excluded₂ =>
        simp [nullable_n, sem, N, Membership.mem, matchesOfMult, hr₁, hr₂]
        simp [Membership.mem, hr₁, hr₂] at ih₁ ih₂
        constructor
        · intro h
          have h₂ := (ih₂ n).mp h
          have h₁ : ∃ n', nullable_n (sem r₁) (n + n') := by
            cases hmax : excluded₁.max? with
            | none =>
              have := List.max?_eq_none_iff.mp hmax
              have : ¬ (n + 0) ∈ excluded₁ := by simp [this]
              exact ⟨0, (ih₁ (n + 0)).mp this⟩
            | some max =>
              have hmax_ge : ∀ b, b ∈ excluded₁ → b ≤ max := (List.max?_eq_some_iff.mp hmax).2
              refine ⟨max + 1, ?_⟩
              have hnot : ¬ (n + (max + 1)) ∈ excluded₁ := by
                intro h
                have h₁ := ((List.max?_eq_some_iff.mp hmax).2) _ h
                have h₂ := Nat.lt_of_lt_of_le (Nat.lt_succ_self max) (Nat.le_add_left (max + 1) n)
                exact Nat.not_lt_of_ge h₁ h₂
              exact (ih₁ (n + (max + 1))).mp hnot
          exact ⟨(Sum.inr (n + h₁.choose, [])), (Sum.inr (n, [])), h₁.choose_spec, h₂, ⟨h₁.choose, rfl, rfl⟩⟩
        · intro  ⟨w₁, w₂, ⟨h₁, h₂, ⟨_, n₁_sub, n_sub⟩⟩⟩ hr; subst w₁ w₂
          exact ((ih₂ n).mpr h₂) hr
  | star r ih =>
    constructor
    · intro h; exact nullable_n_star (sem r) n
    · intro h; simp [N]; cases N r <;> intro hn <;> cases hn
  | la r ih =>
    simp [sem, nullable_n_la]
    cases hr : N r with
    | inl included =>
      have ih0 := ih 0; rw [hr] at ih0
      by_cases h0 : 0 ∈ included
      · have hif : (if 0 ∈ included then MatchSet.included [0] else MatchSet.included []) = MatchSet.included [0] := by simp [h0]
        constructor
        · intro h
          have hn : n = 0 := by
            rw [N, hr, matchesOfLA, hif, Membership.mem] at h
            change n ∈ ([0] : List Nat) at h
            simp at h
            exact h
          exact ⟨hn, (ih0.mp h0)⟩
        · intro ⟨hn, _⟩; subst hn
          rw [N, hr, matchesOfLA, hif, Membership.mem]
          change 0 ∈ ([0] : List Nat); simp
      · constructor
        · intro h
          have false_if : (if 0 ∈ included then MatchSet.included [0] else MatchSet.included []) = MatchSet.included [] := by simp [h0]
          rw [N, hr, matchesOfLA, false_if, Membership.mem] at h
          cases h
        · intro h; have := ih0.mpr h.2; contradiction
    | inr excluded =>
      have ih0 := ih 0; rw [hr] at ih0
      by_cases h0 : 0 ∈ excluded
      · constructor
        · intro h
          have hif : (if 0 ∈ excluded then MatchSet.included [] else MatchSet.included [0]) = MatchSet.included [] := by simp [h0]
          rw [N, hr, matchesOfLA, hif, Membership.mem] at h
          cases h
        · intro h
          have := ih0.mpr h.2
          contradiction
      · have hif : (if 0 ∈ excluded then MatchSet.included [] else MatchSet.included [0]) = MatchSet.included [0] := by simp [h0]
        constructor
        · intro h
          have hn0 : n = 0 := by
            rw [N, hr, matchesOfLA, hif, Membership.mem] at h
            change n ∈ ([0] : List Nat) at h
            simp at h
            exact h
          exact ⟨hn0, ih0.mp h0⟩
        · intro ⟨hn, _⟩; subst hn
          rw [N, hr, matchesOfLA, hif, Membership.mem]
          change 0 ∈ ([0] : List Nat)
          simp
  | step r ih =>
    cases hr : N r with
    | inl included =>
      constructor
      · intro h
        rw [N, hr, matchesOfStep, Membership.mem] at h
        obtain ⟨n', hn', hnn'⟩ := List.mem_map.mp h
        exact ⟨n', hnn'.symm, (ih n').mp (by rw [hr]; exact hn')⟩
      · intro h
        cases n with
        | zero => simp [nullable_n, sem, step] at h
        | succ n =>
          simp [sem, nullable_n, step] at h
          rw [N, hr, matchesOfStep, Membership.mem]
          have hk := (ih n).mpr h
          exact List.mem_map.mpr ⟨n, (by rw [hr] at hk; exact hk), by simp⟩
    | inr excluded =>
      constructor
      · intro h
        rw [N, hr, matchesOfStep, Membership.mem] at h
        cases n with
        | zero =>
          have hfalse : 0 ∉ 0 :: List.map Nat.succ excluded := h
          simp at hfalse
        | succ n =>
          have h₁ : Nat.succ n ∉ List.map Nat.succ excluded := by intro hk; exact h (by simp [hk])
          have h₂ : n ∉ excluded := by intro hk; exact h₁ (List.mem_map.mpr ⟨n, hk, rfl⟩)
          exact ⟨n, rfl, (ih n).mp (by rw [hr]; exact h₂)⟩
      · intro h
        rw [N, hr, matchesOfStep, Membership.mem]
        cases n with
        | zero => simp [nullable_n, sem, step] at h
        | succ n =>
          intro hs
          simp at hs
          simp [sem, nullable_n, step] at h
          have hk := (ih n).mpr h; rw [hr] at hk
          contradiction
