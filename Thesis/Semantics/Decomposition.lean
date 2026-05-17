import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

open StructuredWords
open Operators

variable {α : Type}

def emptyPart (L : Lang α) : Lang α := λ w =>
  match w with
  | Sum.inr (_, []) =>  L w
  | _ => False

def derPart (L : Lang α) : Lang α := λ w =>
  ∃ a : α, ((#a) • (der a L)) w

def derLAPart (L : Lang α) : Lang α := λ w =>
  ∃ a : α, ▷ ((#a) • (derLA a L) • T) w

/-- Theorem 3.5.1 — structured language decomposition on `W₀`. -/
theorem structuredLanguage_decomposition (l : Lang α) : l ⊆ T // (▹ T) → l ≐ (emptyPart l) ∪ (derPart l) ∪ (derLAPart l) := by
  intro hl w
  constructor
  · intro h
    match w with
    | Sum.inl ((hd, tl), v) =>
      cases tl with
      | nil => right; left; exact ⟨hd, Sum.inl ((hd, []), v), Sum.inr (0, v), by simp [symb], h, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      | cons z zs => right; left; exact ⟨hd, Sum.inl ((hd, []), z :: zs ++ v), Sum.inl ((z, zs), v), by simp [symb], h, Or.inr (Or.inr ⟨[], z, zs, by simp, rfl, rfl⟩)⟩
    | Sum.inr (n, v) =>
      cases v with
      | nil => left; exact h
      | cons y ys =>
        have hn0 : n = 0 := by
          cases n with
          | zero => rfl
          | succ n =>
            have := hl (Sum.inr (n + 1, y :: ys))
            simp [complement, step, top, h] at this
        subst hn0
        right; right; refine ⟨y, ?_⟩
        cases ys with
        | nil =>
          refine ⟨Sum.inl ((y, []), []), Sum.inr (0, []), by simp [symb], ?_, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
          exact ⟨Sum.inr (1, []), Sum.inr (0, []), h, trivial, ⟨1, rfl, rfl⟩⟩
        | cons z zs =>
          refine ⟨Sum.inl ((y, []), z :: zs ++ []), Sum.inl ((z, zs), []), by simp [symb], ?_, Or.inr (Or.inr ⟨[], z, zs, by simp, rfl, rfl⟩)⟩
          exact ⟨Sum.inr (1, z :: zs ++ []), Sum.inl ((z, zs), []), by simp [derLA]; exact h, trivial, Or.inl ⟨1, rfl, rfl⟩⟩
  · intro h
    cases h with
    | inl heps =>
      match w with
      | Sum.inl _ => simp [emptyPart] at heps
      | Sum.inr (_, v) =>
        cases v with
        | nil => exact heps
        | cons _ _ => simp [emptyPart] at heps
    | inr h =>
      cases h with
      | inl hder =>
        obtain ⟨a, ⟨x, y, hx, hy, hwc⟩⟩ := hder
        match w with
        | Sum.inl ((hd, tl), v) =>
          cases hwc with
          | inl hwc => obtain ⟨_, _, _⟩ := hwc; subst x; contradiction
          | inr hwc =>
            cases hwc with
            | inl hwc =>
              obtain ⟨_, _⟩ := hwc; subst x y
              cases tl with
              | nil => subst a; exact hy
              | cons _ _ => contradiction
            | inr hwc =>
              obtain ⟨xs, z, zs, htl, _, _⟩ := hwc; subst x y
              cases xs with
              | nil =>
                cases tl with
                | nil => simp at htl
                | cons _ _ => subst a; obtain ⟨hz, hzs⟩ := htl; exact hy
              | cons _ _ => simp [symb] at hx
        | Sum.inr (_, _) => obtain ⟨_, _, _⟩ := hwc; subst x; simp [symb] at hx
      | inr hderLA =>
        obtain ⟨a, ha⟩ := hderLA
        match w with
        | Sum.inl _ => simp [la] at ha
        | Sum.inr (n, v) =>
          cases n with
          | succ _ => simp [la] at ha
          | zero =>
            cases v with
            | nil =>
              obtain ⟨x, _, hx, _, ⟨_, hx_eq, _⟩⟩ := ha; subst hx_eq
              simp [symb] at hx
            | cons y ys =>
              obtain ⟨x, y, hx, hy, hwc⟩ := ha
              cases hwc with
              | inl hwc =>
                obtain ⟨_, hx_eq, _⟩ := hwc
                subst hx_eq
                simp [symb] at hx
              | inr hwc =>
                cases hwc with
                | inl hwc =>
                  obtain ⟨hx_eq, hy_eq⟩ := hwc; subst hx_eq hy_eq
                  cases ys with
                  | cons _ _ => simp [symb] at hx
                  | nil =>
                    subst a
                    obtain ⟨x', _, hx', _, ⟨n₁, hx'_eq, _⟩⟩ := hy; subst hx'_eq
                    cases n₁ with
                    | zero => simp [derLA] at hx'
                    | succ k =>
                      simp [derLA] at hx'
                      have hk0 : k = 0 := by
                        cases k with
                        | zero => rfl
                        | succ k =>
                          have := hl (Sum.inr (k + 1, [y]))
                          simp [complement, step, top, hx'] at this
                      subst hk0
                      exact hx'
                | inr hwc =>
                  obtain ⟨xs', z', zs', htl_eq, hx_eq, hy_eq⟩ := hwc; subst htl_eq hx_eq hy_eq
                  cases xs' with
                  | cons _ _ => simp [symb] at hx
                  | nil =>
                    simp [symb] at hx
                    subst a
                    obtain ⟨x', _, hx', _, hwc'⟩ := hy
                    cases hwc' with
                    | inl hwc' =>
                      obtain ⟨n, hx'_eq, _⟩ := hwc'; subst hx'_eq
                      cases n with
                      | zero => simp [derLA] at hx'
                      | succ k =>
                        simp [derLA] at hx'
                        have hk0 : k = 0 := by
                          cases k with
                          | zero => rfl
                          | succ k =>
                            have := hl (Sum.inr (k + 1, y :: z' :: zs'))
                            simp [complement, step, top, hx'] at this
                        subst hk0; exact hx'
                    | inr hwc' =>
                      cases hwc' with
                      | inl hwc' =>
                        obtain ⟨hx'_eq, _⟩ := hwc'
                        subst hx'_eq; simp [derLA] at hx'
                      | inr hwc' =>
                        obtain ⟨_, _, _, _, hx'_eq, _⟩ := hwc'
                        subst hx'_eq; simp [derLA] at hx'
