import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

-- Results not numbered in the thesis: extra laws and experiments.


open StructuredWords
open Operators

-- ▷(K \ L) = ▷K \ ▷L
theorem la_complement_distribut (k l : Lang α) : ▷ (k // l) ≐ (▷ k // ▷ l) := by
  intro u
  match u with
  | Sum.inl ((x, xs), ys) =>
    have h_l : (la (k //l) (Sum.inl ((x, xs), ys))) → (la k //la l) (Sum.inl ((x, xs), ys)) := by
      simp [la]
    have h_r : (la k //la l) (Sum.inl ((x, xs), ys)) →  (la (k //l) (Sum.inl ((x, xs), ys))) := by
      simp [la, complement]
    exact Iff.intro h_l h_r
  | Sum.inr (n, []) =>
    match n with
    | 0 => simp [complement, la]
    | .succ n => simp [complement, la]
  | Sum.inr (n, y::ys) =>
    match n with
    | 0 => simp [complement, la]
    | .succ n => simp [complement, la]

-- ▷K • ▷L = ▷(K ∩ L)
theorem la_concat_eq_la_inter (k l : Lang α) : ▷ k • ▷ l ≐ ▷ (k ∩ l) := by
  intro u
  match u with
  | Sum.inl ((x, xs), ys) =>
    simp [concat, la]
    intro x; match x with
    | Sum.inl ((hd, tl), v) => simp
    | Sum.inr (n, v) =>
      cases n with
      | zero =>
        cases v with
        | nil =>
          simp; intro hx y; match y with
          | Sum.inl _ => simp
          | Sum.inr (n', v') =>
            cases n' with
            | zero =>
              cases v' with
              | nil => simp; intro hy hc; simp [wc] at hc
              | cons y' ys' => simp; intro hy hc; simp [wc] at hc
            | succ _ => simp
        | cons y ys =>
          simp; intro hx y; match y with
          | Sum.inl _ => simp
          | Sum.inr (n', v') =>
            cases n' with
            | zero =>
              cases v' with
              | nil => simp; intro hy hc; simp [wc] at hc
              | cons y' ys' => simp; intro hy hc; simp [wc] at hc
            | succ _ => simp
      | succ _ => simp
  | Sum.inr (wn, wv) =>
    simp [concat, la, intersection]
    constructor
    . intro ⟨x, hx, y, hy, hc⟩
      match x with
      | Sum.inl _ => simp at hx
      | Sum.inr (n, v) =>
        cases n with
        | zero =>
          cases v with
          | nil =>
            match y with
            | Sum.inl _ => simp at hy
            | Sum.inr (n', v') =>
              cases n' with
              | zero =>
                cases v' with
                | nil =>
                  simp at hx hy
                  cases wn with
                  | zero =>
                    cases wv with
                    | nil => trivial
                    | cons y' ys' => obtain ⟨n, x_sub, y_sub⟩ := hc; injection y_sub with y_pair; simp at y_pair
                  | succ wn => obtain ⟨n, x_sub, y_sub⟩ := hc; injection y_sub with y_pair; simp at y_pair
                | cons y ys =>
                  simp at hx hy
                  cases wn with
                  | zero =>
                    cases wv with
                    | nil => obtain ⟨n, x_sub, y_sub⟩ := hc; injection y_sub with y_pair; simp at y_pair
                    | cons y' ys' => obtain ⟨n, x_sub, y_sub⟩ := hc; injection x_sub with x_pair; simp at x_pair
                  | succ wn => obtain ⟨n, x_sub, y_sub⟩ := hc; injection y_sub with y_pair; simp at y_pair
              | succ _ => simp at hy
          | cons y' ys' =>
            match y with
            | Sum.inl _ => simp at hy
            | Sum.inr (n', v') =>
              cases n' with
              | zero =>
                cases v' with
                | nil =>
                  simp at hx hy
                  cases wn with
                  | zero =>
                    cases wv with
                    | nil => obtain ⟨n, x_sub, y_sub⟩ := hc; injection x_sub with x_pair; simp at x_pair
                    | cons y' ys' => obtain ⟨n, x_sub, y_sub⟩ := hc; injection y_sub with y_pair; simp at y_pair
                  | succ wn => obtain ⟨n, x_sub, y_sub⟩ := hc; injection y_sub with y_pair; simp at y_pair
                | cons y ys =>
                  simp at hx hy
                  cases wn with
                  | zero =>
                    cases wv with
                    | nil => obtain ⟨n, x_sub, y_sub⟩ := hc; injection y_sub with y_pair; simp at y_pair
                    | cons y'' ys'' =>
                      obtain ⟨n, x_sub, y_sub⟩ := hc; injection x_sub with x_pair; injection x_pair with _ h₁; injection y_sub with y_pair; injection y_pair with _ h₂
                      simp at ⊢ h₁ h₂; simp [h₁.1, h₁.2, h₂.1, h₂.2] at hx hy; trivial
                  | succ wn => obtain ⟨n, x_sub, y_sub⟩ := hc; injection y_sub with y_pair; simp at y_pair
              | succ _ => simp at hy
        | succ n => simp at hx
    . cases wn with
      | zero =>
        cases wv with
        | nil => simp; intro hx hy; refine ⟨(Sum.inr (0, [])), hx, (Sum.inr (0, [])), hy, ⟨0, rfl, rfl⟩⟩
        | cons y ys => simp; intro hx hy; exact ⟨(Sum.inr (0, y::ys)), hx, (Sum.inr (0, y::ys)), hy, ⟨0, rfl, rfl⟩⟩
      | succ wn => simp
