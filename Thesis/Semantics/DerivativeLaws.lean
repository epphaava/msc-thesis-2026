import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace DerLaws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

-- ======== DER ==========
theorem der_empty (a : α) : der a ∅ ≐ ∅ := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [der, empty]
  | inr w => cases w with | mk n v => cases n <;> simp [der, empty]

theorem der_unit (a : α) : der a I ≐ ∅ := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [der, unit, empty]
  | inr w => cases w with | mk n v => cases n <;> simp [der, unit, empty]

theorem der_top (a : α): (der a T) ≐ (T // ▹T) := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [der, complement, step, top]
  | inr w => cases w with | mk n v => cases n <;> simp [der, complement, step, top]

theorem der_symb_match (a b: α) (h : a = b) : der b (#a) ≐ (I // ▹I) := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [der, complement, step, symb, unit]
  | inr w => cases w with | mk n v => cases n <;> simp [der, symb, h, complement, step, unit]


theorem der_symb_no_match (a b: α) (h : ¬ (a = b)) : der b (#a) ≐ ∅ := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [empty, der, symb]
  | inr w => cases w with | mk n v => cases n <;> simp [empty, der, symb, h]

theorem der_union (a : α) (k l : Lang α): der a (k ∪ l) ≐ (der a k) ∪ (der a l) := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [der, union]
  | inr w => cases w with | mk n v => cases n <;> simp [der, union]

theorem der_intersection (a : α) (k l : Lang α): der a (k ∩ l) ≐ (der a k) ∩ (der a l) := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [der, intersection]
  | inr w => cases w with | mk n v => cases n <;> simp [der, intersection]

theorem der_complement (a : α) (k l : Lang α): der a (k // l) ≐ ((der a k) // (der a l)) := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [der, complement]
  | inr w => cases w with | mk n v => cases n <;> simp [der, complement]

theorem der_concat (a : α) (k l : Lang α) :
  der a (concat k l) ≐ ((der a k) • l) ∪ ((derLA a k) • (der a l)) := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v => cases u with | mk hd tl =>
      constructor
      · intro ⟨x, y, x_in_lang, y_in_lang, h⟩; cases h with
        | inl h =>
          obtain ⟨n, x_sub, y_sub⟩ := h; right; subst x_sub y_sub;
          exact ⟨(Sum.inr (n.succ, hd :: (tl ++ v))), (Sum.inl ((hd, tl), v)), x_in_lang, y_in_lang, by simp [wc]; exact ⟨⟨n.succ, rfl⟩, rfl⟩⟩
        | inr h =>
          cases h with
          | inl h =>
            obtain ⟨x_sub, y_sub⟩ := h; subst x_sub; left;
            refine ⟨Sum.inl ((hd, tl), v), y, x_in_lang, y_in_lang, ?_⟩
            right; left; trivial
          | inr h =>
            obtain ⟨xs, z, zs, htl, x_sub, y_sub⟩ := h; cases xs with
            | nil =>
              simp at htl; rw [←htl.1, ←htl.2]; subst x_sub; left;
              refine ⟨(Sum.inr (0, z :: (zs ++ v))), y, x_in_lang, y_in_lang, ?_⟩
              left; exists 0
            | cons x xs =>
              simp at htl; rw [←htl.1, ←htl.2]; subst x_sub y_sub; left;
              refine ⟨(Sum.inl ((x, xs), z :: (zs ++ v))), (Sum.inl ((z, zs), v)), x_in_lang, y_in_lang, ?_⟩
              right; right; exists xs, z, zs
      · intro h; cases h with
        | inl h =>
          obtain ⟨x, y, x_in_lang, y_in_lang, h⟩ := h; cases h with
          | inl h =>
            obtain ⟨n, x_sub, y_sub⟩ := h; subst x_sub
            cases n with
            | zero =>
              refine ⟨(Sum.inl ((a, []), hd :: tl ++ v)), y, x_in_lang, y_in_lang, ?_⟩
              right; right; exists [], hd, tl
            | succ x => simp [der] at x_in_lang
          | inr h =>
            cases h with
            | inl h =>
              obtain ⟨x_sub, y_sub⟩ := h; subst x_sub;
              refine ⟨(Sum.inl ((a, hd :: tl), v)), y, x_in_lang, y_in_lang, ?_⟩
              right; left; trivial
            | inr h =>
              obtain ⟨xs, z, zs, htl, x_sub, y_sub⟩ := h; subst x_sub;
              refine ⟨((Sum.inl ((a, hd :: xs), z :: zs ++ v))), y, x_in_lang, y_in_lang, ?_⟩
              right; right; exact ⟨hd :: xs, z, zs, by simp [htl], rfl, y_sub⟩
        | inr h =>
          obtain ⟨x, y, x_in_lang, y_in_lang, h⟩ := h; cases h with
          | inl h =>
            obtain ⟨n, x_sub, y_sub⟩ := h; subst x_sub y_sub
            cases n with
            | zero => cases x_in_lang
            | succ n => exact ⟨(Sum.inr (n, a :: hd :: tl ++ v)), ((Sum.inl ((a, hd :: tl), v))), x_in_lang, y_in_lang, by simp [wc]; exact ⟨⟨n, rfl⟩, rfl⟩⟩
          | inr h =>
            cases h with
            | inl h => simp [h.1, derLA] at x_in_lang
            | inr h => obtain ⟨_, _, _, _, x_sub, _⟩ := h; simp [x_sub, derLA] at x_in_lang
  | inr w =>
    cases w with | mk n v =>
      constructor
      . intro h
        cases n with
        | zero =>
          obtain ⟨s, t, hk, hl, h⟩ := h; cases h with
          | inl h =>
            obtain ⟨n, hs, ht⟩ := h; subst hs ht
            right; refine ⟨Sum.inr (n.succ, v), Sum.inr (0, v), hk, hl, by simp [wc]; exists n.succ⟩
          | inr h =>
            cases h with
            | inl h =>
              obtain ⟨hs, ht⟩ := h; subst hs ht
              left; refine ⟨Sum.inr (0, v), Sum.inr (0, v), hk, hl, by simp [wc]; exists 0⟩
            | inr h => simp at h
        | succ n => simp [der] at h
      . intro h
        cases h with
        | inl h =>
          cases n with
          | zero =>
            obtain ⟨s, t, hk, hl , ⟨n', hs, ht⟩⟩ := h; subst hs ht
            cases n' with
            | zero => refine ⟨Sum.inl ((a, []), v), Sum.inr (0, v), hk, hl, by simp [wc]; rfl⟩
            | succ n' => simp [der] at hk
          | succ n => obtain ⟨s, t, hk, hl , ⟨n', hs, ht⟩⟩ := h; subst hs ht; simp [der] at hk
        | inr h =>
          obtain ⟨s, t, hk, hl, ⟨n', hs, ht⟩⟩ := h; subst ht hs
          cases n with
          | zero =>
            cases n' with
            | zero => trivial
            | succ n' => simp [derLA] at hk; refine ⟨Sum.inr (n', a :: v), Sum.inl ((a, []), v), hk, hl, by simp [wc]; grind⟩
          | succ n => simp [der] at hl

theorem der_star (a : α) (l : Lang α) : der a (l*) ≐ (der a l) • (l*) := by
  intro w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    · simp [der]
      intro h
      suffices ∀ w1, star_help l w1 →
          ∀ hd' tl' v', w1 = Sum.inl ((a, hd' :: tl'), v') →
            concat (der a l) (star l) (Sum.inl ((hd', tl'), v')) by
        cases h with
        | inConcat x y w hx hy hc =>
          exact this _ (star_help.inConcat x y _ hx hy hc) hd tl v rfl
      intro w1 h1
      induction h1 with
      | inUnit _ _ => intro _ _ _ hw; nomatch hw
      | inConcat x y w hx hy hc ih =>
        intro hd' tl' v' hw
        subst hw
        cases hc with
        | inl hc =>
          obtain ⟨_, _, y_sub⟩ := hc
          exact ih hd' tl' v' y_sub
        | inr hc =>
          cases hc with
          | inl hc =>
            obtain ⟨x_eq, y_eq⟩ := hc
            subst x_eq
            exact ⟨Sum.inl ((hd', tl'), v'), Sum.inr (0, v'), hx, star_help.inUnit 0 v',
              Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
          | inr hc =>
            obtain ⟨xs, z, zs, htl, x_sub, y_sub⟩ := hc
            cases xs with
            | nil =>
              simp at htl; obtain ⟨hz, hzs⟩ := htl
              rw [hz, hzs] at x_sub y_sub
              refine ⟨Sum.inr (0, hd' :: tl' ++ v'), y, (by rw [x_sub] at hx; exact hx), hy, Or.inl ⟨0, rfl, y_sub⟩⟩
            | cons xhd xtl =>
              simp at htl; obtain ⟨hhd', htl'⟩ := htl
              refine ⟨Sum.inl ((hd', xtl), z :: zs ++ v'), y, (by rw [x_sub, hhd'] at hx; exact hx), hy, Or.inr (Or.inr ⟨xtl, z, zs, htl', rfl, y_sub⟩)⟩
    · simp [der]
      intro h
      obtain ⟨x, y, hx, hy, hc⟩ := h
      cases hc with
      | inl hc =>
        obtain ⟨n, x_sub, y_sub⟩ := hc
        cases n with
        | succ n => simp [x_sub, der] at hx
        | zero =>
          exact star_help.inConcat (l := l) (Sum.inl ((a, []), hd :: tl ++ v)) y (Sum.inl ((a, hd :: tl), v)) (by rw [x_sub] at hx; exact hx) hy (Or.inr (Or.inr ⟨[], hd, tl, rfl, rfl, y_sub⟩))
      | inr hc =>
        cases hc with
        | inl hc =>
          obtain ⟨x_sub, y_sub⟩ := hc
          exact star_help.inConcat (l := l) (Sum.inl ((a, hd :: tl), v)) y (Sum.inl ((a, hd :: tl), v)) (by rw [x_sub] at hx; exact hx) hy (Or.inr (Or.inl ⟨rfl, y_sub⟩))
        | inr hc =>
          obtain ⟨xs, z, zs, htl, x_sub, y_sub⟩ := hc
          cases xs with
          | nil =>
            subst htl
            exact star_help.inConcat (l := l) (Sum.inl ((a, [hd]), z :: zs ++ v)) y (Sum.inl ((a, hd :: z :: zs), v)) (by rw [x_sub] at hx; exact hx) hy (Or.inr (Or.inr ⟨[hd], z, zs, rfl, rfl, y_sub⟩))
          | cons xhd xtl =>
            subst htl
            exact star_help.inConcat (l := l) (Sum.inl ((a, hd :: xhd :: xtl), z :: zs ++ v)) y (Sum.inl ((a, hd :: xhd :: xtl ++ z :: zs), v)) (by rw [x_sub] at hx; exact hx) hy (Or.inr (Or.inr ⟨hd :: xhd :: xtl, z, zs, rfl, rfl, y_sub⟩))
  | Sum.inr (n, v) =>
    cases n with
    | zero =>
      constructor
      · simp [der]
        intro h
        suffices ∀ w' (h' : star_help l w'), w' = Sum.inl ((a, []), v) → concat (der a l) (star l) (Sum.inr (0, v)) by
          exact this _ h rfl
        intro w' h' w'_sub
        induction h' with
        | inUnit n y => cases w'_sub
        | inConcat x y w hx hy hc ih =>
          subst w'_sub
          cases hc with
          | inl hc =>
            obtain ⟨_, _, y_eq⟩ := hc
            exact ih y_eq
          | inr hc =>
            cases hc with
            | inl hc =>
              obtain ⟨x_sub, _⟩ := hc
              exact ⟨Sum.inr (0, v), Sum.inr (0, v), (by rw [x_sub] at hx; exact hx), star_help.inUnit 0 v, ⟨0, rfl, rfl⟩⟩
            | inr hc =>
              obtain ⟨xs, _, _, htl, _, _⟩ := hc
              cases xs <;> simp at htl
      · intro h
        obtain ⟨x, y, hx, hy, ⟨n', x_sub, y_sub⟩⟩ := h
        subst x_sub y_sub
        cases n' with
        | zero => exact star_help.inConcat (l := l) (Sum.inl ((a, []), v)) (Sum.inr (0, v)) (Sum.inl ((a, []), v)) hx hy (Or.inr (Or.inl ⟨rfl, rfl⟩))
        | succ k => simp [der] at hx
    | succ n =>
      simp [der]
      intro h
      obtain ⟨x, _, hx, _, ⟨_, x_sub, _⟩⟩ := h
      rw [x_sub] at hx; simp [der] at hx


theorem der_la (a : α) (l : Lang α) : der a (la l) ≐ ∅  := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [empty, der, la]
  | inr w =>
    cases w with | mk n v => cases n <;> trivial

theorem der_step (a : α) (l : Lang α) : der a (▹l) ≐ ∅ := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [der, step, empty]
  | inr w =>
    cases w with | mk n v => cases n <;> simp [der, step, empty]

-- ========= DERLA ============
theorem derLA_empty (a : α) : derLA a ∅ ≐ ∅ := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [derLA, empty]
  | inr w => cases w with | mk n v => cases n <;> simp [empty, derLA]

theorem derLA_unit (a : α) : derLA a I ≐ ▹I := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [step, derLA]
  | inr w => cases w with | mk n v => cases n with
    | zero => simp [step, unit, derLA]
    | succ n => cases n <;> simp [step, unit, derLA]

theorem derLA_top (a : α) : derLA a T ≐ step T := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [derLA, step]
  | inr w => cases w with | mk n v => cases n <;> simp [derLA, top, step]

theorem derLA_symb (a b : α) : derLA b (#a) ≐ ∅ := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [empty, derLA]
  | inr w => cases w with | mk n v => cases n <;> simp [empty, symb, derLA]

theorem derLA_union (a : α) (k l : Lang α) : derLA a (k ∪ l) ≐ derLA a k ∪ derLA a l := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [union, derLA]
  | inr w => cases w with | mk n v => cases n <;> simp [union, derLA]

theorem derLA_intersection (a : α) (k l : Lang α): derLA a (k ∩ l) ≐ (derLA a k) ∩ (derLA a l) := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [derLA, intersection]
  | inr w => cases w with | mk n v => cases n <;> simp [derLA, intersection]

theorem derLA_complement (a : α) (k l : Lang α): derLA a (k // l) ≐ ((derLA a k) // (derLA a l)) := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [derLA, complement]
  | inr w => cases w with | mk n v => cases n <;> simp [derLA, complement]

theorem derLA_concat (a : α) (k l : Lang α) : derLA a (k • l) ≐ derLA a k • derLA a l := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl =>
    constructor
    . simp [concat, derLA]
    . intro ⟨x, y, x_in_lang, y_in_lang, h⟩
      cases h with
      | inl h => simp [h.choose_spec.2, derLA] at y_in_lang
      | inr h =>
        cases h with
        | inl h => simp [h.1, derLA] at x_in_lang
        | inr h => obtain ⟨_, _, _, _, x_sub,  _⟩ := h; simp [x_sub, derLA] at x_in_lang
  | inr w =>
    cases w with | mk n v =>
      cases n with
      | zero =>
        constructor
        . simp [concat, derLA]
        . intro ⟨x, y, x_in_lang, y_in_lang, ⟨n, x_sub, y_sub⟩⟩; simp [y_sub, derLA] at y_in_lang
      | succ n =>
        constructor
        . intro ⟨x, y, x_in_lang, y_in_lang, ⟨n', x_sub, y_sub⟩⟩; subst x_sub y_sub
          exact ⟨(Sum.inr ((n + n'.succ), v)), (Sum.inr (n.succ, v)), x_in_lang, y_in_lang, by simp [wc]; exists n'; grind⟩
        . intro ⟨x, y, x_in_lang, y_in_lang, ⟨n', x_sub, y_sub⟩⟩; subst x_sub y_sub
          exact ⟨(Sum.inr ((n + n'), a :: v)), Sum.inr (n, a :: v), by simp [Nat.succ_add] at x_in_lang; exact x_in_lang, y_in_lang, ⟨n', rfl, rfl⟩⟩

theorem derLA_star (a : α) (l : Lang α) : derLA a (l*) ≐ ▹I ∪ derLA a l := by
  intro w
  match w with
  | Sum.inl w => simp [derLA, union, step]
  | Sum.inr (n, v) =>
    cases n with
    | zero => simp [derLA, union, step]
    | succ n =>
      constructor
      · intro h
        left
        refine ⟨n, rfl, ?_⟩
        trivial
      · intro _
        exact star_help.inUnit (l := l) n (a :: v)


theorem derLA_la (a : α) (l : Lang α) : derLA a (la l) ≐ ▹(la (der a l)) := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [derLA, step]
  | inr w =>
    cases w with | mk n v =>
      cases n with
      | zero => simp [step, derLA]
      | succ n =>
        cases n with
        | zero => cases v <;> simp [step, derLA, la, der]
        | succ n => cases v <;> simp [step, derLA, la]

theorem derLA_step (a : α) (l : Lang α) : derLA a (▹l) ≐ ▹ (derLA a l) := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [step, derLA]
  | inr w =>
    cases w with | mk n v =>
      cases n with
      | zero => simp [step, derLA]
      | succ n => cases n <;> simp [step, derLA]
