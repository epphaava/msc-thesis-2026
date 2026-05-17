import Thesis.Syntax.Expressions
import Thesis.Syntax.Derivatives
import Thesis.Syntax.Nullability
import Thesis.Syntax.NullabilityCorrectness
import Thesis.Syntax.DerivativeCorrectness
import Thesis.Algorithm
import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

/-
Examples from the thesis
-/

open Expr
open ExprDerivatives
open NullabilityCorrect
open DerCorrect
open Algorithm
open StructuredWords
open Operators

variable {α : Type} [DecidableEq α]


-- Example 3.2.1

def L_3_2_1 : Lang Char := λ w =>
    w = Sum.inl (('a', ['b']), ['c', 'd']) ∨
    w = Sum.inr (2, ['a', 'b'])

example : der 'a' L_3_2_1 (Sum.inl (('b', []), ['c', 'd'])) := by
  simp [der, L_3_2_1]; trivial

example (w : Word Char) : ¬ der 'b' L_3_2_1 w := by
  intro h
  match w with
  | Sum.inl ((hd, tl), v) => simp [der, L_3_2_1] at h; cases h
  | Sum.inr (n, v) => cases n <;> simp [der, L_3_2_1] at h; cases h

example : derLA 'a' L_3_2_1 (Sum.inr (3, ['b'])) := by
  simp [derLA, L_3_2_1]


-- Example 3.4.1

def K_3_4_1 : Lang Char := λ w => w = Sum.inl (('a', []), ['b', 'c', 'd'])

def L_3_4_1 : Lang Char := λ w => w = Sum.inl (('b', ['c']), ['d'])

example : der 'a' K_3_4_1 (Sum.inr (0, ['b', 'c', 'd'])) := by
  simp [der, K_3_4_1]; trivial

example : derLA_word ['b', 'c'] (der 'a' K_3_4_1) (Sum.inr (2, ['d'])) := by
  simp [derLA_word, derLA, der, K_3_4_1]; trivial

example : der_word ['b', 'c'] L_3_4_1 (Sum.inr (0, ['d'])) := by
  simp [der_word, der, L_3_4_1]; trivial

example : derLA 'd' (der_word ['a', 'b', 'c'] (K_3_4_1 • L_3_4_1)) (Sum.inr (1, [])) := by
  simp [derLA, der_word, der, concat, K_3_4_1, L_3_4_1, wc]
  exists [], 'b', ['c']


-- Example 4.1.1

def r_4_1_1_exact : Expr Char := #'a' • ▷#'b'
def r_4_1_1_prefix : Expr Char := #'a' • ▷(#'b' • T)

example : sem r_4_1_1_exact (Sum.inl (('a', []), ['b'])) := by
  exists (Sum.inl (('a', []), ['b'])); simp [sem, la, symb, wc]; trivial

example : sem r_4_1_1_prefix (Sum.inl (('a', []), ['b', 'c'])) := by
  exists (Sum.inl (('a', []), ['b', 'c'])); simp [sem, la, symb, wc, concat, top];
  constructor
  . exists (Sum.inl (('b', []), ['c'])); simp
    exists (Sum.inl (('c', []), [])); right;
    exists [], 'c', []
  . trivial

example : ¬ sem r_4_1_1_exact (Sum.inl (('a', []), ['b', 'c'])) := by
  intro h
  obtain ⟨x, y, hx, hy, hwc⟩ := h
  match x with
  | Sum.inl ((hd, tl), v) =>
    cases hwc with
    | inl hwc => obtain ⟨_, h, _⟩ := hwc; simp at h
    | inr hwc =>
      cases hwc with
      | inl hwc => obtain ⟨_, _⟩ := hwc; subst y; simp [sem, la, symb] at hy
      | inr hwc => obtain ⟨xs, z, zs, htl, _, _⟩ := hwc; simp at htl
  | Sum.inr (n, v) => cases n <;> simp [sem, symb] at hx


-- Example 4.2.1

def r_4_2_1 : Expr Char := #'a' • ▷#'b'

example : D 'a' r_4_2_1 = ((ε // ▹ε) • ▷#'b') + ∅ • ∅ := by
  simp [r_4_2_1, D, DLA]

example : DLA 'a' r_4_2_1 = ∅ • DLA 'a' (▷ #'b') := by
  simp [r_4_2_1, DLA]

example : sem (D 'a' r_4_2_1) ≐ sem ((ε // ▹ε) • ▷#'b') := by
  intro w
  simp [sem, r_4_2_1, D, union, DLA, concat, empty]

example : sem (DLA 'a' r_4_2_1) ≐ ∅ := by
  intro w
  simp [r_4_2_1, empty]; intro h
  simp [DLA, sem, concat, empty] at h

-- Example 5.3
#eval findAllMatches (α := Char) ((#'a')* • ▷((#'a')*)) ['a']
