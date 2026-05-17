import Thesis.Syntax.Expressions
import Thesis.Semantics.Operators

open Expr

inductive MatchSet : Type
| inl : List Nat → MatchSet
| inr : List Nat → MatchSet
deriving Repr

namespace MatchSet
abbrev included : List Nat → MatchSet := MatchSet.inl
abbrev excluded : List Nat → MatchSet := MatchSet.inr
end MatchSet

instance : Membership Nat MatchSet where
  mem m n :=
    match m with
    | MatchSet.inl included => n ∈ included
    | MatchSet.inr excluded => n ∉ excluded


def matchesOfPlus (m₁ m₂ : MatchSet) : MatchSet :=
  match m₁ with
  | .inl included₁ =>
    match m₂ with
    | .inl included₂ => .included (included₁ ++ included₂)
    | .inr excluded₂ => .excluded (excluded₂.filter (λ n => !(List.elem n included₁)))
  | .inr excluded₁ =>
    match m₂ with
    | .inl included₂ => .excluded (excluded₁.filter (λ n => !(List.elem n included₂)))
    | .inr excluded₂ => .excluded (excluded₁.filter (λ n => List.elem n excluded₂))

def matchesOfIntersection (m₁ m₂ : MatchSet) : MatchSet :=
  match m₁ with
  | .inl included₁ =>
    match m₂ with
    | .inl included₂ => .included (included₁.filter (λ n => List.elem n included₂))
    | .inr excluded₂ => .included (included₁.filter (λ n => !(List.elem n excluded₂)))
  | .inr excluded₁ =>
    match m₂ with
    | .inl included₂ => .included (included₂.filter (λ n => !(List.elem n excluded₁)))
    | .inr excluded₂ => .excluded (excluded₁ ++ excluded₂)

def matchesOfComplement (m₁ m₂ : MatchSet) : MatchSet :=
  match m₁ with
  | .inl included₁ =>
    match m₂ with
    | .inl included₂ => .included (included₁.filter (λ n => !(List.elem n included₂)))
    | .inr excluded₂ => .included (included₁.filter (λ n => List.elem n excluded₂))
  | .inr excluded₁ =>
    match m₂ with
    | .inl included₂ => .excluded (excluded₁ ++ included₂)
    | .inr excluded₂ => .included (excluded₂.filter (λ n => !(List.elem n excluded₁)))

def matchesOfMult (m₁ m₂ : MatchSet) : MatchSet :=
  match m₁ with
  | .inl included₁ =>
    match m₂ with
    | .inl included₂ => .included (included₂.filter (λ n₂ => included₁.any (λ n₁ => Nat.ble n₂ n₁)))
    | .inr excluded₂ =>
      match included₁.max? with
      | none => .included []
      | some max => .included ((List.range (max + 1)).filter (λ n => !(List.elem n excluded₂)))
  | .inr _ => m₂

def matchesOfStar (m : MatchSet) : MatchSet :=
  match m with
  | .inl _ => .excluded []
  | .inr _ => .excluded []

def matchesOfLA (m : MatchSet) : MatchSet :=
  match m with
  | .inl included => if 0 ∈ included then .included [0] else .included []
  | .inr excluded => if 0 ∈ excluded then .included [] else .included [0]

def matchesOfStep (m : MatchSet) : MatchSet :=
  match m with
  | .inl included => .included (included.map Nat.succ)
  | .inr excluded => .excluded (0 :: excluded.map Nat.succ)

/-- Definition 4.3.1 — nullability set `N(r)`. -/
def N (r : Expr α) : MatchSet :=
  match r with
  | .empty => .included []
  | .unit => .excluded []
  | .top => .excluded []
  | .symbol _ => .included []
  | .plus r₁ r₂ => matchesOfPlus (N r₁) (N r₂)
  | .intersection r₁ r₂ => matchesOfIntersection (N r₁) (N r₂)
  | .complement r₁ r₂ => matchesOfComplement (N r₁) (N r₂)
  | .mult r₁ r₂ => matchesOfMult (N r₁) (N r₂)
  | .star _ => .excluded []
  | .la r => matchesOfLA (N r)
  | .step r => matchesOfStep (N r)
termination_by sizeOf r
