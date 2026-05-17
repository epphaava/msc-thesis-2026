import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators

namespace Expr

open StructuredWords
open Operators

-- Definition 4.1.1 (Expression syntax).
inductive Expr (α : Type) : Type
| empty : Expr α
| unit : Expr α
| top : Expr α
| symbol : α → Expr α
| plus : Expr α → Expr α → Expr α
| intersection : Expr α → Expr α → Expr α
| complement : Expr α → Expr α → Expr α
| mult : Expr α → Expr α → Expr α
| star : Expr α → Expr α
| la : Expr α → Expr α
| step : Expr α → Expr α
deriving Repr

notation "∅" => Expr.empty
notation "ε" => Expr.unit
notation "T" => Expr.top
prefix:max "#" => Expr.symbol
infixr:55 "+" => Expr.plus
infixl:55 " ∩ " => Expr.intersection
infixl:30 " // " => Expr.complement
infixr:60 " • " => Expr.mult
postfix:max "*" => Expr.star
prefix:max "▷" => Expr.la
prefix:max "▹" => Expr.step

-- Definition 4.1.2 (Denotational semantics ⟦·⟧).
def sem [DecidableEq α] (r : Expr α) : Lang α :=
  match r with
  | .empty => ∅
  | .unit => I
  | .top => T
  | .symbol x => # x
  | .plus r₁ r₂ => (sem r₁) ∪ (sem r₂)
  | .intersection r₁ r₂ => (sem r₁) ∩ (sem r₂)
  | .complement r₁ r₂ => (sem r₁) // (sem r₂)
  | .mult r₁ r₂ => (sem r₁) • (sem r₂)
  | .star r => (sem r)*
  | .la r => la (sem r)
  | .step r => ▹ (sem r)

variable {α : Type} [DecidableEq α]
