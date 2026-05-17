import Thesis.Syntax.Expressions

namespace ExprDerivatives

open Expr

-- Definition 4.2.1 (Expression derivatives).
mutual
def D [DecidableEq α] (a : α) : Expr α → Expr α
  | .empty | .unit | .la _ | .step _ => ∅
  | .top => T // ▹T
  | .symbol x => if a = x then (ε // ▹ε) else ∅
  | .plus r₁ r₂ => (D a r₁) + (D a r₂)
  | .intersection r₁ r₂ => (D a r₁) ∩ (D a r₂)
  | .complement r₁ r₂ => (D a r₁) // (D a r₂)
  | .mult r₁ r₂ => ((D a r₁) • r₂) + ((DLA a r₁) • (D a r₂))
  | .star r => (D a r) • (r*)

  def DLA [DecidableEq α] (a : α) : Expr α → Expr α
    | .empty | .symbol _ => ∅
    | .unit => ▹ε
    | .top => ▹T
    | .plus r₁ r₂ => (DLA a r₁) + (DLA a r₂)
    | .intersection r₁ r₂ => (DLA a r₁) ∩ (DLA a r₂)
    | .complement r₁ r₂ => (DLA a r₁) // (DLA a r₂)
    | .mult r₁ r₂ => (DLA a r₁) • (DLA a r₂)
    | .star r => ▹ε + (DLA a r)
    | .la r => ▹(▷ (D a r))
    | .step r => ▹(DLA a r)
end

-- Definition 4.2.2 — Iterated match derivative
def D_word [DecidableEq α] (w : List α) (r : Expr α) : Expr α :=
  match w with
  | [] => r
  | a :: tl => D_word tl (D a r)

-- Definition 4.2.2 — Iterated lookahead derivative
def DLA_word [DecidableEq α] (w : List α) (r : Expr α) : Expr α :=
  match w with
  | [] => r
  | a :: tl => DLA_word tl (DLA a r)

-- Definition 4.2.4 — Iterated existential derivative
def xD [DecidableEq α] (w : List α) (r : Expr α) : Expr α :=
  match w with
  | [] => r
  | hd :: tl => xD tl ((D hd r) + (DLA hd r))
