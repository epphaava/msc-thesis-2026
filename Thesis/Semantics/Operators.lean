import Thesis.Semantics.StructuredWords

namespace Operators

open StructuredWords

-- Definition 3.3.1 (Structured word concatenation `wc`).
def wc {α} (x y w : Word α) : Prop :=
  match w with
  | Sum.inl ((hd, tl), v) =>
      (∃ n, x = Sum.inr (n, hd :: tl ++ v) ∧ y = Sum.inl ((hd, tl), v))
      ∨
      (x = Sum.inl ((hd, tl), v) ∧ y = Sum.inr (0, v))
      ∨
      (∃ (xs : List α) (z : α) (zs : List α),
          xs ++ z :: zs = tl ∧
          x = Sum.inl ((hd, xs), z :: zs ++ v) ∧
          y = Sum.inl ((z, zs), v))
  | Sum.inr (n, v) =>
      ∃ n₁, x = Sum.inr (n + n₁, v) ∧ y = Sum.inr (n, v)

-- Definition 3.3.2 (Language operators).
def empty {α} : Lang α := λ _ => False
notation "∅" => empty

def unit : Lang α := λ u =>
  match u with
  | Sum.inr _ => True
  | _ => False
notation "I" => unit

-- helper operator for unit
def unit_n (n : Nat) : Lang α := λ u =>
  match u with
  | Sum.inr (n', _) => n = n'
  | _ => False

def top : Lang α := λ _ => True
notation "T" => top

def symb {α} (a : α) : Lang α := λ u =>
  match u with
  | Sum.inl (⟨hd , []⟩, _) => a = hd
  | _ => False
prefix:max "#" => symb

def union (k l : Lang α) : Lang α := λ u =>
  k u ∨ l u
infixr:55 " ∪ " => union

def intersection (k l : Lang α) : Lang α := λ u =>
  k u ∧ l u
infixl:55 " ∩ " => intersection

def complement (k l : Lang α) : Lang α := λ u =>
  k u ∧ ¬ l u
infixl:30 " // " => complement

def concat {α} (k l : Lang α) : Lang α := λ w =>
  ∃ x y, k x ∧ l y ∧ wc x y w
infixr:60 " • " => concat

-- helper operator for star
inductive star_help {α} (l : Lang α) : Word α → Prop
| inUnit : ∀ n y, star_help l (Sum.inr (n, y))
| inConcat :
  ∀ x y w,
  l x →
  star_help l y →
  wc x y w →
  star_help l w

def star (l : Lang α) : Lang α :=
  star_help l
postfix:max "*" => star

def la (l : Lang α) : Lang α := λ u =>
  match u with
  | Sum.inr (0, v) =>
    match v with
    | [] => l (Sum.inr (0, []))
    | y :: ys => l (Sum.inl ((y, ys), []))
  | _ => False
prefix:max "▷" => la

def step (l : Lang α) : Lang α := λ u =>
  match u with
  | Sum.inr (n, ys) => ∃ n', n = .succ n' ∧  l (Sum.inr (n', ys))
  | _ => False
prefix:max "▹" => step

end Operators
