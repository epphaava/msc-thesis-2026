namespace StructuredWords

-- Structured words ----------------------------------


def NEList (α : Type) := α × List α
def toList (l : NEList α) := l.fst :: l.snd

-- Definition 3.1.1 (Structured words).
def Word (α : Type) := NEList α × List α ⊕ Nat × List α

def Word.match_part {α} (w : NEList α × List α) : NEList α :=
  w.1

def Word.empty_prefix_index {α} (w : Nat × List α) : Nat :=
  w.1

def Word.lookahead_part {α} (w : Word α) : List α :=
  match w with
  | Sum.inl (_, ys) => ys
  | Sum.inr (_, ys) => ys

def Word.word_to_list {α} : Word α → List α
  | Sum.inl (xs, ys) => toList xs ++ ys
  | Sum.inr (_, ys)  => ys

def Word.word_length {α} (w : Word α) : Nat :=
  match w with
  | Sum.inl (x, y) => (toList x).length + y.length
  | Sum.inr (_, y) => y.length

export Word (match_part empty_prefix_index lookahead_part word_to_list word_length)

-- Languages over structured words --------------------------

def Lang (α : Type) : Type := Word α → Prop


-- Subset and equality relations on Lang -------------------

def subset (l₁ l₂ : Lang α) := ∀ (u : Word α), l₁ u → l₂ u
infix:25 " ⊆ " => subset

def subsetAll {α} (Ls : List (Lang α)) (L : Lang α) : Prop :=
  ∀ l ∈ Ls, l ⊆ L
infix:25 " ⊆ " => subsetAll

def LEq (k l : Lang α) :=
 ∀ u, k u ↔ l u
infixl:50 " ≐ " => LEq

end StructuredWords
