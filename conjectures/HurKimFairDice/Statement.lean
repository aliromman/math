module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Count
public import Mathlib.Logic.Relation

@[expose] public section
namespace HurKimFairDice

/-- Position k in the word is the die that bears the face numbered k+1. -/
abbrev Die := Fin 3
abbrev Word := List Die

/-- The number of rolls in which x beats y. Each occurrence of y loses
to the x faces on its right. -/
def wins (x y : Die) : Word → ℕ
  | [] => 0
  | a :: w => (if a = y then w.count x else 0) + wins x y w

def equalCounts (w : Word) : Bool :=
  w.count 0 == w.count 1 && w.count 1 == w.count 2

def Fair (w : Word) : Prop :=
  let n := w.count 0
  0 < n ∧ equalCounts w = true ∧
    2*wins 0 1 w = n^2 ∧ 2*wins 1 2 w = n^2 ∧ 2*wins 2 0 w = n^2

def segment (w : Word) (i j : ℕ) : Word := (w.drop i).take (j-i)

/-- Lemma 2 exchanges two disjoint adjacent pairs xy and yx simultaneously. -/
def exchange (w : Word) (i j : ℕ) : Word :=
  let u := (w.drop i).take 2
  let v := (w.drop j).take 2
  if i+2 ≤ j ∧ j+2 ≤ w.length ∧ u = v.reverse then
    w.take i ++ v ++ segment w (i+2) j ++ u ++ w.drop (j+2)
  else w

/-- Lemma 3 interchanges a permutation of the three letters and a word
with equal letter counts. Both directions are allowed in every context.
The selected interval starts at i and ends just before j. -/
def shift (w : Word) (i j : ℕ) (front : Bool) : Word :=
  let k := if front then i+3 else j-3
  let u := segment w i k
  let v := segment w k j
  let triple := if front then u else v
  let other := if front then v else u
  if i+3 ≤ j ∧ j ≤ w.length ∧ triple.Nodup ∧ equalCounts other = true then
    w.take i ++ v ++ u ++ w.drop j
  else w

inductive Step (w : Word) : Word → Prop
  | exchange (i j : Fin (w.length+1)) : Step w (HurKimFairDice.exchange w i j)
  | shift (i j : Fin (w.length+1)) (front : Bool) : Step w (HurKimFairDice.shift w i j front)

abbrev Similar := Relation.ReflTransGen Step

/-- Hur and Kim, Conjecture 1, equivalently Conjecture 3.5 of the preprint. -/
def Conjecture : Prop := ∀ w : Word, Fair w → 6 ∣ w.length ∧
  ∃ (x y z : Die) (k : ℕ), [x,y,z].Nodup ∧
    Similar w (List.replicate k [x,y,z,z,y,x]).flatten

end HurKimFairDice
