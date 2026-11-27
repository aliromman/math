module

public import Mathlib.Data.List.Basic

@[expose] public section
namespace DefantLinHomometry

abbrev Vec := List ℕ

/-- A north step is true and an east step is false. Read the heights from the origin. -/
def heights (path : List Bool) : Vec :=
  path.scanl (fun h north => if north then h + 1 else h) 0

/-- Enumerate bracket vectors, starting at the right end. The last occurrence of
each path height is fixed. An entry k bounds all later entries through the last
occurrence of height k. These are conditions (I)–(III) of Definition 3.2. -/
def vectorsFrom (top : ℕ) : Vec → List Vec
  | [] => [[]]
  | h :: tail =>
    let choices := if tail.head? == some h then List.range' h (top + 1 - h) else [h]
    (vectorsFrom top tail).flatMap fun rest =>
      choices.filterMap fun k =>
        if (tail.zip rest).all (fun (r, b) => r > k || b ≤ k) then some (k :: rest) else none

def lattice (path : List Bool) : List Vec :=
  let v := heights path
  vectorsFrom (v.getLastD 0) v

/-- Componentwise comparison on bracket vectors of common length. -/
def below : Vec → Vec → Bool
  | [], [] => true
  | a :: as, b :: bs => a ≤ b && below as bs
  | _, _ => false

def meet (x y : Vec) : Vec := x.zipWith min y

/-- A lower cover is a maximal strict predecessor in the componentwise order. -/
def LowerCover (B : List Vec) (c x : Vec) : Prop :=
  c ∈ B ∧ c ≠ x ∧ below c x = true ∧
    ∀ z ∈ B, z ≠ x → below z x = true → below c z = true → z = c

/-- Proposition 2.2. Row(x) is the greatest z such that z ∧ x is the meet of
the lower covers of x. For the bottom element this last meet is x. -/
def RowDegree (B : List Vec) (x y : Vec) (d : ℕ) : Prop :=
  x ∈ B ∧ y ∈ B ∧ ∃ C : List Vec, C.Nodup ∧
    (∀ c, c ∈ C ↔ LowerCover B c x) ∧ C.length = d ∧
    let pop := C.foldl meet x
    meet x y = pop ∧ ∀ z ∈ B, meet x z = pop → below z y = true

abbrev Visit := Vec × ℕ

def adjacent (O : List Visit) : List (Visit × Visit) := O.zip (O.drop 1 ++ O.take 1)

def Orbit (B : List Vec) (O : List Visit) : Prop :=
  O ≠ [] ∧ (O.map Prod.fst).Nodup ∧
    ∀ pair ∈ adjacent O, RowDegree B pair.1.1 pair.2.1 pair.1.2

def degreeSum (O : List Visit) : ℕ := (O.map Prod.snd).sum

/-- Defant and Lin, Conjecture 10.2. -/
def Homometric : Prop := ∀ path : List Bool, ∀ O P : List Visit,
  Orbit (lattice path) O → Orbit (lattice path) P → O.length = P.length →
    degreeSum O = degreeSum P

end DefantLinHomometry
