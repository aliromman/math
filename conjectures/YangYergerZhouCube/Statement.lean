module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Multiset.Replicate
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Fintype.Fin

@[expose] public section
namespace YangYergerZhouCube

open Finset
open scoped symmDiff

/-- The extra vertex is none. Cube coordinates differ on exactly one bit along an edge. -/
def Adj {ι : Type*} [DecidableEq ι] (anchor : Finset ι) :
    Option (Finset ι) → Option (Finset ι) → Prop
  | none, none => False
  | none, some x | some x, none => x = anchor
  | some x, some y => (x ∆ y).card = 1

def cube {ι : Type*} [DecidableEq ι] (a : Finset ι) : SimpleGraph (Option (Finset ι)) where
  Adj := Adj a
  symm := ⟨by rintro (_|x) (_|y) <;> simp [Adj,symmDiff_comm]⟩
  loopless := ⟨by rintro (_|x) <;> simp [Adj]⟩

/-- A pebbling step consumes two pebbles and puts one on an adjacent vertex. -/
inductive Moves {V : Type*} (edge : V → V → Prop) : Multiset V → Multiset V → Prop
  | refl (C) : Moves edge C C
  | step {u v} (rest) (h : edge u v) :
      Moves edge (rest + Multiset.replicate 2 u) (rest + {v})
  | trans {A B C} : Moves edge A B → Moves edge B C → Moves edge A C

def Supplies {V : Type*} (edge : V → V → Prop) (C D : Multiset V) : Prop :=
  ∃ rest, Moves edge C (D + rest)

/-- Place the specified number of pebbles at each vertex of a face. -/
def pack {ι V : Type*} (s : Finset ι) (node : Finset ι → V) (p : Finset ι → ℕ) : Multiset V :=
  ∑ x ∈ s.powerset, Multiset.replicate (p x) (node x)

/-- The pendant root has weight zero. All other weights use graph distance to that root. -/
noncomputable def inverseWeight {ι : Type*} [DecidableEq ι] (a : Finset ι) : Option (Finset ι) → ℚ
  | none => 0
  | some x => 1 / (cube a).dist (some x) none

noncomputable def distanceWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (a : Finset ι) (p : Finset ι → ℕ) : ℚ :=
  ∑ x ∈ (univ : Finset ι).powerset, (p x : ℚ) * inverseWeight a (some x)

/-- Yang, Yerger and Zhou, Conjecture 2. The parameter m is n − 1 in the paper. -/
def CubeWeightConjecture : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∀ anchor : Finset (Fin m),
    inverseWeight anchor none=0 ∧ (∀ x, 0 < inverseWeight anchor (some x)) ∧
    ∀ p : Finset (Fin m) → ℕ, ∀ atRoot : ℕ,
    ¬ Supplies (cube anchor).Adj
      (Multiset.replicate atRoot none + pack univ some p) {none} →
    distanceWeight anchor p ≤ distanceWeight anchor (fun _ => 1)

end YangYergerZhouCube
