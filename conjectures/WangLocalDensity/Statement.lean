module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Finset.Powerset

@[expose] public section
namespace WangLocalDensity
open Finset SimpleGraph
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- All nonempty vertex sets that induce a connected subgraph. -/
noncomputable def subtrees : Finset (Finset V) :=
  univ.powerset.filter fun S ↦ (G.induce (S : Set V)).Connected

/-- Expected fraction of vertices outside S in a uniform subtree that contains S. -/
def familyDensity (F : Finset (Finset V)) (S : Finset V) : ℚ :=
  let supersets := F.filter (fun U ↦ S ⊆ U)
  ((∑ U ∈ supersets, (U.card-S.card)) : ℕ) /
    ((supersets.card * (Fintype.card V-S.card) : ℕ) : ℚ)

noncomputable def density (S : Finset V) : ℚ := familyDensity (subtrees G) S

/-- Wang's Conjecture 20. The local density is defined at proper subtrees. -/
def Conjecture : Prop := ∀ (n : ℕ) (T : SimpleGraph (Fin n)), T.IsTree →
  ∀ S ∈ subtrees T, S ≠ univ →
    (∀ U ∈ subtrees T, U ≠ univ → density T U ≤ density T S) →
      ∃ v ∈ S, ∃! w, T.Adj v w

end WangLocalDensity
