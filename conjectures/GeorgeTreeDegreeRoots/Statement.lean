module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section
namespace GeorgeTreeDegreeRoots

/-- The degree polynomial evaluated at a complex number. Each vertex contributes one term. -/
noncomputable def degreeValue {V : Type*} [Fintype V] (G : SimpleGraph V) (z : ℂ) : ℂ := by
  classical exact ∑ v, z ^ G.degree v

/-- The degree roots of finite trees. Finite vertex sets can be labeled by `Fin n`. -/
def treeRoots : Set ℂ :=
  {z | ∃ n, ∃ G : SimpleGraph (Fin n), G.IsTree ∧ degreeValue G z = 0}

/-- Ian C. George, On the Degree Polynomial of Graphs, Conjecture 1 (2023). -/
def Conjecture : Prop :=
  (∀ z ∈ treeRoots, ‖z‖ < 1 → z.im = 0) ∧ ¬ Dense treeRoots

end GeorgeTreeDegreeRoots
