module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace BrownCameron

/-- Independent vertex sets of each size. -/
noncomputable def layer {V : Type*} [Fintype V] (G : SimpleGraph V) (j : ℕ) :
    Finset (Finset V) := by
  classical
  exact G.indepSetFinset j

/-- The independence polynomial evaluated at a complex number. -/
noncomputable def independence {V : Type*} [Fintype V] (G : SimpleGraph V) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (G.indepNum + 1), ((layer G j).card : ℂ) * z^j

end BrownCameron
