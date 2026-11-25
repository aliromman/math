module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace BrownCameronEvenTrees

/-- Independent vertex sets of each size. -/
noncomputable def layer {V : Type*} [Fintype V] (G : SimpleGraph V) (j : ℕ) :
    Finset (Finset V) := by
  classical
  exact G.indepSetFinset j

/-- The independence polynomial evaluated at a complex number. -/
noncomputable def independence {V : Type*} [Fintype V] (G : SimpleGraph V) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (G.indepNum + 1), ((layer G j).card : ℂ) * z^j

/-- Brown and Cameron, Conjecture 4.4. Write the even order as `2 * k`. -/
def Conjecture : Prop := ∀ (k : ℕ) (_ : 3 ≤ k) (T : SimpleGraph (Fin (2 * k))),
  T.IsTree → ∀ z : ℂ, independence T z = 0 → ‖z‖ ≤ (2^(k-2)+k+1 : ℕ)

end BrownCameronEvenTrees
