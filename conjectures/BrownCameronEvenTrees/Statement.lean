module

public import conjectures.BrownCameronEvenTrees.IndependencePolynomial
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace BrownCameronEvenTrees

export BrownCameron (layer independence)

/-- Brown and Cameron, Conjecture 4.4. Write the even order as `2 * k`. -/
def Conjecture : Prop := ∀ (k : ℕ) (_ : 3 ≤ k) (T : SimpleGraph (Fin (2 * k))),
  T.IsTree → ∀ z : ℂ, independence T z = 0 → ‖z‖ ≤ (2^(k-2)+k+1 : ℕ)

end BrownCameronEvenTrees
