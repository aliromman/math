module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace BrownCameronGraphModulus

/-- Independent vertex sets of each size. -/
noncomputable def layer {V : Type*} [Fintype V] (G : SimpleGraph V) (j : ℕ) :
    Finset (Finset V) := by
  classical
  exact G.indepSetFinset j

/-- The independence polynomial evaluated at a complex number. -/
noncomputable def independence {V : Type*} [Fintype V] (G : SimpleGraph V) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (G.indepNum + 1), ((layer G j).card : ℂ) * z^j

/-- The three upper bounds in Brown and Cameron, Conjecture 4.2. -/
def bound (n : ℕ) : ℕ :=
  if n % 3 = 0 then 2 * 3 ^ ((n - 3) / 3) + n / 3
  else if n % 3 = 1 then 3 ^ ((n - 1) / 3) + (n - 1) / 3
  else 4 * 3 ^ ((n - 5) / 3) + (n + 1) / 3

/-- Every independence root of every graph of order at least three obeys the bound. -/
def Conjecture : Prop := ∀ (n : ℕ) (_ : 3 ≤ n) (G : SimpleGraph (Fin n)),
  ∀ z : ℂ, independence G z = 0 → ‖z‖ ≤ (bound n : ℝ)

end BrownCameronGraphModulus
