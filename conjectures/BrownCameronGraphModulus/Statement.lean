module

public import conjectures.BrownCameronEvenTrees.IndependencePolynomial

@[expose] public section

namespace BrownCameronGraphModulus

export BrownCameron (layer independence)

/-- The three upper bounds in Brown and Cameron, Conjecture 4.2. -/
def bound (n : ℕ) : ℕ :=
  if n % 3 = 0 then 2 * 3 ^ ((n - 3) / 3) + n / 3
  else if n % 3 = 1 then 3 ^ ((n - 1) / 3) + (n - 1) / 3
  else 4 * 3 ^ ((n - 5) / 3) + (n + 1) / 3

/-- Every independence root of every graph of order at least three obeys the bound. -/
def Conjecture : Prop := ∀ (n : ℕ) (_ : 3 ≤ n) (G : SimpleGraph (Fin n)),
  ∀ z : ℂ, independence G z = 0 → ‖z‖ ≤ (bound n : ℝ)

end BrownCameronGraphModulus
