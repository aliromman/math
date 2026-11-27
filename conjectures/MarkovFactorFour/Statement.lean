module

public import conjectures.MarkovFactorFour.Farey

@[expose] public section
namespace MarkovFactorFour

/-- Evans, Veselov and Winn, Conjecture 8.1. The last inequality is i/a+j/b>1. -/
def Conjecture : Prop :=
  ∀ a b : ℕ, 0 < a → a ≤ b → Nat.Coprime a b → ∀ i j : ℕ,
    i < a → j < b → a*b < i*b + j*a → (4 : ℤ) ∣ (numerator a b).coeff (exponent i j)

end MarkovFactorFour
