module

public import conjectures.KarlovskySumBound.Statement

@[expose] public section
namespace KarlovskySumAttainment
open KarlovskySumBound (Solution upper)
open scoped BigOperators

def Conjecture3 : Prop := ∀ (k F : ℕ), 2 ≤ k → 0 < F →
  ((∃ x : Fin (k+2) → ℕ, Solution F x ∧ ((∑ i, x i) : ℕ) = upper k F ∧
    ∀ y : Fin (k+2) → ℕ, Solution F y → ∑ i,y i ≤ ∑ i,x i) ↔
  ∃ b : ℕ, 0 < b ∧ F+1=(k+b)*k.factorial)

end KarlovskySumAttainment
