module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs

@[expose] public section
namespace KarlovskySumBound
open scoped BigOperators

/-- Equation (17), with the terms listed in strictly increasing order. -/
def Solution {n : ℕ} (F : ℕ) (x : Fin n → ℕ) : Prop :=
  (∀ i, 0 < x i) ∧ StrictMono x ∧ ∏ i, x i = F * ∑ i, x i

/-- The bound in equation (18), with n = k + 2. -/
def upper (k F : ℕ) : ℚ :=
  (F+1 : ℚ)*((F : ℚ)+(k : ℚ)*(k+1).factorial/2+1)/k.factorial

def Conjecture2 : Prop := ∀ (k F : ℕ), 2 ≤ k → 0 < F →
  ∀ x : Fin (k+2) → ℕ, Solution F x → ((∑ i, x i) : ℕ) ≤ upper k F

end KarlovskySumBound
