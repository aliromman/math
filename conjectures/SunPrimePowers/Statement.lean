module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Nth

@[expose] public section

namespace SunPrimePowers

/-- Sun uses one-based indexing for the primes. -/
noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Conjecture 2.1 in Sun, *Conjectures involving arithmetical sequences* (2013).
The sum runs over the primes up to and including the `n`th prime. -/
def Conjecture : Prop :=
  ∀ a : ℝ, 0 < a → ∀ n : ℕ, 2 * ⌈a⌉₊ ^ 2 + ⌈a⌉₊ + 6 ≤ n →
    (∑ p ∈ (Finset.range (primeAt n + 1)).filter Nat.Prime, (p : ℝ) ^ a) / n <
      (primeAt n : ℝ) ^ a / (a + 1)

end SunPrimePowers
