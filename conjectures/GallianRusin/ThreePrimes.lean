module

public import conjectures.GallianRusin.Coefficients
public import conjectures.GallianRusin.Factorization

@[expose] public section
namespace GallianRusin
open Polynomial

/-- At prime order the coefficient list consists entirely of ones. -/
theorem polynomial_prime (p : ℕ) (hp : p.Prime) :
    polynomial (List.replicate p 1) = cyclotomic p ℤ := by
  let : Fact p.Prime := ⟨hp⟩
  rw [polynomial_standard, cyclotomic_prime]
  rfl

/-- Coefficients of the nontrivial cyclotomic factors common to 30 and 105. -/
def commonFactor : ℕ → List ℤ
  | 3 => [1, 1, 1]
  | 5 => [1, 1, 1, 1, 1]
  | 15 => [1, -1, 0, 1, -1, 1, 0, -1, 1]
  | _ => []

theorem commonFactor_3 : polynomial (commonFactor 3) = cyclotomic 3 ℤ :=
  polynomial_prime 3 (by decide)

theorem commonFactor_5 : polynomial (commonFactor 5) = cyclotomic 5 ℤ :=
  polynomial_prime 5 (by decide)

theorem commonFactor_15 : polynomial (commonFactor 15) = cyclotomic 15 ℤ := by
  have a := table_product commonFactor (m := 15) [15, 3, 5] (by decide)
  have b := standard_factors (m := 15) (by decide) [15, 3, 5] (by decide) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at a b
  rw [commonFactor_3, commonFactor_5] at a
  apply mul_right_cancel₀ _ (a.trans b.symm)
  apply_rules [mul_ne_zero, Polynomial.cyclotomic_ne_zero]

/-- For primes `p, q, r`, the four entries record the exponents of the cyclotomic factors
of orders `p*q`, `p*r`, `q*r`, and `p*q*r`, in that order. -/
structure Code where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq

/-- The six bits specify which other primes divide each prime-sided die's increment. -/
def shape (mask : ℕ) : Code :=
  let bit (j : ℕ) := mask / 2 ^ j % 2
  ⟨bit 0 + bit 2, bit 1 + bit 4, bit 3 + bit 5,
    bit 0 * bit 1 + bit 2 * bit 3 + bit 4 * bit 5⟩

end GallianRusin
