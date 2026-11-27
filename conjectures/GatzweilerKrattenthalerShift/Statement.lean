module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
open Polynomial
namespace GatzweilerKrattenthalerShift

/-- The numerator at shift `m`. At shift zero this is the denominator of equation (2). -/
noncomputable def factors (m n : ℕ) (a : ℕ → ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.Icc 1 n, (1 - X^(m+i))^(a i)

/-- Gatzweiler and Krattenthaler, Conjecture 4. The polynomial identity specifies the quotient. -/
def Conjecture : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → n ≤ m → ∀ a : ℕ → ℕ, ∀ P : ℝ[X],
    factors 0 n a * P = factors m n a → ∀ j : ℕ, 0 ≤ P.coeff j

end GatzweilerKrattenthalerShift
