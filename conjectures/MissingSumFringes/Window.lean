module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
namespace MissingSumFringes
open Finset
open scoped Pointwise Classical

/-- The sums absent from the first t nonnegative integers. -/
def missing (t : ℕ) (A : Finset ℕ) : Finset ℕ := (range t) \ (A+A)

/-- Probability that the prefix has m missing sums and ends at a missing sum. -/
noncomputable def window (m t : ℕ) : ℝ :=
  (((range t).powerset.filter fun A => (missing t A).card=m ∧ (t=0 ∨ t-1∈missing t A)).card : ℝ)/(2:ℝ)^t

end MissingSumFringes
