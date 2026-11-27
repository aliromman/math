module

public import conjectures.MissingSumFringes.Window
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

/-- Length of the interval of possible sums for a subset of {0,...,n−1}. -/
def width (n : ℕ) : ℕ := 2*n-1

noncomputable def conditionalMean (n k : ℕ) (W : ℕ → Finset ℕ → ℕ) : ℝ :=
  (((range n).powerset.filter fun A ↦ (missing (width n) A).card=k).expect
    fun A ↦ (W n A : ℝ))

end MissingSumFringes
