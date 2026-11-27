module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.LiminfLimsup

@[expose] public section
namespace CFPLogDensity

open Finset Filter

/-- The sums of finite sets of distinct positive integers of one color. -/
def subsetSums {r : ℕ} (color : ℕ → Fin r) (i : Fin r) : Set ℕ :=
  {m | ∃ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ color a = i) ∧ ∑ a ∈ A, a = m}

noncomputable def logMass (S : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ (Icc 1 N).filter (· ∈ S), (k : ℝ)⁻¹

/-- Sample the upper logarithmic density at integer cutoffs. -/
noncomputable def sampledDensity (S : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => logMass S N / Real.log N) atTop

/-- Upper logarithmic density at real cutoffs, as in the original statement. -/
noncomputable def upperLogDensity (S : Set ℕ) : ℝ :=
  limsup (fun x : ℝ => logMass S ⌊x⌋₊ / Real.log x) atTop

/-- Every part of a partition contains a positive integer. -/
def UsesAll {r : ℕ} (color : ℕ → Fin r) : Prop := ∀ i, ∃ n, 0 < n ∧ color n = i

/-- The best guaranteed upper logarithmic density among the color classes. -/
noncomputable def densityConstant (r : ℕ) : ℝ :=
  ⨅ color : {f : ℕ → Fin r // UsesAll f}, ⨆ i : Fin r, upperLogDensity (subsetSums color.val i)

noncomputable def value (r : ℕ) (b : ℝ) : ℝ :=
  (1 - 1 / (2*b)) / (1 - 1/b^r)

def Root (r : ℕ) (b : ℝ) : Prop :=
  1 < b ∧ b^r + (r : ℝ) - 1 = 2*(r : ℝ)*b

/-- Conlon, Fox and Pham, Conjecture 10. -/
def Conjecture : Prop := ∀ r : ℕ, 3 ≤ r →
  (∃! b : ℝ, Root r b) ∧ ∀ b : ℝ, Root r b →
    let c := (1-1/(2*b))*(1+1/(2*(r:ℝ)*b-r))
    densityConstant r = c ∧
    ∃ color : ℕ → Fin r, UsesAll color ∧ (⨆ i, upperLogDensity (subsetSums color i)) = c

end CFPLogDensity
