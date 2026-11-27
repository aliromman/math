module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Defs.Filter

open Finset Filter

namespace AlabamaParadox

/-- There is no nonzero rational relation between the population shares.
Clearing denominators gives this equivalent integer formulation. -/
@[expose] public def IndependentShares {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * p i = 0 → ∀ i, a i = 0

/-- Hamilton gives each state its lower quota, then assigns the remaining
seats to states with the largest fractional remainders. -/
@[expose] public def Hamilton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (n : ℕ) (a : ι → ℤ) : Prop :=
  ∑ i, a i = (n : ℤ) ∧ ∃ winners : Finset ι,
    (∀ i, a i = ⌊(n : ℝ) * p i⌋ + if i ∈ winners then 1 else 0) ∧
    ∀ i ∈ winners, ∀ j ∉ winners, Int.fract ((n : ℝ) * p j) ≤ Int.fract ((n : ℝ) * p i)

/-- At least one state loses a seat when the house grows from n to n+1. -/
@[expose] public def Loss {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (n : ℕ) : Prop :=
  0 < n ∧ ∃ a b, Hamilton p n a ∧ Hamilton p (n + 1) b ∧ ∃ i, b i < a i

@[expose] public noncomputable def frequency (E : ℕ → Prop) (N : ℕ) : ℝ := by
  classical exact ((range N).filter E).card / (N : ℝ)

/-- Janson and Linusson's conjecture after Corollary 2.3 of the journal article
(Corollary 2.4 of the preprint) “The probability of the Alabama paradox”. -/
@[expose] public def Conjecture : Prop :=
  ∀ {m : ℕ} (p : Fin m → ℝ), (∀ i, 0 < p i) → ∑ i, p i = 1 → IndependentShares p →
    ∃ q : ℝ, Tendsto (frequency (Loss p)) atTop (nhds q) ∧ q ≤ 1 - 2 / Real.exp 1

end AlabamaParadox
