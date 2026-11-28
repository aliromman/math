module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Set.OrdConnected

@[expose] public section
open scoped Pointwise

namespace BuchweitzGapset

/-- The set of sums of exactly `n` elements of `A`, with repetitions allowed. -/
def sums (A : Finset ℤ) : ℕ → Finset ℤ
  | 0 => {0}
  | n + 1 => sums A n + A

/-- The excess in Buchweitz's bound for an iterated sumset. -/
def beta (A : Finset ℤ) (n : ℕ) : ℤ :=
  ((sums A n).card : ℤ) - (2 * (n : ℤ) - 1) * ((A.card : ℤ) - 1)

/-- The positive support of the excess at orders at least two. -/
def obstruction (A : Finset ℤ) : Set ℕ := {n | 2 ≤ n ∧ 0 < beta A n}

/-- A finite set of positive integers whose complement in the naturals is closed under addition. -/
def IsGapset (A : Finset ℤ) : Prop :=
  (∀ x ∈ A, 0 < x) ∧ ∀ u v : ℕ, (u : ℤ) ∉ A → (v : ℤ) ∉ A → ((u + v : ℕ) : ℤ) ∉ A

/-- Eliahou, García-García, Marín-Aragón and Vigneron-Tenorio, Question 4.1. -/
def Conjecture : Prop := ∀ A : Finset ℤ, (obstruction A).OrdConnected

/-- The same question restricted to gapsets of numerical semigroups. -/
def GapsetConjecture : Prop := ∀ A : Finset ℤ, IsGapset A → (obstruction A).OrdConnected

/-- Weak unimodality on the positive orders. No middle value can be strictly
less than both outer values. This also permits monotone sequences. -/
def UnimodalExcess (A : Finset ℤ) : Prop :=
  ∀ i j k : ℕ, 0 < i → i ≤ j → j ≤ k → min (beta A i) (beta A k) ≤ beta A j

/-- Eliahou, García-García, Marín-Aragón and Vigneron-Tenorio, Question 4.2. -/
def UnimodalityQuestion : Prop := ∀ A : Finset ℤ, UnimodalExcess A

end BuchweitzGapset
