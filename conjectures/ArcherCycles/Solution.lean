module

public import conjectures.ArcherCycles.Count
import Mathlib.Tactic.LinearCombination

@[expose] public section
namespace ArcherCycles
open Finset PowerSeries

private noncomputable def decreasing : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦ (family true n).card

private theorem coeff_series (n : ℕ) : coeff n series = ((positive n).card : ℚ) := by
  rw [card_positive]
  by_cases h : n=0 <;> simp [series,h]

private theorem coeff_all (n : ℕ) : coeff n (1+series) = ((valid n).card : ℚ) := by
  cases n <;> simp [series,PowerSeries.coeff_one]

private theorem shift (s : PowerSeries ℚ) (n : ℕ) :
    coeff (n+1) (X*s) = coeff n s := by
  simp

theorem ordinary_series : ordinary = X*(1+series) := by
  ext n
  cases n with
  | zero => simp [ordinary]
  | succ n => rw [shift,coeff_all]; simp [ordinary]

private theorem series_rec : series = X*(1+series+series*decreasing) := by
  ext n
  cases n with
  | zero => simp [series]
  | succ n =>
    rw [shift,map_add,coeff_all,coeff_mul]
    simp only [coeff_series,decreasing,coeff_mk,card_positive (n+1),Nat.succ_ne_zero,
      ↓reduceIte]
    exact_mod_cast count_all n

private theorem decreasing_rec : decreasing = 1+X*(1+series*decreasing) := by
  ext n
  cases n with
  | zero => simp [decreasing,family,Finset.filter_singleton]
  | succ n =>
    rw [map_add,shift,map_add,coeff_one,coeff_one,coeff_mul]
    simp only [Nat.succ_ne_zero,↓reduceIte,zero_add,decreasing,coeff_mk,coeff_series]
    exact_mod_cast count_decreasing n

/-- The unique split at the minimum gives the two contributions from the empty
and nonempty upper block. Eliminating the auxiliary series gives a quadratic. -/
theorem quadratic : series = X+2*X*series+X*(1-X)*series^2 := by
  have h : decreasing = 1+series-X*series := by
    linear_combination decreasing_rec - series_rec
  have f := series_rec
  rw [h] at f
  linear_combination f

theorem resolved : Conjecture := by
  refine ⟨1-2*X-2*X*(1-X)*series,by simp,?_,?_⟩
  · linear_combination -4 * X * (1-X) * quadratic
  · linear_combination 2 * quadratic

/-- info: 'ArcherCycles.resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolved

end ArcherCycles
