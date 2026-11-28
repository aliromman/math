module

public import conjectures.BilleyFahrbachTalmageClassification.Kernel
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
namespace BilleyFahrbachTalmageClassification

theorem difference_real_part {s y : ℝ} (hy : y ∈ Set.Icc 0 1) :
    (difference s y).re = ((1+y)/2)^s-((1-y)/2)^s := by
  rw [difference, ←Complex.ofReal_cpow (by linarith [hy.1] : 0 ≤ (1+y)/2),
    ←Complex.ofReal_cpow (by linarith [hy.2] : 0 ≤ (1-y)/2)]
  rfl

private theorem power_diff_ge {j : ℕ} (hj : 1 ≤ j) {s u v : ℝ} (hs0 : j ≤ s)
    (hs1 : s ≤ j+1) (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) (hsum : u+v=1) :
    u^(j+1)-v^(j+1) ≤ u^s-v^s := by
  let d := u^(j+1)-v^(j+1)
  have hd : 0 ≤ d := sub_nonneg.mpr (pow_le_pow_left₀ hv.le hvu _)
  let f (t : ℝ) := (v/u)^t + d*(u⁻¹)^t
  have hconv : ConvexOn ℝ Set.univ f := by
    exact (convexOn_rpow_left (div_pos hv hu)).add ((convexOn_rpow_left (inv_pos.mpr hu)).smul hd)
  have iff_ (t : ℝ) : f t ≤ 1 ↔ d ≤ u^t-v^t := by
    dsimp only [f]
    rw [Real.div_rpow hv.le hu.le,Real.inv_rpow hu.le,←div_eq_mul_inv,←add_div,
      div_le_one (Real.rpow_pos_of_pos hu t)]
    constructor <;> intro h <;> linarith
  have hleft : f j ≤ 1 := by
    rw [iff_,Real.rpow_natCast,Real.rpow_natCast]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hh := mul_nonneg (mul_nonneg hu.le hv.le)
      (sub_nonneg.mpr (pow_le_pow_left₀ hv.le hvu k))
    dsimp [d]
    simp only [pow_succ]
    linear_combination hh + ((u^k)*u - (v^k)*v)*hsum
  have hright : f ((j:ℝ)+1) ≤ 1 := by
    rw [iff_,←Nat.cast_succ,Real.rpow_natCast,Real.rpow_natCast]
  apply (iff_ s).mp
  apply (hconv.le_on_segment (Set.mem_univ _) (Set.mem_univ _ ) ?_).trans (max_le hleft hright)
  rw [segment_eq_Icc (by linarith : (j:ℝ) ≤ j+1)]
  exact ⟨hs0,hs1⟩

/-- The smaller endpoint value bounds the power difference throughout a unit interval. -/
theorem difference_ge_next {j : ℕ} (hj : 1 ≤ j) {s y : ℝ} (hs0 : j ≤ s)
    (hs1 : s ≤ j+1) (hy : y ∈ Set.Icc 0 1) :
    (difference ((j+1:ℕ):ℂ) y).re ≤ (difference s y).re := by
  rw [show ((j+1:ℕ):ℂ) = (((j+1:ℕ):ℝ):ℂ) by norm_num,
    difference_real_part hy,difference_real_part hy,Real.rpow_natCast,Real.rpow_natCast]
  by_cases he : y=1
  · subst y
    have hs : s ≠ 0 := by
      have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
      linarith
    norm_num [Real.zero_rpow hs]
  · exact power_diff_ge hj hs0 hs1 (by linarith [hy.1]) (by linarith [lt_of_le_of_ne hy.2 he])
      (by linarith [hy.1]) (by ring)

theorem difference_next_nonneg (j : ℕ) {y : ℝ} (hy : y ∈ Set.Icc 0 1) :
    0 ≤ (difference ((j+1:ℕ):ℂ) y).re := by
  rw [show ((j+1:ℕ):ℂ) = (((j+1:ℕ):ℝ):ℂ) by norm_num,
    difference_real_part hy,Real.rpow_natCast,Real.rpow_natCast]
  exact sub_nonneg.mpr (pow_le_pow_left₀ (by linarith [hy.2]) (by linarith [hy.1]) _)

theorem difference_next_pos (j : ℕ) {y : ℝ} (hy : y ∈ Set.Ioc 0 1) :
    0 < (difference ((j+1:ℕ):ℂ) y).re := by
  rw [show ((j+1:ℕ):ℂ) = (((j+1:ℕ):ℝ):ℂ) by norm_num,
    difference_real_part ⟨hy.1.le,hy.2⟩,Real.rpow_natCast,Real.rpow_natCast]
  exact sub_pos.mpr (pow_lt_pow_left₀ (by linarith [hy.1]) (by linarith [hy.2]) (by omega))

end BilleyFahrbachTalmageClassification
