module

public import conjectures.BilleyFahrbachTalmageClassification.BetaExpansion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The change in the prefix factorial at the complex test point -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Finset

private noncomputable def ratio (n : ℕ) : ℝ :=
  ∏ j ∈ range n, (1 + 25/(4*((j:ℝ)+2)^2))

private theorem ratio_succ (n : ℕ) : ratio (n+1) = ratio n * (1+25/(4*((n:ℝ)+2)^2)) :=
  prod_range_succ ..

private theorem ratio_bounded (n : ℕ) : ratio n ≤ 25 := by
  have base : ratio 20 ≤ 25*(1-7/(20+2:ℝ)) := by norm_num [ratio,prod_range_succ]
  have mono : Monotone ratio := by
    apply monotone_nat_of_le_succ
    intro k
    rw [ratio_succ]
    apply le_mul_of_one_le_right
    · unfold ratio
      positivity
    · exact le_add_of_nonneg_right (by positivity)
  by_cases hn : n ≤ 20
  · exact (mono hn).trans (base.trans (by norm_num))
  have tail (k : ℕ) (hk : 20 ≤ k) : ratio k ≤ 25*(1-7/((k:ℝ)+2)) := by
    induction k,hk using Nat.le_induction with
    | base => exact_mod_cast base
    | succ k hk ih =>
      rw [ratio_succ]
      refine (mul_le_mul_of_nonneg_right ih (by positivity)).trans ?_
      push_cast
      have h : (20:ℝ) ≤ k := by exact_mod_cast hk
      have h₀ : 0 < (k:ℝ)+2 := by positivity
      have h₁ : 0 < (k:ℝ)+1+2 := by positivity
      field_simp
      nlinarith [sq_nonneg (k:ℝ), pow_nonneg (Nat.cast_nonneg (α:=ℝ) k) 3]
  refine (tail n (by omega)).trans ?_
  have : 0 ≤ 7/((n:ℝ)+2) := by positivity
  linarith

private theorem ratio_eq (n : ℕ) :
    ‖risingProduct (1+(5/2:ℂ)*Complex.I+1) n‖^2 =
      ratio n * ‖risingProduct 2 n‖^2 := by
  induction n with
  | zero => simp [risingProduct,ratio]
  | succ n ih =>
    simp only [risingProduct, prod_range_succ, norm_mul, mul_pow] at ih ⊢
    rw [ratio_succ, ih]
    have h : ‖(1+(5/2:ℂ)*Complex.I+1)+(n:ℂ)‖^2 = ((n:ℝ)+2)^2 + 25/4 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      norm_num [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
      ring
    have h' : ‖(2:ℂ)+(n:ℂ)‖^2 = ((n:ℝ)+2)^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      norm_num [Complex.add_re,Complex.add_im]
      ring
    rw [h,h']
    have hv : (0:ℝ) < n+2 := by positivity
    field_simp

theorem fourGap_factorial_ratio (n : ℕ) :
    ‖risingProduct (1+(5/2:ℂ)*Complex.I+1) n‖ ≤ 5*‖risingProduct 2 n‖ := by
  have h := mul_le_mul_of_nonneg_right (ratio_bounded n) (sq_nonneg ‖risingProduct 2 n‖)
  rw [←ratio_eq] at h
  nlinarith only [h, norm_nonneg (risingProduct 2 n), norm_nonneg (risingProduct (1+(5/2:ℂ)*Complex.I+1) n)]

end BilleyFahrbachTalmageClassification
