module

public import conjectures.BilleyFahrbachTalmageClassification.BetaExpansion
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The symmetric concave weight and its increasing density -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials ReflectedNewton Set

noncomputable def bernsteinSum (n : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ range (n+1), C (a j) * bernsteinPolynomial ℝ n j

theorem derivative_bernsteinSum (n : ℕ) (a : ℕ → ℝ) :
    (bernsteinSum (n+1) a).derivative = C ((n:ℝ)+1) *
      bernsteinSum n (fun j => a (j+1) - a j) := by
  let b := bernsteinPolynomial ℝ n
  have hlast : b (n+1) = 0 := bernsteinPolynomial.eq_zero_of_lt ℝ (by omega)
  have hshift : ∑ j ∈ range (n+1), C (a (j+1))*b (j+1) =
      ∑ j ∈ range (n+1), C (a j)*b j - C (a 0)*b 0 := by
    have h := Finset.sum_range_succ' (fun j => C (a j)*b j) (n+1)
    rw [Finset.sum_range_succ _ (n+1), hlast, mul_zero, add_zero] at h
    linear_combination -h
  simp only [bernsteinSum, derivative_sum, derivative_C_mul]
  rw [Finset.sum_range_succ' _ (n+1)]
  simp only [bernsteinPolynomial.derivative_succ_aux, bernsteinPolynomial.derivative_zero,
    Nat.add_one_sub_one, Nat.cast_add, Nat.cast_one, map_add, map_one, map_natCast, map_sub,
    sub_mul, mul_sub, Finset.sum_sub_distrib]
  change (∑ j ∈ range (n+1), C (a (j+1)) * (((n:ℝ[X])+1)*b j) -
      ∑ j ∈ range (n+1), C (a (j+1)) * (((n:ℝ[X])+1)*b (j+1))) +
      C (a 0)*(-((n:ℝ[X])+1)*b 0) = _
  simp_rw [mul_left_comm (C _) ((n:ℝ[X])+1), ← Finset.mul_sum]
  rw [hshift]
  ring

theorem bernsteinSum_flip (n : ℕ) (a : ℕ → ℝ) (h : ∀ j ≤ n, a (n-j) = a j) :
    (bernsteinSum n a).comp (1-X) = bernsteinSum n a := by
  simp only [bernsteinSum, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp]
  calc
    _ = ∑ j ∈ range (n+1), C (a (n-j))*bernsteinPolynomial ℝ n (n-j) := by
      apply sum_congr rfl
      intro j hj
      have hj' : j ≤ n := by simpa using mem_range.mp hj
      rw [bernsteinPolynomial.flip ℝ n j hj', h j hj']
    _ = _ := by simpa using sum_range_reflect (fun j => C (a j)*bernsteinPolynomial ℝ n j) (n+1)

noncomputable def normalizedCoefficient (S : Finset ℕ) (j : ℕ) : ℝ :=
  peakPaddedCoefficient S ((j:ℤ)-1) / (maxPeak S).factorial

theorem momentWeight_eq (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    momentWeight S = bernsteinSum (maxPeak S) (normalizedCoefficient S) := by
  let m := maxPeak S
  have hm : 2 ≤ m := (last_peak_reduction hS hne).1
  have h0 : normalizedCoefficient S 0 = 0 := by
    simp [normalizedCoefficient, peakPaddedCoefficient]
  have hlast : normalizedCoefficient S m = 0 := by
    simp [normalizedCoefficient, peakPaddedCoefficient, m, show ¬ (maxPeak S:ℤ)-1 ≤ (maxPeak S:ℤ)-2 by omega]
  have hmain (j : ℕ) (hj : j < m-1) :
      normalizedCoefficient S (j+1) = peakCoefficient S j / m.factorial := by
    have hj' : (j:ℤ) ≤ (m:ℤ)-2 := by omega
    simp [normalizedCoefficient, peakPaddedCoefficient, m, show (j:ℤ) ≤ (maxPeak S:ℤ)-2 from hj']
  change _ = ∑ j ∈ range (m+1), C (normalizedCoefficient S j) * bernsteinPolynomial ℝ m j
  rw [sum_range_succ, hlast, map_zero, zero_mul, add_zero]
  rw [show m = (m-1)+1 by omega] at ⊢
  rw [sum_range_succ', h0, map_zero, zero_mul, add_zero]
  dsimp [momentWeight]
  apply sum_congr rfl
  intro j hj
  rw [hmain j (mem_range.mp hj), show m-1+1=m by omega]

theorem bernstein_nonneg (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    0 ≤ (bernsteinPolynomial ℝ n j).eval t := by
  simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X, eval_sub, eval_one]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
    (pow_nonneg (sub_nonneg.mpr ht.2) _)

theorem momentWeight_flip (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    (momentWeight S).comp (1-X) = momentWeight S := by
  rw [momentWeight_eq S hS hne]
  apply bernsteinSum_flip
  intro j hj
  have h := (peakCoefficient_symmetric_concave S hS hne).reflected ((j:ℤ)-1) (by omega) (by omega)
  have he : (((maxPeak S-j:ℕ):ℤ)-1) = (maxPeak S:ℤ)-2-((j:ℤ)-1) := by omega
  simp only [normalizedCoefficient, he, h]

theorem momentWeight_second_nonpos (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ((momentWeight S).derivative.derivative).eval t ≤ 0 := by
  let n := maxPeak S-2
  have hm := (last_peak_reduction hS hne).1
  have he : maxPeak S = n+1+1 := by dsimp [n]; omega
  rw [momentWeight_eq S hS hne, he, derivative_bernsteinSum, derivative_C_mul,
    derivative_bernsteinSum]
  simp only [eval_mul, eval_C, bernsteinSum, eval_finsetSum]
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_)
  apply sum_nonpos
  intro j hj
  apply mul_nonpos_of_nonpos_of_nonneg _ (bernstein_nonneg _ _ ht)
  have hj' := mem_range.mp hj
  have h := (peakCoefficient_symmetric_concave S hS hne).concave (j:ℤ) (by omega) (by omega)
  simp only [normalizedCoefficient, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have hf : 0 ≤ ((maxPeak S).factorial : ℝ) := by positivity
  rw [← sub_div, ← sub_div, ← sub_div]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hf

theorem momentWeight_derivative_flip (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) (t : ℝ) :
    (momentWeight S).derivative.eval (1-t) = -(momentWeight S).derivative.eval t := by
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval t) (momentWeight_flip S hS hne)
  simp only [derivative_comp, derivative_sub, derivative_one, derivative_X, zero_sub, eval_mul,
    eval_comp, eval_sub, eval_one, eval_X, eval_neg] at h
  linarith

theorem momentWeight_derivative_antitone (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    AntitoneOn (momentWeight S).derivative.eval (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (by fun_prop)
  · exact (momentWeight S).derivative.differentiable.differentiableOn
  · intro t ht
    rw [Polynomial.deriv]
    exact momentWeight_second_nonpos S hS hne (interior_subset ht)

/-- The slope of the symmetric moment weight on the left half of the interval. -/
noncomputable def prefixDensity (S : Finset ℕ) (y : ℝ) : ℝ :=
  (momentWeight S).derivative.eval ((1-y)/2) / 2

theorem prefixDensity_continuous (S : Finset ℕ) : Continuous (prefixDensity S) := by
  unfold prefixDensity
  fun_prop

theorem prefixDensity_mono (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    MonotoneOn (prefixDensity S) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact momentWeight_derivative_antitone S hS hne
    ⟨by linarith [hy.2], by linarith [hy.1]⟩ ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)

theorem prefixDensity_nonneg (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {y : ℝ} (hy : y ∈ Set.Icc 0 1) : 0 ≤ prefixDensity S y := by
  have h := momentWeight_derivative_flip S hS hne (1/2)
  norm_num at h
  have hzero : prefixDensity S 0 = 0 := by simp [prefixDensity]; linarith
  rw [← hzero]
  exact prefixDensity_mono S hS hne (by norm_num) hy hy.1

theorem momentWeight_endpoints (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    (momentWeight S).eval 0 = 0 ∧ (momentWeight S).eval 1 = 0 := by
  have h0 : (momentWeight S).eval 0 = 0 := by
    simp [momentWeight, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_0]
  have h := congrArg (fun p : ℝ[X] => p.eval 0) (momentWeight_flip S hS hne)
  exact ⟨h0, by simpa [eval_comp, h0] using h⟩

end BilleyFahrbachTalmageClassification
