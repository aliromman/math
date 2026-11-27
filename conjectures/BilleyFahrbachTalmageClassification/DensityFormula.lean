module

public import conjectures.BilleyFahrbachTalmageClassification.BernsteinDensity
public import conjectures.BilleyFahrbachTalmageClassification.Kernel
public import conjectures.PermutationPeaks.Values
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The integral formula for complex arguments -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials MeasureTheory

theorem prefix_parts (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {z : ℂ} (hz : 0 < z.re) :
    z * (∫ t : ℝ in 0..1, (((momentWeight S).eval t : ℝ) : ℂ) * (t:ℂ)^(z-1)) =
      -(∫ t : ℝ in 0..1, (((momentWeight S).derivative.eval t : ℝ) : ℂ) * (t:ℂ)^z) := by
  let w (t : ℝ) : ℂ := ((momentWeight S).eval t : ℝ)
  let dw (t : ℝ) : ℂ := ((momentWeight S).derivative.eval t : ℝ)
  have hc : Continuous (fun t : ℝ => (t:ℂ)^z) := Complex.continuous_ofReal_cpow_const hz
  have hi : IntervalIntegrable (fun t : ℝ => (t:ℂ)^(z-1)) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_cpow'
    simpa using sub_lt_sub_right hz 1
  have hprev := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := w) (u' := dw) (v := fun t : ℝ => (t:ℂ)^z) (v' := fun t : ℝ => z * (t:ℂ)^(z-1))
    (a:=0) (b:=1) (by dsimp [w]; fun_prop) hc.continuousOn
    (fun t _ => ((momentWeight S).hasDerivAt t).ofReal_comp)
    (fun t ht => hasDerivAt_ofReal_cpow_const (by simp at ht; exact ht.1.ne')
      (by rintro rfl; simp at hz))
    (by apply Continuous.intervalIntegrable; dsimp [dw]; fun_prop) (hi.const_mul _)
  have hw1 := (momentWeight_endpoints S hS hne).2
  have hw0 := (momentWeight_endpoints S hS hne).1
  dsimp [w, dw] at hprev
  simp only [hw1, hw0, Complex.ofReal_zero, zero_mul, sub_zero, zero_sub] at hprev
  simpa only [mul_left_comm _ z, intervalIntegral.integral_const_mul] using hprev

private theorem foldHalves (F : ℝ → ℂ) (hF : Continuous F) :
    ∫ y : ℝ in 0..1, (F ((1+y)/2)+F ((1-y)/2)) =
      2*(∫ t : ℝ in 0..1, F t) := by
  let u (y : ℝ) := (1+y)/2
  let v (y : ℝ) := (1-y)/2
  have hcu : Continuous u := by dsimp [u]; fun_prop
  have hcv : Continuous v := by dsimp [v]; fun_prop
  change (∫ y : ℝ in 0..1, (F (u y)+F (v y))) = _
  rw [intervalIntegral.integral_add (f := fun y => F (u y)) (g := fun y => F (v y))
    ((hF.comp hcu).intervalIntegrable ..) ((hF.comp hcv).intervalIntegrable ..)]
  have hu : u = fun y => 1/2*y+1/2 := by funext; dsimp [u]; ring
  have hv : v = fun y => -(1/2)*y+1/2 := by funext; dsimp [v]; ring
  rw [hu, hv, intervalIntegral.integral_comp_mul_add F (by norm_num : (1/2:ℝ)≠0),
    intervalIntegral.integral_comp_mul_add F (by norm_num : -(1/2:ℝ)≠0)]
  norm_num [Complex.real_smul]
  rw [intervalIntegral.integral_symm (a:=0) (b:=1/2),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (a:=0) (b:=1/2)) (hF.intervalIntegrable (a:=1/2) (b:=1))]
  ring

theorem density_mellin (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {z : ℂ} (hz : 0 < z.re) :
    (∫ y : ℝ in 0..1, (prefixDensity S y : ℂ) * difference z y) =
      z*(∫ t : ℝ in 0..1, (((momentWeight S).eval t : ℝ) : ℂ) * (t:ℂ)^(z-1)) := by
  let F (t : ℝ) : ℂ := ((momentWeight S).derivative.eval t : ℝ) * (t:ℂ)^z
  have hF : Continuous F := by
    apply Continuous.mul _ (Complex.continuous_ofReal_cpow_const hz)
    fun_prop
  have hp (y : ℝ) : (prefixDensity S y:ℂ)*difference z y =
      -(1/2 : ℂ)*(F ((1+y)/2)+F ((1-y)/2)) := by
    have h := momentWeight_derivative_flip S hS hne ((1-y)/2)
    rw [show (1-(1-y)/2:ℝ)=(1+y)/2 by ring] at h
    simp [prefixDensity, difference, F, h]
    ring
  simp_rw [hp, intervalIntegral.integral_const_mul, foldHalves F hF]
  rw [prefix_parts S hS hne hz]
  dsimp [F]
  ring

/-- The normalized peak polynomial is the integral of a difference of two powers. -/
theorem density_formula (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {z : ℂ} (hz : 0 < z.re) :
    peakValue S ((maxPeak S:ℂ)+z) = risingProduct (z+1) (maxPeak S) *
      ∫ y : ℝ in 0..1, (prefixDensity S y : ℂ) * difference z y := by
  rw [peakValue, peak_mellin S hS hne z hz, density_mellin S hS hne hz]
  rw [show maxPeak S+1=1+maxPeak S by omega, risingProduct_add]
  simp [risingProduct]
  ring

end BilleyFahrbachTalmageClassification
