module

public import conjectures.BilleyFahrbachTalmageClassification.Moments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The strict three-point inequality for a prefix -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials MeasureTheory

theorem cubic_weight_bound (f : ℝ → ℝ) (hc : Continuous f) (hm : MonotoneOn f (Set.Icc 0 1)) :
    (∫ y : ℝ in 0..1, f y*y) / 2 ≤ ∫ y : ℝ in 0..1, f y*y^3 := by
  let d := Real.sqrt (1/2)
  have hd : d^2=(1/2:ℝ) := Real.sq_sqrt (by norm_num)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd1 : d ≤ 1 := by nlinarith
  have his : 0 ≤ ∫ y : ℝ in 0..1, (f y-f d) * (y^3-y/2) := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro y hy
    have hy0 := hy.1
    by_cases h : y≤d
    · have hl := hm hy ⟨hd0,hd1⟩ h
      apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hy0 (show y^2-d^2≤0 by nlinarith)]
    · have hl := hm ⟨hd0,hd1⟩ hy (le_of_not_ge h)
      apply mul_nonneg (by linarith)
      nlinarith [mul_nonneg hy0 (show 0≤y^2-d^2 by nlinarith)]
  have he (y : ℝ) : (f y-f d)*(y^3-y/2) = f y*y^3 - (1/2)*(f y*y) - f d*(y^3) + (f d/2)*y := by ring
  simp_rw [he] at his
  have hi₁ : IntervalIntegrable (fun y : ℝ => f y * y^3) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi₂ : IntervalIntegrable (fun y : ℝ => (1/2)*(f y*y)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi₃ : IntervalIntegrable (fun y : ℝ => f d * y^3) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi₄ : IntervalIntegrable (fun y : ℝ => (f d/2)*y) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add ((hi₁.sub hi₂).sub hi₃) hi₄,
    intervalIntegral.integral_sub (hi₁.sub hi₂) hi₃, intervalIntegral.integral_sub hi₁ hi₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_id] at his
  norm_num at his
  linarith

private theorem nat_density (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty) (n : ℕ) (hn : 0<n) :
    (peakPolynomial A).eval ((maxPeak A:ℝ)+n) = realRising ((n:ℝ)+1) (maxPeak A) *
      ∫ y : ℝ in 0..1, prefixDensity A y * (((1+y)/2)^n-((1-y)/2)^n) := by
  have h := density_formula A hA hne (z:=(n:ℂ)) (by simpa using (show (0:ℝ)<n by exact_mod_cast hn))
  have h1 : (n:ℂ)+1 = (((n:ℝ)+1:ℝ):ℂ) := by simp
  have h2 : (maxPeak A:ℂ)+n = (((maxPeak A:ℝ)+n:ℝ):ℂ) := by simp
  rw [h2, peakValue_real, h1, realRising_cast] at h
  simp only [difference, Complex.cpow_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
    ← Complex.ofReal_mul, intervalIntegral.integral_ofReal] at h
  exact Complex.ofReal_inj.mp h

private theorem prefix_ratio_two (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty) :
    let c : ℝ := maxPeak A
    (peakPolynomial A).eval (c+2)^2 / ((peakPolynomial A).eval (c+1) * (peakPolynomial A).eval (c+3)) < 16/9 := by
  dsimp only
  let f := prefixDensity A
  let L := ∫ y : ℝ in 0..1, f y*y
  let H := ∫ y : ℝ in 0..1, f y*y^3
  let r (x : ℝ) := realRising x (maxPeak A)
  have hc : Continuous f := prefixDensity_continuous A
  have hL : 0 < L := prefix_mass_pos A hA hne
  have hH : L/2 ≤ H := cubic_weight_bound f hc (prefixDensity_mono A hA hne)
  have h3 : 0 < (3*L+H)/4 := by linarith
  have he1 (y : ℝ) : ((1+y)/2)^1-((1-y)/2)^1=y := by ring
  have he2 (y : ℝ) : ((1+y)/2)^2-((1-y)/2)^2=y := by ring
  have he3 (y : ℝ) : f y*(((1+y)/2)^3-((1-y)/2)^3) = (3/4)*(f y*y) + (1/4)*(f y*y^3) := by ring
  have hp1 := nat_density A hA hne 1 (by decide)
  have hp2 := nat_density A hA hne 2 (by decide)
  have hp3 := nat_density A hA hne 3 (by decide)
  simp_rw [he1] at hp1
  simp_rw [he2] at hp2
  change _ = _ * ∫y:ℝ in 0..1, f y * _ at hp3
  simp_rw [he3] at hp3
  have hi1 : IntervalIntegrable (fun y : ℝ => (3/4)*(f y*y)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi2 : IntervalIntegrable (fun y : ℝ => (1/4)*(f y*y^3)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hp3
  norm_num at hp1 hp2 hp3
  rw [hp1, hp2, hp3]
  change (r 3*L)^2/(r 2*L*(r 4 * (3/4*L+1/4*H))) < 16/9
  have hR : r 3^2/(r 2*r 4)<3/2 := by
    convert realRising_ratio (x:=2) (by norm_num) (maxPeak A) using 1 <;> norm_num [r]
  have h0 : 0<r 2 := realRising_pos (by norm_num) _
  have h4 : 0<r 4 := realRising_pos (by norm_num) _
  have hfrac : L^2/(L*((3*L+H)/4)) ≤ 8/7 := by
    apply (div_le_iff₀ (mul_pos hL h3)).mpr
    nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hH)]
  calc
    _ = (r 3^2/(r 2*r 4))*(L^2/(L*((3*L+H)/4))) := by
      rw [show (3/4*L+1/4*H)=(3*L+H)/4 by ring]
      field_simp [h0.ne', h4.ne', hL.ne', show (3*L+H)≠0 by linarith]
    _ ≤ (r 3^2/(r 2*r 4))*(8/7) := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ < (3/2)*(8/7) := mul_lt_mul_of_pos_right hR (by norm_num)
    _ < 16/9 := by norm_num

theorem prefix_ratio (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty) (s : ℕ) (hs : 2 ≤ s) :
    let c : ℝ := maxPeak A
    let x : ℝ := s
    (peakPolynomial A).eval (c+x)^2 / ((peakPolynomial A).eval (c+(x-1)) *
      (peakPolynomial A).eval (c+(x+1))) < (4/3)*x^2/(x^2-1) := by
  by_cases h : s=2
  · subst s
    norm_num
    exact prefix_ratio_two A hA hne
  · obtain ⟨n,rfl⟩ : ∃ n, s=n+3 := ⟨s-3,by omega⟩
    simpa using prefix_ratio_large A hA hne n

end BilleyFahrbachTalmageClassification
