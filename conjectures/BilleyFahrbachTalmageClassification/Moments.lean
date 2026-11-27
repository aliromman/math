module

public import conjectures.BilleyFahrbachTalmageClassification.ExtensionDensity
public import conjectures.BilleyFahrbachTalmageClassification.PositiveValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Log-convexity of the prefix moments -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials MeasureTheory

noncomputable def prefixMoment (A : Finset ℕ) (n : ℕ) : ℝ :=
  ∫ t : ℝ in 0..1, (momentWeight A).eval t * t^n

theorem momentWeight_nonneg (A : Finset ℕ) (hA : Admissible A) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    0 ≤ (momentWeight A).eval t := by
  simp only [momentWeight, eval_finsetSum, eval_mul, eval_C]
  apply sum_nonneg
  intro k hk
  exact mul_nonneg (div_nonneg (peakCoefficient_nonnegative A hA k) (Nat.cast_nonneg _))
    (bernstein_nonneg _ _ ht)

theorem moment_value (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty) (n : ℕ) :
    (peakPolynomial A).eval ((maxPeak A:ℝ)+(n+1)) =
      realRising (n+1) (maxPeak A+1) * prefixMoment A n := by
  have h := peak_mellin A hA hne ((n:ℂ)+1) (by simp; positivity)
  have h1 : ((n:ℂ)+1) = ((((n:ℝ)+1):ℝ):ℂ) := by simp
  have h2 : (maxPeak A:ℂ)+((n:ℂ)+1) = (((maxPeak A:ℝ)+((n:ℝ)+1):ℝ):ℂ) := by simp
  change peakValue A _ = _ at h
  rw [h2, peakValue_real] at h
  simp_rw [add_sub_cancel_right, Complex.cpow_natCast, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul] at h
  rw [h1, realRising_cast, intervalIntegral.integral_ofReal, ← Complex.ofReal_mul] at h
  exact Complex.ofReal_inj.mp h

theorem prefixMoment_pos (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty) (n : ℕ) :
    0 < prefixMoment A n := by
  have h := peak_after_pos A hA (n:=maxPeak A+(n+1)) (by omega)
  push_cast at h
  rw [moment_value A hA hne n] at h
  exact pos_of_mul_pos_right h (realRising_pos (by positivity) _).le

theorem prefixMoment_logConvex (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty) (n : ℕ) :
    (prefixMoment A (n+1))^2 ≤ prefixMoment A n * prefixMoment A (n+2) := by
  let m := prefixMoment A n
  let b := prefixMoment A (n+1)
  let g (j : ℕ) (t : ℝ) := (momentWeight A).eval t * t^j
  have hc (j : ℕ) : Continuous (g j) := by dsimp [g]; fun_prop
  have hi : 0 ≤ ∫ t : ℝ in 0..1, g n t * (m*t-b)^2 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t ht
    exact mul_nonneg (mul_nonneg (momentWeight_nonneg A hA ht) (pow_nonneg ht.1 _)) (sq_nonneg _)
  have he (t : ℝ) : g n t * (m*t-b)^2 =
      m^2*g (n+2) t - (2*m*b)*g (n+1) t + b^2*g n t := by
    dsimp [g]
    rw [pow_add, pow_succ]
    ring
  simp_rw [he] at hi
  have hi₀ := ((hc (n+2)).const_mul (m^2)).intervalIntegrable (a:=0) (b:=1) (μ:=volume)
  have hi₁ := ((hc (n+1)).const_mul (2*m*b)).intervalIntegrable (a:=0) (b:=1) (μ:=volume)
  have hi₂ := ((hc n).const_mul (b^2)).intervalIntegrable (a:=0) (b:=1) (μ:=volume)
  rw [intervalIntegral.integral_add (hi₀.sub hi₁) hi₂, intervalIntegral.integral_sub hi₀ hi₁,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  change 0 ≤ m^2 * prefixMoment A (n+2) - (2*m*b)*b + b^2*m at hi
  have h' : 0 ≤ m*(m*prefixMoment A (n+2)-b^2) := by linarith
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h' (prefixMoment_pos A hA hne n))

theorem realRising_shift (x : ℝ) (k : ℕ) :
    realRising (x+1) k * x = realRising x k * (x+k) := by
  have h := Finset.prod_range_succ' (fun j : ℕ => x+j) k
  rw [prod_range_succ] at h
  have hh (j : ℕ) : x+1+(j:ℝ)=x+(j+1:ℕ) := by push_cast; ring
  simp only [realRising, hh]
  simpa only [Nat.cast_zero, add_zero] using h.symm

theorem realRising_ratio {x : ℝ} (hx : 0 < x) (k : ℕ) :
    realRising (x+1) k ^ 2 / (realRising x k * realRising (x+2) k) < (x+1)/x := by
  have h1 := realRising_shift x k
  have h2 := realRising_shift (x+1) k
  rw [show x+1+1=x+2 by ring] at h2
  have hx1 : 0<x+1 := by linarith
  have hx2 : 0<x+2 := by linarith
  have h0 := realRising_pos hx k
  have hr := realRising_pos hx1 k
  have ht := realRising_pos hx2 k
  suffices hm : (realRising (x+1) k / realRising x k) <
      (x+1)/x * (realRising (x+2) k / realRising (x+1) k) by
    apply (div_lt_div_iff₀ (mul_pos h0 ht) hx).mpr
    have h := (div_lt_iff₀ h0).mp hm
    field_simp [ne_of_gt hx, ne_of_gt hr] at h
    nlinarith
  have he0 : realRising (x+1) k / realRising x k = (x+k)/x :=
    (div_eq_div_iff h0.ne' hx.ne').mpr (by linarith)
  have he1 : realRising (x+2) k / realRising (x+1) k = (x+1+k)/(x+1) :=
    (div_eq_div_iff hr.ne' hx1.ne').mpr (by linarith)
  rw [he0,he1]
  rw [div_mul_div_comm, div_lt_div_iff₀ hx (mul_pos hx hx1)]
  nlinarith [mul_pos hx hx1]

theorem prefix_ratio_large (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty) (n : ℕ) :
    let c : ℝ := maxPeak A
    let s : ℝ := n+3
    (peakPolynomial A).eval (c+s)^2 / ((peakPolynomial A).eval (c+(s-1)) *
      (peakPolynomial A).eval (c+(s+1))) < (4/3) * s^2 / (s^2-1) := by
  dsimp only
  let x : ℝ := n+2
  let k := maxPeak A+1
  have hx : 0 < x := by dsimp [x]; positivity
  have htwo : 2 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  let m (j : ℕ) := prefixMoment A j
  let r (v : ℝ) := realRising v k
  have hR := realRising_ratio hx k
  change r (x+1)^2 / (r x*r (x+2)) < (x+1)/x at hR
  have hlog := prefixMoment_logConvex A hA hne (n+1)
  have hm0 := prefixMoment_pos A hA hne (n+1)
  have hm2 := prefixMoment_pos A hA hne (n+3)
  have hfrac : m (n+2)^2/(m (n+1)*m (n+3)) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos hm0 hm2)).mpr
    simpa [m] using hlog
  have hp (j : ℕ) := moment_value A hA hne j
  have hp0 := hp (n+1)
  have hp1 := hp (n+2)
  have hp2 := hp (n+3)
  push_cast at hp0 hp1 hp2
  have he0 : (((n:ℝ)+3)-1) = (n+1:ℝ)+1 := by ring
  have he1 : ((n:ℝ)+3) = ((n:ℝ)+2)+1 := by ring
  rw [he0, hp0, hp2, he1, hp1]
  rw [show (n:ℝ)+1+1=(n:ℝ)+2 by ring, show (n:ℝ)+2+1+1=(n:ℝ)+2+2 by ring]
  change ((r (x+1) * m (n+2))^2 /
      ((r x * m (n+1))*(r (x+2) * m (n+3)))) < (4/3)*(x+1)^2/((x+1)^2-1)
  have hr0 : 0<r x := realRising_pos hx k
  have hr2 : 0<r (x+2) := realRising_pos (by linarith) k
  calc
    _ = (r (x+1)^2/(r x*r (x+2)))*(m (n+2)^2/(m (n+1)*m (n+3))) := by ring
    _ ≤ (r (x+1)^2/(r x*r (x+2)))*1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ < (x+1)/x := by simpa using hR
    _ ≤ _ := by
      apply (div_le_div_iff₀ hx (by nlinarith : 0<(x+1)^2-1)).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ x-2) (mul_nonneg hx.le (by linarith : 0 ≤ x+1))]

end BilleyFahrbachTalmageClassification
