module

public import conjectures.PermutationPeaks.PeakCoefficients
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # A beta-integral expansion of a peak polynomial -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials ReflectedNewton

/-- The product of `n` consecutive increasing factors, starting at `z`. -/
noncomputable def risingProduct (z : ℂ) (n : ℕ) : ℂ := ∏ j ∈ range n, (z+j)

private theorem product_smeval (z : ℂ) (n : ℕ) :
    (ascPochhammer ℕ n).smeval z = risingProduct z n := by
  induction n with
  | zero => simp [risingProduct]
  | succ n ih =>
    rw [ascPochhammer_succ_right, Polynomial.smeval_mul, ih]
    have hc : ((n : ℕ[X]).smeval z) = (n : ℂ) := by
      rw [← Polynomial.C_eq_natCast, Polynomial.smeval_C]
      simp
    simp [risingProduct, Finset.prod_range_succ, hc]

theorem risingProduct_eq (z : ℂ) (n : ℕ) :
    risingProduct z n = n.factorial * Ring.multichoose z n := by
  simpa [nsmul_eq_mul, product_smeval] using (Ring.factorial_nsmul_multichoose_eq_ascPochhammer z n).symm

theorem risingProduct_add (z : ℂ) (j k : ℕ) :
    risingProduct z (j+k) = risingProduct z j * risingProduct (z+j) k := by
  simp only [risingProduct, Finset.prod_range_add, Nat.cast_add, add_assoc]

theorem risingProduct_ne_zero {z : ℂ} (hz : 0 < z.re) (n : ℕ) : risingProduct z n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj h
  have := congrArg Complex.re h
  simp at this
  linarith [Nat.cast_nonneg (α := ℝ) j]

theorem multichoose_beta (z : ℂ) (hz : 0 < z.re) (j k : ℕ) :
    Ring.multichoose z j = risingProduct z (j+(k+1)) *
      Complex.betaIntegral (z+j) (k+1) / (j.factorial * k.factorial) := by
  have hj : 0 < (z+j).re := by simpa using add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg j)
  rw [Complex.betaIntegral_eval_nat_add_one_right hj, risingProduct_add]
  change _ = risingProduct z j * risingProduct (z+j) (k+1) *
    ((k.factorial : ℂ) / risingProduct (z+j) (k+1)) / _
  rw [risingProduct_eq z j]
  have hjf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [risingProduct_ne_zero hj, hjf, hkf]

/-- The polynomial Bernstein density. Its endpoints are zero and its coefficients are concave. -/
noncomputable def momentWeight (S : Finset ℕ) : ℝ[X] :=
  ∑ k ∈ range (maxPeak S-1),
    C (peakCoefficient S k / (maxPeak S).factorial) * bernsteinPolynomial ℝ (maxPeak S) (k+1)

theorem peakNewtonPolynomial (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    peakPolynomial S = ∑ k ∈ range (maxPeak S-1), C (peakCoefficient S k) *
      (risingPolynomial (k+1)).comp (X - C (maxPeak S : ℝ)) := by
  apply Polynomial.funext
  intro x
  simpa [Polynomial.eval_finsetSum, Polynomial.eval_comp] using peakCoefficient_expansion S hS hne x

theorem peakComplexExpansion (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) (z : ℂ) :
    aeval ((maxPeak S : ℂ)+z) (peakPolynomial S) = ∑ k ∈ range (maxPeak S-1),
      (peakCoefficient S k : ℂ) * Ring.multichoose z (k+1) := by
  rw [peakNewtonPolynomial S hS hne]
  simp only [map_sum, map_mul, aeval_C, aeval_comp, map_sub, aeval_X, risingPolynomial]
  simp [Ring.map_multichoose]

private theorem bernstein_beta_integrand (m j : ℕ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (((bernsteinPolynomial ℝ m j).eval t : ℝ) : ℂ) * (t:ℂ)^(z-1) =
      m.choose j * ((t:ℂ)^((z+j)-1) * (1-(t:ℂ))^(((m-j:ℕ):ℂ)+1-1)) := by
  have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [show z+j-1 = z-1+j by ring, Complex.cpow_add _ _ ht', add_sub_cancel_right]
  simp [bernsteinPolynomial, Complex.cpow_natCast]
  ring

theorem bernstein_beta_integral (m j : ℕ) (z : ℂ) :
    (∫ t : ℝ in 0..1, (((bernsteinPolynomial ℝ m j).eval t : ℝ) : ℂ) * (t:ℂ)^(z-1)) =
      m.choose j * Complex.betaIntegral (z+j) ((m-j:ℕ)+1) := by
  rw [Complex.betaIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  exact bernstein_beta_integrand _ _ _ ht.1

theorem bernstein_beta_value (m j : ℕ) (hj : j ≤ m) (z : ℂ) (hz : 0 < z.re) :
    Ring.multichoose z j = risingProduct z (m+1) / m.factorial *
      (∫ t : ℝ in 0..1, (((bernsteinPolynomial ℝ m j).eval t : ℝ) : ℂ) * (t:ℂ)^(z-1)) := by
  have hf : ((m.choose j : ℂ) * (j.factorial : ℂ) * ((m-j).factorial : ℂ)) = (m.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hjf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hkf : ((m-j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m-j)
  have hmf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  rw [multichoose_beta z hz j (m-j), show j+(m-j+1)=m+1 by omega, bernstein_beta_integral]
  field_simp [hmf, hjf, hkf]
  linear_combination (risingProduct z (m+1) * Complex.betaIntegral (z+j) ((m-j:ℕ)+1)) * (-hf)

/-- The Mellin transform of the density reconstructs the value of the source polynomial. -/
theorem peak_mellin (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) (z : ℂ) (hz : 0 < z.re) :
    aeval ((maxPeak S : ℂ)+z) (peakPolynomial S) = risingProduct z (maxPeak S+1) *
      ∫ t : ℝ in 0..1, (((momentWeight S).eval t : ℝ) : ℂ) * (t:ℂ)^(z-1) := by
  let m := maxPeak S
  let b (k : ℕ) (t : ℝ) : ℂ := (((bernsteinPolynomial ℝ m (k+1)).eval t : ℝ) : ℂ) * (t:ℂ)^(z-1)
  have hi : IntervalIntegrable (fun t : ℝ => (t:ℂ)^(z-1)) MeasureTheory.volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_cpow'
    simpa using sub_lt_sub_right hz 1
  have hb (k : ℕ) : IntervalIntegrable (b k) MeasureTheory.volume 0 1 := by
    apply hi.continuousOn_mul
    fun_prop
  have he (t : ℝ) : (((momentWeight S).eval t : ℝ) : ℂ) * (t:ℂ)^(z-1) =
      ∑ k ∈ range (m-1), ((peakCoefficient S k : ℂ) / m.factorial) * b k t := by
    simp [momentWeight, Polynomial.eval_finsetSum, b, m, Finset.sum_mul, mul_assoc]
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (hb k).const_mul _), mul_sum, peakComplexExpansion S hS hne]
  apply sum_congr rfl
  intro k hk
  have hj : k+1 ≤ m := by have := mem_range.mp hk; dsimp [m]; omega
  rw [intervalIntegral.integral_const_mul, bernstein_beta_value m (k+1) hj z hz]
  dsimp [b, m]
  ring

end BilleyFahrbachTalmageClassification
