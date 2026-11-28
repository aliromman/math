module

public import conjectures.BilleyFahrbachTalmageClassification.SmallModel
public import conjectures.BilleyFahrbachTalmageClassification.IntegralFactorization
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The integral and nonreal roots of the four base polynomials -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials

theorem intFactors_good (xs : List ℤ) :
    (intFactors xs).Splits ∧ IntegralRoots (intFactors xs) ∧ intFactors xs ≠ 0 := by
  induction xs with
  | nil =>
    simpa [intFactors] using And.intro (Splits.one : (1:ℝ[X]).Splits)
      (And.intro (integralRoots_const (one_ne_zero : (1:ℝ)≠0)) (one_ne_zero : (1:ℝ[X])≠0))
  | cons j xs ih =>
    change ((X-C (j:ℝ))*intFactors xs).Splits ∧ IntegralRoots ((X-C (j:ℝ))*intFactors xs) ∧
      (X-C (j:ℝ))*intFactors xs ≠ 0
    exact ⟨(Splits.X_sub_C _).mul ih.1, integralRoots_mul (integralRoots_linear j) ih.2.1,
      mul_ne_zero (X_sub_C_ne_zero _) ih.2.2⟩

theorem baseModel_good (r : ℕ) (hr : r≤1) : (baseModel r).Splits ∧ IntegralRoots (baseModel r) := by
  interval_cases r
  · exact ⟨(intFactors_good _).1,(intFactors_good _).2.1⟩
  · exact ⟨(Splits.C _).mul (intFactors_good _).1,
      integralRoots_mul (integralRoots_const (by norm_num)) (intFactors_good _).2.1⟩

private theorem quadratic_bad : ¬(X^2+2*X+5 : ℝ[X]).Splits := by
  intro hs
  let z : ℂ := ⟨-1,1⟩
  have h := norm_eval_le_aeval _ hs z
  have hh := mul_self_le_mul_self (abs_nonneg _) h
  rw [← sq, ← sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hh
  norm_num [z, pow_succ, map_ofNat, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] at hh

private theorem cubic_bad : ¬(17*X^3-17*X^2+87*X+105 : ℝ[X]).Splits := by
  intro hs
  let z : ℂ := ⟨1,2⟩
  have h := norm_eval_le_aeval _ hs z
  have hh := mul_self_le_mul_self (abs_nonneg _) h
  rw [← sq, ← sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hh
  norm_num [z, pow_succ, map_ofNat, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im] at hh

theorem baseModel_bad (r : ℕ) (hr : 2≤r) (hr' : r≤3) : ¬ (baseModel r).Splits := by
  interval_cases r
  · change ¬(C (1/30:ℝ)*intFactors [2,4,6]*_).Splits
    rw [splits_mul_iff_right (mul_ne_zero (by norm_num) (intFactors_good _).2.2)
      ((Splits.C _).mul (intFactors_good _).1)]
    exact quadratic_bad
  · change ¬(C (1/2520:ℝ)*intFactors [2,4,6,8]*_).Splits
    rw [splits_mul_iff_right (mul_ne_zero (by norm_num) (intFactors_good _).2.2)
      ((Splits.C _).mul (intFactors_good _).1)]
    exact cubic_bad

theorem two_factorization (r : ℕ) (hr : r≤3) : peakPolynomial (extend ∅ (2::List.replicate r 2)) = baseModel r := by
  have hg : ∀ j∈(2::List.replicate r 2), 2≤j := by simp
  have h := positive_axis_identity (extend ∅ (2::List.replicate r 2)) 0 (baseModel r) (by
    intro x hx
    have hh : 0 < (x:ℂ).re := hx
    simpa using (extension_empty _ hg hh).trans (two_model r hr hh))
  simpa using h

/-- The integral of the first power difference, with evaluation at one for the empty prefix. -/
noncomputable def prefixMass (A : Finset ℕ) : ℝ :=
  if A.Nonempty then ∫ y : ℝ in 0..1, prefixDensity A y*y else 1

theorem prefixMass_pos (A : Finset ℕ) (hA : Admissible A) : 0 < prefixMass A := by
  by_cases hne : A.Nonempty
  · simpa [prefixMass,hne] using prefix_mass_pos A hA hne
  · simp [prefixMass,hne]

theorem three_factorization (A : Finset ℕ) (hA : Admissible A) (r : ℕ) (hr : r≤3) :
    (peakPolynomial (extend A (3::List.replicate r 2))).comp (X+C (maxPeak A:ℝ)) =
      C (prefixMass A/2)*prefixPoly (maxPeak A)*X*(baseModel r).comp (X-1) := by
  apply positive_axis_identity
  intro x hx
  have hp : 0 < (x:ℂ).re := hx
  have hg : ∀ j∈(3::List.replicate r 2), 2≤j := by simp
  simp only [map_mul, aeval_C, aeval_X, aeval_comp, map_sub, map_one, prefixPoly_aeval]
  by_cases hne : A.Nonempty
  · rw [extension_density A hA hne _ hg hp]
    simp_rw [three_model r hr]
    have hh (y : ℝ) : (prefixDensity A y:ℂ)*((y:ℂ)*((x:ℂ)/2)*aeval ((x:ℂ)-1) (baseModel r)) =
        (((prefixDensity A y*y):ℝ):ℂ) * (((x:ℂ)/2)*aeval ((x:ℂ)-1) (baseModel r)) := by
      push_cast
      ring
    simp_rw [hh, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    simp [prefixMass,hne]
    ring
  · have ha := not_nonempty_iff_eq_empty.mp hne
    subst A
    rw [show maxPeak ∅=0 by simp [maxPeak]]
    simp only [Nat.cast_zero, zero_add, extension_empty _ hg hp, three_model r hr, Complex.ofReal_one,
      one_mul, risingProduct, range_zero, prod_empty, mul_one, prefixMass, Finset.not_nonempty_empty, ite_false]
    push_cast
    ring

theorem three_good (A : Finset ℕ) (hA : Admissible A) (r : ℕ) (hr : r≤1) :
    (peakPolynomial (extend A (3::List.replicate r 2))).Splits ∧
      IntegralRoots (peakPolynomial (extend A (3::List.replicate r 2))) := by
  let S := extend A (3::List.replicate r 2)
  obtain ⟨hs,hi⟩ := baseModel_good r hr
  have h0 : prefixMass A/2 ≠ 0 := (div_pos (prefixMass_pos A hA) (by norm_num)).ne'
  constructor
  · apply (splits_translate_iff _ (maxPeak A)).mp
    rw [three_factorization A hA r (by omega)]
    exact (((Splits.C _).mul (prefixPoly_splits _)).mul Splits.X).mul
      (by simpa using hs.comp_X_sub_C 1)
  · apply integralRoots_of_translate (maxPeak A:ℤ)
    rw [Int.cast_natCast, three_factorization A hA r (by omega)]
    apply integralRoots_mul (integralRoots_mul (integralRoots_mul (integralRoots_const h0)
      (prefixPoly_integral _)) (by simpa using integralRoots_linear 0))
    simpa [sub_eq_add_neg] using integralRoots_translate hi (-1)

theorem three_bad (A : Finset ℕ) (hA : Admissible A) (r : ℕ) (hr : 2≤r) (hr' : r≤3) :
    ¬(peakPolynomial (extend A (3::List.replicate r 2))).Splits := by
  intro h
  have hs := h.comp_X_add_C (maxPeak A:ℝ)
  rw [three_factorization A hA r hr'] at hs
  have hn : C (prefixMass A / 2) * prefixPoly (maxPeak A) * X ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by simpa using (div_pos (prefixMass_pos A hA) (by norm_num : (0:ℝ)<2)).ne')
      (prefixPoly_ne_zero _)) X_ne_zero
  have hmodel := (splits_mul_iff_right hn (((Splits.C _).mul (prefixPoly_splits _)).mul Splits.X)).mp hs
  exact baseModel_bad r hr hr' ((splits_iff_comp_splits_of_natDegree_eq_one
    (show (X-1:ℝ[X]).natDegree=1 by simpa using natDegree_X_sub_C (1:ℝ))).mpr hmodel)

end BilleyFahrbachTalmageClassification
