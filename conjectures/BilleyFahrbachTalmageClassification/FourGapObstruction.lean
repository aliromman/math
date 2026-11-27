module

public import conjectures.BilleyFahrbachTalmageClassification.FourTwo
public import conjectures.BilleyFahrbachTalmageClassification.ExtensionDensity
public import conjectures.BilleyFahrbachTalmageClassification.PeakRoots
public import conjectures.BilleyFahrbachTalmageClassification.FourGapRoots
public import conjectures.BilleyFahrbachTalmageClassification.FourGapRatio
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Four successive gaps of length two exclude real-rootedness -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials MeasureTheory

private noncomputable abbrev z : ℂ := 1 + (5/2:ℂ)*Complex.I

private theorem kernel_continuous : Continuous (gapKernel [2,2,2,2] z) := by
  have he : z = peakTestPoint := by
    apply Complex.ext <;> norm_num [z, peakTestPoint, Complex.mul_re, Complex.mul_im]
  rw [he]
  simp_rw [show gapKernel [2,2,2,2] peakTestPoint = fun y => 16*difference peakTestPoint y + (y:ℂ)*fourCorrections (y^2) from funext fourTwo_formula]
  exact (continuous_const.mul (difference_continuous (by norm_num [peakTestPoint]))).add
    (Complex.continuous_ofReal.mul (by simp only [fourCorrections,Complex.mk_eq_add_mul_I]; fun_prop))

private theorem weighted_bound (f : ℝ → ℝ) (hc : Continuous f) (hm : MonotoneOn f (Set.Icc 0 1))
    (hn : ∀ y ∈ Set.Icc 0 1, 0 ≤ f y) :
    ‖∫ y : ℝ in 0..1, (f y : ℂ)*gapKernel [2,2,2,2] z y‖ ≤ (33/2)*∫ y : ℝ in 0..1, f y*y := by
  let m : ℝ := 1/2
  let G (y : ℝ) := f y*y
  let H (y : ℝ) := (f y:ℂ)*gapKernel [2,2,2,2] z y
  have gc : Continuous G := hc.mul continuous_id
  have hc' : Continuous H := (Complex.continuous_ofReal.comp hc).mul kernel_continuous
  have hm0 : (0:ℝ) ≤ m := by norm_num [m]
  have hm1 : m ≤ 1 := by norm_num [m]
  have hc₀ : Continuous (fun y : ℝ => f m*y) := continuous_const.mul continuous_id
  have lo := intervalIntegral.integral_mono_on (μ:=volume) hm0 (gc.intervalIntegrable ..)
      (hc₀.intervalIntegrable ..) (fun y hy => mul_le_mul_of_nonneg_right
        (hm ⟨hy.1,hy.2.trans hm1⟩ ⟨hm0,hm1⟩ hy.2) hy.1)
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hm1 (hc₀.intervalIntegrable ..)
      (gc.intervalIntegrable ..) (fun y hy => mul_le_mul_of_nonneg_right
        (hm ⟨hm0,hm1⟩ ⟨hm0.trans hy.1,hy.2⟩ hy.1) (hm0.trans hy.1))
  change (∫ y : ℝ in 0..m, G y) ≤ ∫ y : ℝ in 0..m, f m*y at lo
  change (∫ y : ℝ in m..1, f m*y) ≤ ∫ y : ℝ in m..1, G y at hi
  rw [intervalIntegral.integral_const_mul, integral_id] at lo hi
  norm_num [m] at lo hi
  have part {a b K : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
      (hK : ∀ y ∈ Set.Icc a b, ‖gapKernel [2,2,2,2] z y‖ ≤ K*y) :
      ‖∫ y : ℝ in a..b, H y‖ ≤ K*(∫ y : ℝ in a..b, G y) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ ((continuous_const.mul gc).intervalIntegrable ..)
    apply Filter.Eventually.of_forall
    intro y hy
    have hy' := hn y ⟨ha.trans hy.1.le, hy.2.trans hb⟩
    have := mul_le_mul_of_nonneg_left (hK y ⟨hy.1.le,hy.2⟩) hy'
    simpa [H, G, norm_mul, abs_of_nonneg hy', mul_left_comm] using this
  have h₁ := part hm0 le_rfl hm1 (K:=24) (fun _ h => fourTwo_bound_low h)
  have h₂ := part hm1 hm0 le_rfl (K:=14) (fun _ h => fourTwo_bound_high h)
  change ‖∫ y : ℝ in 0..1, H y‖ ≤ (33/2)*∫ y : ℝ in 0..1, G y
  rw [←intervalIntegral.integral_add_adjacent_intervals (hc'.intervalIntegrable (a:=0) (b:=m) ..)
      (hc'.intervalIntegrable (a:=m) (b:=1) ..),
    ←intervalIntegral.integral_add_adjacent_intervals (gc.intervalIntegrable (a:=0) (b:=m) ..)
      (gc.intervalIntegrable (a:=m) (b:=1) ..)]
  refine (norm_add_le _ _).trans ?_
  dsimp [m] at h₁ h₂ ⊢
  linarith

private theorem fourSet (A : Finset ℕ) : extend A [2,2,2,2] =
    insert (maxPeak A+8) (insert (maxPeak A+6) (insert (maxPeak A+4) (insert (maxPeak A+2) A))) := by
  simp (disch := omega) [extend,maxPeak, Finset.sup_insert, Nat.add_assoc]

/-- Four successive gaps of size two after a nonempty admissible prefix force
at least one nonreal zero. -/
theorem four_gap_obstruction (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty) :
    ¬(peakPolynomial (extend A [2,2,2,2])).Splits := by
  intro hs
  let c := maxPeak A
  let S := extend A [2,2,2,2]
  let f := prefixDensity A
  let M := ∫ y : ℝ in 0..1, f y*y
  have hg : ∀ j ∈ ([2,2,2,2]:List ℕ), 2 ≤ j := by simp
  have hS := extend_admissible A hA _ hg
  have hr (j : ℕ) (hj : j ∈ ([0,2,4,6,8]:List ℕ)) : (peakPolynomial S).eval ((c:ℝ)+j) = 0 := by
    have he : c+j ∈ S := by
      dsimp only [c,S]
      rw [fourSet]
      have htop := maxPeak_mem hne
      rcases (show j=0 ∨ j=2 ∨ j=4 ∨ j=6 ∨ j=8 by simpa using hj) with rfl|rfl|rfl|rfl|rfl <;> simp [htop]
    exact_mod_cast peak_root S hS he
  have h₀ := fourGap_root_ratio (peakPolynomial S) hs c hr
  change 11*|(peakPolynomial S).eval ((c:ℝ)+1)| ≤ ‖peakValue S ((c:ℂ)+z)‖ at h₀
  have hm : 0 < M := prefix_mass_pos A hA hne
  have hreal := extension_density A hA hne _ hg (z:=1) (by norm_num)
  have hint : (fun y : ℝ => (f y:ℂ)*gapKernel [2,2,2,2] 1 y) =
      fun y => (8:ℂ)*((f y*y:ℝ):ℂ) := by
    funext y
    rw [fourTwo_at_one,Complex.ofReal_mul]
    ring
  change peakValue S ((c:ℂ)+1) = risingProduct (1+1) c *
    ∫ y : ℝ in 0..1, (f y:ℂ)*gapKernel [2,2,2,2] 1 y at hreal
  rw [hint,intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal] at hreal
  have hnorm : |(peakPolynomial S).eval ((c:ℝ)+1)| = ‖risingProduct 2 c‖ * (8*M) := by
    have he := peakValue_real S ((c:ℝ)+1)
    push_cast at he
    rw [hreal] at he
    have hh := congrArg (fun u:ℂ => ‖u‖) he.symm
    simpa [norm_mul, show (1+1:ℂ) = 2 by norm_num, M, abs_of_nonneg hm.le] using hh
  rw [hnorm] at h₀
  have hc := extension_density A hA hne _ hg (z:=z) (by norm_num [z,Complex.mul_re])
  change peakValue S ((c:ℂ)+z) = risingProduct (z+1) c *
    ∫ y : ℝ in 0..1, (f y:ℂ)*gapKernel [2,2,2,2] z y at hc
  rw [hc,norm_mul] at h₀
  have hF := weighted_bound f (prefixDensity_continuous A) (prefixDensity_mono A hA hne)
    (fun _ hy => prefixDensity_nonneg A hA hne hy)
  have h₁ := h₀.trans (mul_le_mul (fourGap_factorial_ratio c) hF (norm_nonneg _)
    (by positivity : 0 ≤ 5*‖risingProduct 2 c‖))
  have hpos := mul_pos (norm_pos_iff.mpr (risingProduct_ne_zero (by norm_num : 0 < (2:ℂ).re) c)) hm
  change 11*(‖risingProduct 2 c‖*(8*M)) ≤ 5*‖risingProduct 2 c‖*((33/2)*M) at h₁
  linarith

end BilleyFahrbachTalmageClassification
