module

public import conjectures.BilleyFahrbachTalmageClassification.GapValues
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Integral representation after any list of gaps -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials MeasureTheory

private theorem pos_index {j a g : ℕ} (hj : j ∈ Ico (a+1) (a+g)) : 0 < (j:ℂ).re := by
  rw [Complex.natCast_re]
  exact_mod_cast (show 0 < j by have := (mem_Ico.mp hj).1; omega)

theorem difference_continuous {z : ℂ} (hz : 0 < z.re) : Continuous (difference z) := by
  unfold difference
  apply Continuous.sub <;> apply (Complex.continuous_ofReal_cpow_const hz).comp <;> fun_prop

theorem gapStep_continuous (a g : ℕ) (F : ℝ → ℂ → ℂ)
    (hf : ∀ z : ℂ, 0 < z.re → Continuous (fun y => F y z)) {z : ℂ} (hz : 0 < z.re) :
    Continuous (fun y => gapStep a g (F y) z) := by
  unfold gapStep
  apply Continuous.add
  · split_ifs <;> first | exact continuous_const | exact continuous_const.mul (hf z hz)
  · apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (hf _ (pos_index hj))

theorem gapKernel_continuous (gs : List ℕ) {z : ℂ} (hz : 0 < z.re) : Continuous (gapKernel gs z) := by
  suffices h : ∀ (gs : List ℕ) (a : ℕ) (F : ℝ → ℂ → ℂ),
      (∀ w : ℂ, 0 < w.re → Continuous (fun y => F y w)) →
      ∀ w : ℂ, 0 < w.re → Continuous (fun y => applyGaps gs a (F y) w) from
    h gs 0 (fun y w => difference w y) (fun _ hw => difference_continuous hw) z hz
  intro xs
  induction xs with
  | nil => exact fun _ _ hF _ hw => hF _ hw
  | cons g xs ih =>
    intro a F hF w hw
    exact ih (a+g) (fun y => gapStep a g (F y)) (fun _ hw' => gapStep_continuous a g F hF hw') w hw

private theorem gapStep_integral (a g : ℕ) (f : ℝ → ℂ) (hc : Continuous f)
    (F : ℝ → ℂ → ℂ) (hf : ∀ z : ℂ, 0 < z.re → Continuous (fun y => F y z))
    {z : ℂ} (hz : 0 < z.re) :
    gapStep a g (fun w => ∫ y : ℝ in 0..1, f y * F y w) z =
      ∫ y : ℝ in 0..1, f y * gapStep a g (F y) z := by
  let J := Ico (a+1) (a+g)
  let q (j : ℕ) := (-1:ℂ)^(a+g-1-j) * Ring.choose z j
  let k : ℂ := if Even g then -2 else 0
  have hs (G : ℂ → ℂ) : gapStep a g G z = k*G z + ∑ j ∈ J, q j * G j := by
    by_cases he : Even g <;> simp [gapStep,k,J,q,he]
  simp_rw [hs]
  simp_rw [mul_add, mul_sum, mul_left_comm (f _) k, mul_left_comm (f _) (q _)]
  have ht (j : ℕ) (hj : j ∈ J) : Continuous (fun y => q j * (f y * F y j)) :=
    continuous_const.mul (hc.mul (hf j (pos_index hj)))
  rw [intervalIntegral.integral_add
    (f := fun y => k*(f y*F y z)) (g := fun y => ∑ j ∈ J, q j*(f y*F y j))
    ((continuous_const.mul (hc.mul (hf z hz))).intervalIntegrable ..)
    ((continuous_finsetSum J ht).intervalIntegrable ..)]
  rw [intervalIntegral.integral_finsetSum (fun j hj => (ht j hj).intervalIntegrable ..)]
  simp_rw [intervalIntegral.integral_const_mul]

private theorem applyGaps_integral (gs : List ℕ) (a : ℕ) (f : ℝ → ℂ) (hc : Continuous f)
    (F : ℝ → ℂ → ℂ) (hf : ∀ z : ℂ, 0 < z.re → Continuous (fun y => F y z))
    {z : ℂ} (hz : 0 < z.re) :
    applyGaps gs a (fun w => ∫ y : ℝ in 0..1, f y * F y w) z =
      ∫ y : ℝ in 0..1, f y * applyGaps gs a (F y) z := by
  induction gs generalizing a F z with
  | nil => rfl
  | cons g gs ih =>
    simp only [applyGaps]
    trans applyGaps gs (a+g) (fun w => ∫ y : ℝ in 0..1, f y*gapStep a g (F y) w) z
    · exact applyGaps_congr gs _ (fun w hw => gapStep_integral _ _ f hc F hf hw) hz
    · exact ih _ (fun y => gapStep a g (F y)) (fun _ hw => gapStep_continuous _ _ F hf hw) hz

theorem extension_density (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty)
    (gs : List ℕ) (hg : ∀ g ∈ gs, 2 ≤ g) {z : ℂ} (hz : 0 < z.re) :
    peakValue (extend A gs) ((maxPeak A:ℂ)+z) = risingProduct (z+1) (maxPeak A) *
      ∫ y : ℝ in 0..1, (prefixDensity A y : ℂ) * gapKernel gs z y := by
  have hn : risingProduct (z+1) (maxPeak A) ≠ 0 := risingProduct_ne_zero (by simp; linarith) _
  rw [mul_comm (risingProduct _ _)]
  apply (div_eq_iff hn).mp
  change normalizedValue _ (extend A gs) z = _
  rw [normalized_extend (maxPeak A) 0 A hA (by simp) gs hg hz]
  trans applyGaps gs 0 (fun w => ∫ y : ℝ in 0..1, (prefixDensity A y:ℂ)*difference w y) z
  · exact applyGaps_congr _ _ (fun w hw => normalized_prefix A hA hne hw) hz
  · exact applyGaps_integral _ _ (fun y => (prefixDensity A y:ℂ))
      (Complex.continuous_ofReal.comp (prefixDensity_continuous A)) (fun y w => difference w y)
      (fun _ hw => difference_continuous hw) hz

theorem extension_empty (gs : List ℕ) (hg : ∀ g ∈ gs, 2 ≤ g) {z : ℂ} (hz : 0 < z.re) :
    peakValue (extend ∅ gs) z = gapKernel gs z 1 := by
  have he : maxPeak ∅ = 0 := by simp [maxPeak]
  have h := normalized_extend 0 0 ∅ (by simp [Admissible]) (by simpa using he) gs hg hz
  simpa [normalizedValue, risingProduct, gapKernel] using h.trans (applyGaps_congr gs 0
    (F:=normalizedValue 0 ∅) (G:=fun w => difference w 1) (by
      intro w hw
      have hw' : w ≠ 0 := by rintro rfl; simp at hw
      simp [normalized_empty, difference, Complex.zero_cpow hw']) hz)

theorem difference_one (y : ℝ) : difference 1 y = (y:ℂ) := by
  simp [difference]
  ring

theorem prefix_mass_pos (A : Finset ℕ) (hA : Admissible A) (hne : A.Nonempty) :
    0 < ∫ y : ℝ in 0..1, prefixDensity A y * y := by
  have hp := (mul_pos (show 0 < (maxPeak A:ℝ)-1 by
    have h := (last_peak_reduction hA hne).1; exact_mod_cast (show (1:ℤ) < (maxPeak A:ℤ) by omega) |> sub_pos.mpr)
    (leadingValue_pos A hA hne)).trans_le (grow_after_peak A hA hne)
  have h := density_formula A hA hne (z:=1) (by norm_num)
  have hreal : peakValue A ((maxPeak A:ℂ)+1) = (((peakPolynomial A).eval ((maxPeak A:ℝ)+1):ℝ):ℂ) := by
    simpa using peakValue_real A ((maxPeak A:ℝ)+1)
  rw [hreal] at h
  simp_rw [difference_one, ← Complex.ofReal_mul] at h
  rw [intervalIntegral.integral_ofReal] at h
  have hprod : risingProduct (1+1) (maxPeak A) =
      ((∏ j ∈ range (maxPeak A), ((1+1:ℝ)+j) : ℝ):ℂ) := by simp [risingProduct]
  rw [hprod, ← Complex.ofReal_mul] at h
  have hh := Complex.ofReal_inj.mp h
  rw [hh] at hp
  have hpos : 0 < ∏ j ∈ range (maxPeak A), ((1+1:ℝ)+j) := Finset.prod_pos (fun _ _ => by positivity)
  exact pos_of_mul_pos_right hp hpos.le

end BilleyFahrbachTalmageClassification
