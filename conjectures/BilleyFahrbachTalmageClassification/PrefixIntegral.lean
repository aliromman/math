module

public import conjectures.BilleyFahrbachTalmageClassification.ExtensionDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Integration over a prefix endpoint

A nonempty prefix has a nonnegative density. The empty prefix evaluates
the same kernel at one. Both operations preserve the inequalities used below. -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Set MeasureTheory PermutationPeaks PeakPolynomials

noncomputable def prefixIntegral (A : Finset ℕ) (f : ℝ → ℝ) : ℝ :=
  if A.Nonempty then ∫ y : ℝ in 0..1, prefixDensity A y*f y else f 1

theorem prefixIntegral_scale (A : Finset ℕ) (k : ℝ) (f : ℝ → ℝ) :
    prefixIntegral A (fun y => k*f y) = k*prefixIntegral A f := by
  unfold prefixIntegral
  split_ifs
  · simp_rw [mul_left_comm (prefixDensity A _) k, intervalIntegral.integral_const_mul]
  · rfl

theorem prefixIntegral_add (A : Finset ℕ) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    prefixIntegral A (fun y => f y+g y) = prefixIntegral A f + prefixIntegral A g := by
  unfold prefixIntegral
  split_ifs
  · simp_rw [mul_add]
    exact intervalIntegral.integral_add (((prefixDensity_continuous A).mul hf).intervalIntegrable ..)
      (((prefixDensity_continuous A).mul hg).intervalIntegrable ..)
  · rfl

theorem prefixIntegral_mono (A : Finset ℕ) (hA : Admissible A) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ y ∈ Icc 0 1, f y ≤ g y) :
    prefixIntegral A f ≤ prefixIntegral A g := by
  unfold prefixIntegral
  split_ifs with hne
  · exact intervalIntegral.integral_mono_on (by norm_num)
      (((prefixDensity_continuous A).mul hf).intervalIntegrable ..)
      (((prefixDensity_continuous A).mul hg).intervalIntegrable ..)
      (fun y hy => mul_le_mul_of_nonneg_left (h y hy) (prefixDensity_nonneg A hA hne hy))
  · exact h 1 (by constructor <;> norm_num)

theorem prefixIntegral_pos (A : Finset ℕ) (hA : Admissible A) {f : ℝ → ℝ}
    (hf : Continuous f) (h : ∀ y ∈ Ioc 0 1, 0 < f y) : 0 < prefixIntegral A f := by
  unfold prefixIntegral
  split_ifs with hne
  · have hex : ∃ y ∈ Icc 0 1, 0 < prefixDensity A y*y := by
      by_contra! hbad
      have ht : (∫ y : ℝ in 0..1, prefixDensity A y*y) ≤ ∫ _y : ℝ in 0..1, (0:ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (((prefixDensity_continuous A).mul continuous_id).intervalIntegrable ..)
          (continuous_const.intervalIntegrable ..) hbad
      simpa using (not_le_of_gt (prefix_mass_pos A hA hne)) (by simpa using ht)
    obtain ⟨y,hy,hypos⟩ := hex
    have hden := prefixDensity_nonneg A hA hne hy
    have hs : 0 < prefixDensity A y ∧ 0 < y := by
      rcases mul_pos_iff.mp hypos with hs|hs
      · exact hs
      · linarith [hs.1]
    exact intervalIntegral.integral_pos (by norm_num)
      (((prefixDensity_continuous A).mul hf).continuousOn)
      (fun t ht => mul_nonneg (prefixDensity_nonneg A hA hne ⟨ht.1.le,ht.2⟩) (h t ht).le)
      ⟨y,hy,mul_pos hs.1 (h y ⟨hs.2,hy.2⟩)⟩
  · exact h 1 (by constructor <;> norm_num)

theorem normalized_re_kernel (A : Finset ℕ) (hA : Admissible A) (gs : List ℕ)
    (hg : ∀ g ∈ gs, 2 ≤ g) {z : ℂ} (hz : 0 < z.re) :
    (normalizedValue (maxPeak A) (extend A gs) z).re =
      prefixIntegral A (fun y => (gapKernel gs z y).re) := by
  unfold prefixIntegral
  split_ifs with hne
  · have hn : risingProduct (z+1) (maxPeak A) ≠ 0 := risingProduct_ne_zero (by simp; linarith) _
    rw [normalizedValue, extension_density A hA hne gs hg hz, mul_div_cancel_left₀ _ hn]
    have hi : IntervalIntegrable (fun y => (prefixDensity A y:ℂ)*gapKernel gs z y) volume 0 1 :=
      ((Complex.continuous_ofReal.comp (prefixDensity_continuous A)).mul
      (gapKernel_continuous gs hz)).intervalIntegrable (μ := volume) 0 1
    change RCLike.re (∫ y : ℝ in 0..1, (prefixDensity A y:ℂ)*gapKernel gs z y) = _
    rw [← intervalIntegral.intervalIntegral_re hi]
    simp [RCLike.re_to_complex]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    subst A
    simpa [normalizedValue, maxPeak, risingProduct] using congrArg Complex.re (extension_empty gs hg hz)

end BilleyFahrbachTalmageClassification
