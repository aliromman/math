module

public import conjectures.BilleyFahrbachTalmageClassification.FourTwoModel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
namespace BilleyFahrbachTalmageClassification

private noncomputable def testCoeff : ℕ → ℂ
  | 0 => 1
  | n+1 => testCoeff n * (peakTestPoint - n)/(n+1)

private theorem testCoeff_eq (n : ℕ) : Ring.choose peakTestPoint n = testCoeff n := by
  induction n with
  | zero => exact Ring.choose_zero_right _
  | succ n ih => rw [peak_choose_succ, ih]; rfl

private theorem two_step (a : ℕ) (F : ℂ → ℂ) (s : ℂ) :
    gapStep a 2 F s = Ring.choose s (a+1) * F ((a+1 : ℕ) : ℂ) - 2*F s := by
  rw [gapStep_two, Nat.cast_succ]

private theorem realPowRe (t : ℝ) (n : ℕ) : ((t:ℂ)^n).re = t^n := by rw [←Complex.ofReal_pow]; rfl
private theorem realPowIm (t : ℝ) (n : ℕ) : ((t:ℂ)^n).im = 0 := by rw [←Complex.ofReal_pow]; rfl
private theorem difference_nat (k : ℕ) (y : ℝ) :
    difference (k : ℂ) y = (((1+y)/2:ℝ):ℂ)^k - (((1-y)/2:ℝ):ℂ)^k := by
  simp [difference]

private theorem difference_nat_real (k : ℕ) (y : ℝ) : difference (k:ℂ) y =
    (((((1+y)/2)^k - ((1-y)/2)^k) : ℝ):ℂ) := by
  rw [difference_nat,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_pow]

private theorem difference_nat_pair (k : ℕ) (y : ℝ) : difference (k:ℂ) y =
    ⟨((1+y)/2)^k - ((1-y)/2)^k, 0⟩ := by rw [difference_nat_real]; rfl

theorem fourTwo_formula (y : ℝ) :
    gapKernel [2,2,2,2] peakTestPoint y =
      16*difference peakTestPoint y + (y : ℂ)*fourCorrections (y^2) := by
  simp only [gapKernel, applyGaps, two_step, difference_nat_pair, Ring.choose_natCast, testCoeff_eq]
  apply Complex.ext <;>
    norm_num [Nat.choose, testCoeff, peakTestPoint, realPowRe, realPowIm, fourCorrections,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.div_re,Complex.div_im,Complex.normSq_apply] <;> ring

theorem fourTwo_at_one (y : ℝ) : gapKernel [2,2,2,2] 1 y = 8 * (y : ℂ) := by
  rw [show (1:ℂ) = ((1:ℕ):ℂ) by norm_num]
  simp only [gapKernel, applyGaps, two_step, Ring.choose_natCast, difference_nat_real]
  norm_num [Nat.choose]
  ring

theorem lowApprox_eq (y : ℝ) :
    (y : ℂ) * lowApprox (y^2) =
      16*truncTest 12 (-1/2) * (truncTest 12 y - truncTest 12 (-y)) +
      (y : ℂ)*fourCorrections (y^2) := by
  simp only [truncTest, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [testCoeff_eq]
  apply Complex.ext <;> norm_num [testCoeff,Complex.div_re,Complex.div_im,Complex.normSq_apply,peakTestPoint,realPowRe,realPowIm,lowApprox,fourCorrections,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im] <;> ring_nf <;> simp [Complex.neg_re, Complex.neg_im, realPowRe, realPowIm] <;> ring

theorem highApprox_eq (v : ℝ) :
    highApprox v = 16*truncTest 6 (-v) + (((1-2*v) : ℝ):ℂ)*fourCorrections ((1-2*v)^2) := by
  simp only [truncTest, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [testCoeff_eq]
  apply Complex.ext <;> norm_num [testCoeff,Complex.div_re,Complex.div_im,Complex.normSq_apply,peakTestPoint,realPowRe,realPowIm,highApprox,fourCorrections,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im] <;> ring_nf <;> simp [Complex.neg_re, Complex.neg_im, realPowRe, realPowIm] <;> ring

end BilleyFahrbachTalmageClassification
