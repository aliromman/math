module

public import conjectures.BilleyFahrbachTalmageClassification.ExtensionDensity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Exact integer values on either side of the next peak -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials

private theorem reflected_binomial (k : ℕ) (u : ℂ) :
    ∑ j ∈ range (k+1), (-1:ℂ)^j * (k.choose j) * u^j = (1-u)^k := by
  rw [show (1-u:ℂ)=(-u)+1 by ring, add_pow]
  apply sum_congr rfl
  intro j hj
  rw [show (-u:ℂ) = (-1)*u by ring, mul_pow, one_pow, mul_one]
  ring

private theorem alternate_difference (k : ℕ) (y : ℝ) :
    ∑ j ∈ range (k+1), (-1:ℂ)^j * (k.choose j) * difference j y = -difference k y := by
  let u : ℂ := ((1+y)/2:ℝ)
  let v : ℂ := ((1-y)/2:ℝ)
  have hu : 1-u=v := by dsimp [u,v]; push_cast; ring
  have hv : 1-v=u := by dsimp [u,v]; push_cast; ring
  simp only [difference, Complex.cpow_natCast, mul_sub, sum_sub_distrib]
  change (∑ j ∈ range (k+1), (-1:ℂ)^j * (k.choose j) * u^j) -
    (∑ j ∈ range (k+1), (-1:ℂ)^j * (k.choose j) * v^j) = -(u^k-v^k)
  rw [reflected_binomial, reflected_binomial, hu, hv]
  ring

private theorem sign_sub {n j : ℕ} (hj : j ≤ n) :
    (-1:ℂ)^(n-j) = (-1:ℂ)^n * (-1:ℂ)^j := by
  calc
    _ = (-1:ℂ)^(n-j)*((-1:ℂ)^j*(-1:ℂ)^j) := by rw [← mul_pow]; norm_num
    _ = _ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]

theorem kernel_before_gap (h k : ℕ) (hk : 0 < k) (hkh : k<h) (y : ℝ) :
    gapKernel [h] k y = -difference k y := by
  let f (j : ℕ) := (-1:ℂ)^j * (k.choose j) * difference j y
  have h0 : f 0 = 0 := by simp [f,difference]
  have ht : ∑ j ∈ Ico 1 h, f j = -difference k y := by
    have hi := Finset.sum_Ico_eq_sub (f:=f) (show 1 ≤ h by omega)
    rw [hi, sum_range_one, h0, sub_zero]
    rw [← alternate_difference]
    symm
    apply sum_subset (range_mono (show k+1 ≤ h by omega))
    intro j hj hjk
    have hh : k<j := by simp at hjk; omega
    simp [Nat.choose_eq_zero_of_lt hh]
  have hsum : ∑ j ∈ Ico 1 h, (-1:ℂ)^(h-1-j) * Ring.choose (k:ℂ) j * difference j y =
      (-1:ℂ)^(h-1) * (∑ j ∈ Ico 1 h, f j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hh := (mem_Ico.mp hj).2
    rw [sign_sub (by omega : j ≤ h-1), Ring.choose_natCast]
    simp [f,mul_assoc]
  simp only [gapKernel, applyGaps, gapStep, Nat.zero_add]
  rw [hsum, ht]
  by_cases he : Even h
  · have ho : Odd (h-1) := by rw [Nat.odd_iff]; rw [Nat.even_iff] at he; omega
    rw [ite_eq_left he, ho.neg_one_pow]
    ring
  · have he' : Even (h-1) := by rw [Nat.even_iff]; rw [Nat.even_iff] at he; omega
    rw [ite_eq_right he, he'.neg_one_pow]
    ring

theorem kernel_at_gap (h : ℕ) (hh : 1 ≤ h) (y : ℝ) : gapKernel [h] h y = 0 := by
  have hb := kernel_before_gap (h+1) h hh (by omega) y
  change gapStep 0 (h+1) (fun w => difference w y) h = _ at hb
  simp only [gapStep_succ 0 h hh, Nat.cast_zero, Ring.choose_natCast, Nat.choose_self,
    Nat.cast_one, zero_add, one_mul] at hb
  change gapStep 0 h (fun w => difference w y) h = 0
  linear_combination -hb

theorem kernel_after_gap (h : ℕ) (hh : 1 ≤ h) (y : ℝ) :
    gapKernel [h] (h+1) y = (h+1)*difference h y - 2*difference (h+1) y := by
  have hnext := kernel_at_gap (h+1) (by omega) y
  change gapStep 0 (h+1) (fun w => difference w y) ((h+1:ℕ):ℂ) = 0 at hnext
  rw [gapStep_succ 0 h hh] at hnext
  simp only [Nat.cast_zero, zero_add, Ring.choose_natCast, Nat.choose_succ_self_right] at hnext
  push_cast at hnext
  change gapStep 0 h (fun w => difference w y) (h+1) = _
  linear_combination -hnext

private theorem two_gaps_below (r a k : ℕ) (hk : k≤a) (F : ℂ → ℂ) :
    applyGaps (List.replicate r 2) a F k = (-2:ℂ)^r * F k := by
  induction r generalizing a F with
  | zero => simp [applyGaps]
  | succ r ih =>
    rw [List.replicate_succ, applyGaps, ih _ (by omega) _, gapStep_two, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (by omega : k<a+1), Nat.cast_zero, zero_mul, zero_sub, pow_succ]
    ring

theorem kernel_integer_before (h r k : ℕ) (hk : 0<k) (hkh : k<h) (y : ℝ) :
    gapKernel (h::List.replicate r 2) k y = -(-2:ℂ)^r * difference k y := by
  change applyGaps (List.replicate r 2) (0+h) (gapStep 0 h (fun w => difference w y)) k = _
  rw [two_gaps_below _ _ _ (by omega)]
  change (-2:ℂ)^r * gapKernel [h] k y = _
  rw [kernel_before_gap _ _ hk hkh]
  ring

theorem integer_before_gap (A : Finset ℕ) (hA : Admissible A) (h r k : ℕ)
    (hh : 2≤h) (hk : 0<k) (hkh : k<h) :
    (peakPolynomial (extend A (h::List.replicate r 2))).eval ((maxPeak A:ℝ)+k) =
      -(-2:ℝ)^r * (peakPolynomial A).eval ((maxPeak A:ℝ)+k) := by
  let gs := h::List.replicate r 2
  have hg : ∀ j ∈ gs, 2≤j := by
    intro j hj
    simp only [gs,List.mem_cons,List.mem_replicate] at hj
    rcases hj with rfl | ⟨_,rfl⟩ <;> omega
  have hpos : 0 < (k:ℂ).re := by simp; exact_mod_cast hk
  have he : peakValue (extend A gs) ((maxPeak A:ℂ)+k) =
      -(-2:ℂ)^r * peakValue A ((maxPeak A:ℂ)+k) := by
    by_cases hne : A.Nonempty
    · rw [extension_density A hA hne gs hg hpos, density_formula A hA hne hpos]
      simp_rw [gs, kernel_integer_before _ _ _ hk hkh, mul_left_comm _ (-(-2:ℂ)^r),
        intervalIntegral.integral_const_mul]
      ring
    · have ha := not_nonempty_iff_eq_empty.mp hne
      subst A
      rw [show maxPeak ∅=0 by simp [maxPeak], Nat.cast_zero, zero_add, extension_empty gs hg hpos,
        kernel_integer_before _ _ _ hk hkh]
      simp [peakValue, peakPolynomial_empty, difference, Complex.zero_cpow (by exact_mod_cast hk.ne' : (k:ℂ)≠0)]
  have hx : (maxPeak A:ℂ)+k = (((maxPeak A:ℝ)+k:ℝ):ℂ) := by simp
  rw [hx, peakValue_real, peakValue_real] at he
  exact_mod_cast he

end BilleyFahrbachTalmageClassification
