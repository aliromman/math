module

public import conjectures.BilleyFahrbachTalmageClassification.Corrections
public import conjectures.BilleyFahrbachTalmageClassification.DifferenceBounds
public import conjectures.BilleyFahrbachTalmageClassification.GapEnvelope
public import conjectures.BilleyFahrbachTalmageClassification.IntegerKernels
public import conjectures.BilleyFahrbachTalmageClassification.PositiveValues
public import conjectures.BilleyFahrbachTalmageClassification.PrefixIntegral
public import conjectures.BilleyFahrbachTalmageClassification.Tail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A gap of length at least ten followed by at most three gaps of length two -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Finset Set PermutationPeaks PeakPolynomials

theorem extend_append (A : Finset ℕ) (xs ys : List ℕ) :
    extend A (xs++ys) = extend (extend A xs) ys := by
  induction xs generalizing A with
  | nil => rfl
  | cons g gs ih => exact ih _

private theorem valid_suffix {h : ℕ} (hh : 2 ≤ h) (r : ℕ) :
    ∀ g ∈ (h::List.replicate r 2), 2 ≤ g := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl|ht
  · exact hh
  · have := (List.mem_replicate.mp ht).2
    omega

private theorem suffix_max (A : Finset ℕ) (h r : ℕ) :
    maxPeak (extend A (h::List.replicate r 2)) = maxPeak A + (h+2*r) := by
  simp [extend_max, List.sum_replicate, Nat.mul_comm]

private theorem real_part_choose (s : ℝ) (k : ℕ) (w : ℂ) :
    (Ring.choose (s:ℂ) k * w).re = Ring.choose s k * w.re := by
  have hc := Ring.map_choose (algebraMap ℝ ℂ) s k
  change (↑(Ring.choose s k) : ℂ) = Ring.choose (s:ℂ) k at hc
  rw [← hc, Complex.mul_re]
  simp

private theorem suffix_next (A : Finset ℕ) (hA : Admissible A) {h : ℕ}
    (hh : 2 ≤ h) (i : ℕ) {s : ℝ} (hs : 0 < s) :
    (normalizedValue (maxPeak A) (extend A (h::List.replicate (i+1) 2)) s).re =
      Ring.choose s (h+2*i+1) *
        (normalizedValue (maxPeak A) (extend A (h::List.replicate i 2)) ↑(h+2*i+1 : ℕ)).re -
        2*(normalizedValue (maxPeak A) (extend A (h::List.replicate i 2)) s).re := by
  let T := extend A (h::List.replicate i 2)
  have hT : Admissible T := extend_admissible A hA _ (valid_suffix hh i)
  have hm : maxPeak T = maxPeak A+(h+2*i) := suffix_max A h i
  have he : h::List.replicate (i+1) 2 = (h::List.replicate i 2)++[2] := by
    rw [List.replicate_add]; rfl
  rw [he, extend_append]
  change (normalizedValue (maxPeak A) (insert (maxPeak T+2) T) (s:ℂ)).re = _
  rw [hm, Nat.add_assoc, normalized_gap _ _ _ hT hm 2 (by decide) (by simpa : 0 < (s:ℂ).re)]
  rw [gapStep_two, Complex.sub_re, real_part_choose]
  simp [T]

private theorem delta_norm {s y : ℝ} (hs : 0 ≤ s) (hy : y ∈ Set.Icc 0 1) :
    ‖difference (s:ℂ) y‖ = (difference (s:ℂ) y).re := by
  rw [difference, ← Complex.ofReal_cpow (by linarith [hy.1] : 0 ≤ (1+y)/2),
    ← Complex.ofReal_cpow (by linarith [hy.2] : 0 ≤ (1-y)/2), ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  exact abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow (by linarith [hy.2]) (by linarith [hy.1]) hs))

private theorem average_tail (A : Finset ℕ) (hA : Admissible A) {h : ℕ} (hh : 10 ≤ h)
    {s : ℝ} (hs₀ : (h:ℝ)-3 ≤ s) (hs₁ : s ≤ (h:ℝ)-1) :
    |(normalizedValue (maxPeak A) (extend A [h]) s).re + (normalizedValue (maxPeak A) A s).re| ≤
      |Ring.choose (s-2) (h-2)| * (normalizedValue (maxPeak A) A s).re := by
  have hs : 0 < (s:ℂ).re := by
    have hh' : (10:ℝ) ≤ h := by exact_mod_cast hh
    change 0 < s
    linarith
  let f (y : ℝ) := (gapKernel [h] (s:ℂ) y).re
  let g (y : ℝ) := (difference (s:ℂ) y).re
  let B := |Ring.choose (s-2) (h-2)|
  have hf : Continuous f := Complex.continuous_re.comp (gapKernel_continuous [h] hs)
  have hg : Continuous g := Complex.continuous_re.comp (difference_continuous hs)
  have ha (y : ℝ) (hy : y ∈ Set.Icc 0 1) : |f y+g y| ≤ B*g y := by
    calc
      _ ≤ ‖gapKernel [h] (s:ℂ) y + difference (s:ℂ) y‖ := Complex.abs_re_le_norm _
      _ ≤ _ := by
        simpa only [B,g,delta_norm (by simpa using hs.le) hy] using single_gap_error hh hs₀ hs₁ hy.1 hy.2
  have hF := normalized_re_kernel A hA [h] (by simp; omega) hs
  have hG := normalized_re_kernel A hA [] (by simp) hs
  change (normalizedValue (maxPeak A) A s).re = prefixIntegral A g at hG
  rw [hF,hG]
  change |prefixIntegral A f+prefixIntegral A g| ≤ B*prefixIntegral A g
  rw [← prefixIntegral_add A hf hg, ← prefixIntegral_scale]
  apply abs_le.mpr
  constructor
  · have hlow := prefixIntegral_mono A hA (f:=fun y => (-B)*g y) (g:=fun y => f y+g y)
      (continuous_const.mul hg) (hf.add hg)
      (fun y hy => (show (-B)*g y ≤ f y+g y by linarith [(abs_le.mp (ha y hy)).1]))
    rw [prefixIntegral_scale A (-B) g, neg_mul] at hlow
    rw [prefixIntegral_scale A B g]
    exact hlow
  · exact prefixIntegral_mono A hA (hf.add hg) (continuous_const.mul hg)
      (fun y hy => (abs_le.mp (ha y hy)).2)

private theorem average_power (A : Finset ℕ) (hA : Admissible A) {s : ℝ} {h : ℕ}
    (hs : 1 ≤ s) (hh : s ≤ h) :
    s*(normalizedValue (maxPeak A) A h).re ≤ (h:ℝ)*(normalizedValue (maxPeak A) A s).re := by
  have hp : 0 < (s:ℂ).re := by simp; linarith
  have hq : 0 < (h:ℂ).re := by simp; exact_mod_cast (by exact_mod_cast (by linarith : 0 < (h:ℝ)) : 0<h)
  have hd := normalized_re_kernel A hA [] (by simp) hp
  have hi := normalized_re_kernel A hA [] (by simp) hq
  simp only [extend, gapKernel, applyGaps] at hd hi
  rw [hd,hi, ← prefixIntegral_scale, ← prefixIntegral_scale]
  apply prefixIntegral_mono A hA
    (continuous_const.mul (Complex.continuous_re.comp (difference_continuous hq)))
    (continuous_const.mul (Complex.continuous_re.comp (difference_continuous hp)))
  intro y hy
  change s*(difference (h:ℂ) y).re ≤ (h:ℝ)*(difference (s:ℂ) y).re
  rw [← Complex.ofReal_natCast, difference_real_part hy, difference_real_part hy]
  exact power_difference _ _ hs hh (by linarith [hy.2]) (by linarith [hy.1]) (by linarith [hy.2])

private theorem first_coefficient (A : Finset ℕ) (hA : Admissible A) {h : ℕ} (hh : 2 ≤ h) :
    (normalizedValue (maxPeak A) (extend A [h]) ((h+1:ℕ):ℂ)).re ≤
      ((h:ℝ)+1)*(normalizedValue (maxPeak A) A h).re := by
  have hp : 0 < ((h+1:ℕ):ℂ).re := by simp; positivity
  have hq : 0 < (h:ℂ).re := by simp; exact_mod_cast (show 0 < h by omega)
  have hd := normalized_re_kernel A hA [h] (by simpa) hp
  have hi := normalized_re_kernel A hA [] (by simp) hq
  simp only [extend, gapKernel, applyGaps] at hi
  rw [hd,hi, ← prefixIntegral_scale]
  apply prefixIntegral_mono A hA (Complex.continuous_re.comp (gapKernel_continuous [h] hp))
    (continuous_const.mul (Complex.continuous_re.comp (difference_continuous hq)))
  intro y hy
  change (gapKernel [h] ((h+1:ℕ):ℂ) y).re ≤ ((h:ℝ)+1)*(difference (h:ℂ) y).re
  rw [Nat.cast_succ, kernel_after_gap h (by omega)]
  have hn := difference_next_nonneg h hy
  rw [Nat.cast_succ] at hn
  simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
    Complex.add_im, Complex.natCast_im, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    add_zero, zero_mul, sub_zero]
  linarith

theorem large_gap_sign (A : Finset ℕ) (hA : Admissible A) {h r : ℕ} (hh : 10 ≤ h)
    (hr : r ≤ 3) {s : ℝ} (hs₀ : (h:ℝ)-3 ≤ s) (hs₁ : s ≤ (h:ℝ)-1) :
    0 < (-1:ℝ)^(r+1) * (normalizedValue (maxPeak A) (extend A (h::List.replicate r 2)) s).re := by
  let T (i : ℕ) := extend A (h::List.replicate i 2)
  let C (i : ℕ) := (normalizedValue (maxPeak A) (T i) (h+2*i+1:ℕ)).re
  let D := (normalizedValue (maxPeak A) A s).re
  let Dh := (normalizedValue (maxPeak A) A h).re
  have hh' : (10:ℝ) ≤ h := by exact_mod_cast hh
  have hs : 1 ≤ s := by linarith
  have hs' : s ≤ h := by linarith
  have hm (i : ℕ) : maxPeak (T i) = maxPeak A+(h+2*i) := suffix_max _ _ _
  have hAd (i : ℕ) : Admissible (T i) := extend_admissible A hA _ (valid_suffix (by omega) i)
  have hpos (i j : ℕ) (hj : h+2*i<j) : 0 < (normalizedValue (maxPeak A) (T i) j).re :=
    normalizedValue_pos _ _ (hAd i) _ (by rw [hm]; omega)
  have hDh : 0 < Dh := normalizedValue_pos _ _ hA _ (by omega)
  have hcmp := average_power A hA hs hs'
  change s*Dh ≤ (h:ℝ)*D at hcmp
  have hD : 0 < D := by
    by_contra! hn
    linarith [mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ (h:ℝ)) hn,
      mul_pos (by linarith : 0 < s) hDh]
  apply correction_sign h r s D Dh C (fun i => (normalizedValue (maxPeak A) (T i) s).re)
    (by omega) hs hs' hD hcmp (fun i => (hpos i _ (by omega)).le)
    (by simpa [C,T,Dh] using first_coefficient A hA (h:=h) (by omega)) ?_
    (by simpa [T,D] using average_tail A hA hh hs₀ hs₁)
    (fun i => suffix_next A hA (by omega) i (by linarith)) (choose_error_envelope hh hr hs₀ hs₁)
  intro i
  let k := h+2*i+1
  let j := k+2
  have hv := suffix_next A hA (h:=h) (by omega) i (s:=(j:ℝ)) (by dsimp [j,k]; positivity)
  have hidx : h+2*(i+1)+1=j := by dsimp [j,k]; omega
  have hc : j.choose k = j.choose 2 := Nat.choose_symm_of_eq_add rfl
  simp only [Complex.ofReal_natCast, Ring.choose_natCast] at hv
  change (normalizedValue (maxPeak A) (T (i+1)) j).re =
    (j.choose k:ℝ)*C i-2*(normalizedValue (maxPeak A) (T i) j).re at hv
  rw [hc, Nat.cast_choose_two] at hv
  have hp := hpos i j (by dsimp [j,k]; omega)
  change 2*(normalizedValue _ (T (i+1)) (h+2*(i+1)+1:ℕ)).re ≤ _
  rw [hidx]
  have hj : (j:ℝ) = (h:ℝ)+2*i+3 := by dsimp [j,k]; push_cast; ring
  rw [hj] at hv
  linarith

end BilleyFahrbachTalmageClassification
