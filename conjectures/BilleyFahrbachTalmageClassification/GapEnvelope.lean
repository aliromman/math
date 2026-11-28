module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The error bound for a last gap of size at least ten -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Finset

private noncomputable def edgeCoeff (n : ℕ) (δ : ℝ) : ℝ := |Ring.choose ((n:ℝ)-δ) n|

private theorem edgeCoeff_step (n : ℕ) (δ : ℝ) :
    ((n:ℝ)+1)*edgeCoeff (n+1) δ = |(n:ℝ)+1-δ| * edgeCoeff n δ := by
  have h := Ring.choose_smul_choose ((n:ℝ)+1-δ) (n := n+1) (k := 1) (by omega)
  simp only [Nat.choose_one_right,nsmul_eq_mul,Ring.choose_one_right,Nat.add_sub_cancel,
    Nat.cast_succ, Nat.cast_zero, zero_add] at h
  rw [show (n:ℝ)+1-δ-1 = n-δ by ring] at h
  have hh := congrArg abs h
  simpa [edgeCoeff, abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ n+1)] using hh

private theorem small_edge {δ : ℝ} (h1 : 1 ≤ δ) (h2 : δ ≤ 2) (n : ℕ) (hn : 2 ≤ n) :
    (n:ℝ) * edgeCoeff n δ ≤ (δ-1)*(2-δ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have ha := edgeCoeff_step 1 δ
    have hb := edgeCoeff_step 0 δ
    have hz : edgeCoeff 0 δ = 1 := by simp [edgeCoeff]
    rw [hz] at hb
    norm_num at ha hb ⊢
    rw [abs_of_nonneg (by linarith : 0 ≤ 2-δ)] at ha
    rw [abs_of_nonpos (by linarith : 1-δ ≤ 0)] at hb
    rw [hb] at ha
    linarith
  | succ k hk ih =>
    have hc : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hr := edgeCoeff_step k δ
    rw [abs_of_nonneg (by linarith)] at hr
    have hg : 0 ≤ edgeCoeff k δ := abs_nonneg _
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hg]

private theorem large_edge {δ : ℝ} (h2 : 2 ≤ δ) (h3 : δ ≤ 3) (n : ℕ) (hn : 3 ≤ n) :
    (n:ℝ)*((n:ℝ)-1)*edgeCoeff n δ ≤ (δ-1)*(δ-2)*(3-δ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have ha := edgeCoeff_step 2 δ
    have hb := edgeCoeff_step 1 δ
    have hc := edgeCoeff_step 0 δ
    have hz : edgeCoeff 0 δ = 1 := by simp [edgeCoeff]
    rw [hz] at hc
    norm_num at ha hb hc ⊢
    rw [abs_of_nonneg (by linarith : 0 ≤ 3-δ)] at ha
    rw [abs_of_nonpos (by linarith : 2-δ ≤ 0)] at hb
    rw [abs_of_nonpos (by linarith : 1-δ ≤ 0)] at hc
    linear_combination 2*ha + (3-δ)*hb + (3-δ)*(δ-2)*hc
  | succ k hk ih =>
    have hc : (3:ℝ) ≤ k := by exact_mod_cast hk
    have hr := edgeCoeff_step k δ
    rw [abs_of_nonneg (by linarith)] at hr
    have hg : 0 ≤ edgeCoeff k δ := abs_nonneg _
    push_cast
    nlinarith only [mul_nonneg (by positivity : (0:ℝ) ≤ k)
      (mul_nonneg (sub_nonneg.mpr h2) hg), congrArg (fun t : ℝ => (k:ℝ)*t) hr, ih]

private noncomputable def errorSum (r : ℕ) (δ : ℝ) : ℝ :=
  1 + ∑ j ∈ range r, (∏ k ∈ range (2*j+1), (δ+k))/(2*4^j)

private theorem errorSum_nonneg (r : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ errorSum r δ := by
  unfold errorSum
  positivity

private theorem errorSum_le {r : ℕ} (hr : r ≤ 3) {δ b : ℝ} (h0 : 0 ≤ δ) (hb : δ ≤ b) :
    errorSum r δ ≤ errorSum 3 b := by
  unfold errorSum
  apply add_le_add le_rfl
  trans ∑ j ∈ range r, (∏ k ∈ range (2*j+1), (b+k))/(2*4^j)
  · gcongr with j hj k hk
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hr) (fun j _ _ => by
      have : 0 ≤ b := h0.trans hb
      positivity)

/-- The accumulated error of at most three further two-gaps is strictly
smaller than the leading difference throughout the test interval. -/
theorem choose_error_envelope {h r : ℕ} {s : ℝ} (hh : 10 ≤ h) (hr : r ≤ 3)
    (hs0 : (h:ℝ)-3 ≤ s) (hs1 : s ≤ (h:ℝ)-1) :
    |Ring.choose (s-2) (h-2)| *
      (1+∑ j ∈ range r, (∏ k ∈ range (2*j+1), ((h:ℝ)-s+k))/(2*4^j)) < 1 := by
  let n := h-2
  let δ := (h:ℝ)-s
  have hn : 8 ≤ n := by dsimp [n]; omega
  have hnr : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hδ₁ : 1 ≤ δ := by dsimp [δ]; linarith
  have hδ₃ : δ ≤ 3 := by dsimp [δ]; linarith
  have hδ₀ : 0 ≤ δ := by linarith
  have he : (n:ℝ)-δ = s-2 := by
    dsimp [n,δ]
    rw [Nat.cast_sub (by omega)]
    norm_num
  change |Ring.choose (s-2) n| * errorSum r δ < 1
  rw [←he]
  change edgeCoeff n δ * errorSum r δ < 1
  have hnC : 0 ≤ edgeCoeff n δ := abs_nonneg _
  by_cases h₂ : δ ≤ 2
  · have hL := small_edge hδ₁ h₂ n (by omega)
    have hB : edgeCoeff n δ ≤ 1/32 := by
      nlinarith only [hL, sq_nonneg (δ-3/2), mul_nonneg (sub_nonneg.mpr hnr) hnC]
    have hE := errorSum_le hr hδ₀ h₂
    rw [show errorSum 3 2 = 55/2 by norm_num [errorSum, sum_range_succ, prod_range_succ]] at hE
    nlinarith only [mul_le_mul hB hE (errorSum_nonneg r hδ₀) (by norm_num : (0:ℝ) ≤ 1/32)]
  · have h₂' : 2 ≤ δ := le_of_not_ge h₂
    have hL := large_edge h₂' hδ₃ n (by omega)
    have hsmall : (δ-2)*(3-δ) ≤ 1/4 := by nlinarith [sq_nonneg (δ-5/2)]
    have htri : (δ-1)*(δ-2)*(3-δ) ≤ 1/2 := by
      nlinarith only [mul_le_mul (by linarith : δ-1 ≤ 2) hsmall
        (mul_nonneg (sub_nonneg.mpr h₂') (sub_nonneg.mpr hδ₃)) (by norm_num : (0:ℝ) ≤ 2)]
    have hlen : (56:ℝ) ≤ n*((n:ℝ)-1) := by nlinarith [mul_nonneg (sub_nonneg.mpr hnr) (by linarith : 0 ≤ (n:ℝ)-1)]
    have hB : edgeCoeff n δ ≤ 1/112 := by
      nlinarith only [hL,htri,mul_nonneg (sub_nonneg.mpr hlen) hnC]
    have hE := errorSum_le hr hδ₀ hδ₃
    rw [show errorSum 3 3 = 355/4 by norm_num [errorSum, sum_range_succ, prod_range_succ]] at hE
    nlinarith only [mul_le_mul hB hE (errorSum_nonneg r hδ₀) (by norm_num : (0:ℝ) ≤ 1/112)]

end BilleyFahrbachTalmageClassification
