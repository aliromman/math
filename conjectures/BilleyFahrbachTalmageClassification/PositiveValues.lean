module

public import conjectures.BilleyFahrbachTalmageClassification.GapValues
import Mathlib.Tactic.Positivity

/-! # Positive normalized values beyond the last peak -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials

noncomputable def realRising (x : ℝ) (c : ℕ) : ℝ := ∏ j ∈ range c, (x+j)

theorem realRising_cast (x : ℝ) (c : ℕ) : risingProduct (x:ℂ) c = (realRising x c:ℂ) := by
  simp [risingProduct, realRising]

theorem realRising_pos {x : ℝ} (hx : 0<x) (c : ℕ) : 0 < realRising x c :=
  prod_pos (fun j _ => add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg j))

theorem peak_after_pos (S : Finset ℕ) (hS : Admissible S) {n : ℕ} (hn : maxPeak S<n) :
    0 < (peakPolynomial S).eval (n:ℝ) := by
  by_cases hne : S.Nonempty
  · have hm := (last_peak_reduction hS hne).1
    have hfirst := (mul_pos (show 0 < (maxPeak S:ℝ)-1 by
      apply sub_pos.mpr; exact_mod_cast (show 1<maxPeak S by omega)) (leadingValue_pos S hS hne)).trans_le
      (grow_after_peak S hS hne)
    have ht := tail_mono S hS (a:=maxPeak S+1) (b:=n) (by simp) (by simpa using hn.le) hn
    push_cast at ht
    exact hfirst.trans_le ht
  · have he := not_nonempty_iff_eq_empty.mp hne
    simp [he, peakPolynomial_empty]

theorem normalizedValue_real (c : ℕ) (A : Finset ℕ) (s : ℝ) :
    normalizedValue c A s = (((peakPolynomial A).eval ((c:ℝ)+s) / realRising (s+1) c : ℝ):ℂ) := by
  rw [normalizedValue]
  have h1 : (c:ℂ)+(s:ℂ) = (((c:ℝ)+s:ℝ):ℂ) := by simp
  have h2 : (s:ℂ)+1 = ((s+1:ℝ):ℂ) := by simp
  rw [h1, h2, peakValue_real, realRising_cast, Complex.ofReal_div]

theorem normalizedValue_pos (c : ℕ) (A : Finset ℕ) (hA : Admissible A) (j : ℕ)
    (hj : maxPeak A<c+j) : 0 < (normalizedValue c A j).re := by
  have he := normalizedValue_real c A (j:ℝ)
  rw [Complex.ofReal_natCast] at he
  rw [he, Complex.ofReal_re]
  have hp := peak_after_pos A hA hj
  push_cast at hp
  exact div_pos hp (realRising_pos (by positivity) c)

end BilleyFahrbachTalmageClassification
