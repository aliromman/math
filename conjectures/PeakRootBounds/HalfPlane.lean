module

public import conjectures.PeakRootBounds.Gap
public import conjectures.PeakRootBounds.PeakValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The lower bound for the real parts of peak-polynomial roots -/

@[expose] public section
namespace PeakRootBounds
open PermutationPeaks PeakPolynomials ReflectedNewton Polynomial Finset

private theorem admissible_empty' : Admissible ∅ := by simp [Admissible]

theorem singleton_value (z : ℂ) (k : ℕ) :
    peakValue {k + 1} z = Ring.choose (z - 1) k - 1 := by
  induction k with
  | zero =>
    have hbad : ¬Admissible {1} := by intro h; have := h.1 1 (by simp); omega
    simp [peakValue, peakPolynomial_inadmissible _ hbad]
  | succ k ih =>
    have hrec := extension_recurrence ∅ admissible_empty' z (k+1) (by simp [maxPeak]) (by omega)
    have hpas := Ring.choose_succ_succ (z-1) k
    rw [sub_add_cancel] at hpas
    simp only [insert_empty_eq, peakPolynomial_empty, eval_one, Complex.ofReal_one, one_mul] at hrec
    rw [hrec, ih, hpas]
    simp [peakValue, peakPolynomial_empty]
    ring

private theorem one_le_scale (z : ℂ) (w : ℕ → ℝ) (hw : w 0 = 1) (h : Monotone (scale z w)) (j : ℕ) :
    1 ≤ scale z w j := by
  simpa [scale, hw] using h (Nat.zero_le j)

private theorem shifted_choose_unshifted_bound {z : ℂ} (hz : z.re < -3) (d : ℕ) :
    ‖Ring.choose (z-1) d‖ ≤ wWeight d * scale z dWeight d := by
  induction d with
  | zero => norm_num [scale, wWeight, dWeight, Nat.choose]
  | succ d ih =>
    have hpas := Ring.choose_succ_succ (z-1) d
    rw [sub_add_cancel] at hpas
    have hpas' : Ring.choose (z-1) (d+1) = Ring.choose z (d+1) - Ring.choose (z-1) d := by
      rw [hpas]; ring
    rw [hpas', wWeight_step]
    have hmon := mul_le_mul_of_nonneg_left ((unshifted_scale_mono hz).monotone (Nat.le_succ d)) (wWeight_nonneg d)
    have hlead := weight_scale z dWeight (dWeight_pos (d+1))
    linarith [norm_sub_le (Ring.choose z (d+1)) (Ring.choose (z-1) d)]

private theorem singleton_half_plane {z : ℂ} (hz : z.re < -3) {a : ℕ} (ha : 2 ≤ a) :
    PeakBounds z a 1 (peakValue {a} z) ∧ peakValue {a} z ≠ 0 := by
  have hp : peakValue {a} z = Ring.choose (z-1) (a-1) - 1 := by
    simpa only [show a-1+1=a by omega] using singleton_value z (a-1)
  have hd (j : ℕ) := one_le_scale z dWeight (by norm_num [dWeight, Nat.choose]) (unshifted_scale_mono hz).monotone j
  have hw (j : ℕ) := one_le_scale (z-1) wWeight (by norm_num [wWeight, Nat.choose]) (shifted_scale_mono hz).monotone j
  have wh (j : ℕ) : 1 ≤ wWeight j := by
    simpa [wWeight, Nat.choose] using wWeight_mono (Nat.zero_le j)
  constructor
  · constructor
    · rw [hp, mul_one]
      have hh := shifted_choose_unshifted_bound hz (a-1)
      have ht := norm_sub_le (Ring.choose (z-1) (a-1)) 1
      rw [norm_one] at ht
      linarith [hd (a-1)]
    · rw [hp]; simp only [Complex.ofReal_one, one_mul, sub_sub_cancel_left, norm_neg, norm_one, mul_one]
      split_ifs with h
      · simpa using hw (a-2)
      · have hh : 1 ≤ 2 * wWeight (a-1) := by linarith [wh (a-1)]
        simpa only [one_mul] using mul_le_mul hh (hw (a-2)) (by norm_num) (by linarith : 0 ≤ 2 * wWeight (a-1))
  · intro hzero
    have he := sub_eq_zero.mp (hp.symm.trans hzero)
    have hstrict := (shifted_scale_mono hz) (show 0<a-1 by omega)
    have hlow : 1 < scale (z-1) wWeight (a-1) := by
      simpa [scale, wWeight, Nat.choose] using hstrict
    have hsc := weight_scale (z-1) wWeight (wWeight_pos (a-1))
    rw [he, norm_one] at hsc
    have hh := mul_lt_mul_of_pos_left hlow (wWeight_pos (a-1))
    linarith [wh (a-1)]

private theorem peak_half_plane_bounds (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {z : ℂ} (hz : z.re < -3) :
    PeakBounds z (maxPeak S) (leadingValue S) (peakValue S z) ∧ peakValue S z ≠ 0 := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    let m := maxPeak S
    let T := S.erase m
    obtain ⟨hm, hT, hall, him, _⟩ := last_peak_reduction hS hne
    change insert m T = S at him
    by_cases hneT : T.Nonempty
    · let a := maxPeak T
      have ha := (last_peak_reduction hT hneT).1
      have hgap : a + 2 ≤ m := by have := (hall a (maxPeak_mem hneT)).2; change a < m-1 at this; omega
      have hpT : T ⊂ S := Finset.erase_ssubset (maxPeak_mem hne)
      have hold := (ih T hpT hT hneT).1
      have hstep := gap_bounds_and_ne_zero (a := a) (m := m) (f := fun n => (peakPolynomial T).eval (n:ℝ))
        (Q := fun n => peakValue (insert n T) z) hz ha hgap (leadingValue_pos T hT hneT)
        (peakPolynomial_root T hT hneT) (tail_mono T hT)
        (by simpa using grow_after_peak T hT hneT) hold (adjacent_extension_zero T hneT z)
        (fun n hn => extension_recurrence T hT z n hn (by omega))
      have he := extension_leading T hT (m-1) (by change a+1≤m-1; omega) (by omega)
      rw [show m-1+1=m by omega, him] at he
      simpa only [him, ← he] using hstep
    · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneT
      have hs : {m} = S := by simpa only [hTempty, insert_empty_eq] using him
      have he := extension_leading ∅ admissible_empty' (m-1) (by simp [maxPeak]; omega) (by omega)
      simp only [show m-1+1=m by omega, insert_empty_eq, peakPolynomial_empty, eval_one] at he
      rw [hs] at he
      have hbase : PeakBounds z m 1 (peakValue {m} z) ∧ peakValue {m} z ≠ 0 := singleton_half_plane hz hm
      rw [hs, ← he] at hbase
      exact hbase

/-- Every root of the permutation peak polynomial has real part at least `-3`. -/
theorem peak_half_plane (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {z : ℂ} (hz : z.re < -3) : peakValue S z ≠ 0 := (peak_half_plane_bounds S hS hne hz).2

end PeakRootBounds
