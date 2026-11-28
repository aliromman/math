module

public import conjectures.PeakRootBounds.ComplexBasis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A reverse Newton expansion with one positive coefficient gives a disk bound. -/

@[expose] public section
namespace PeakRootBounds
open Finset

theorem rising_step (x : ℂ) (j : ℕ) :
    (j+1 : ℂ) * Ring.multichoose x (j+1) = (x+j) * Ring.multichoose x j := by
  have h := Ring.choose_smul_choose (x+j) (n := j+1) (k := 1) (by omega)
  simp only [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_add_one, Ring.choose_one_right,
    Nat.add_sub_cancel] at h
  rw [Ring.multichoose_eq, Ring.multichoose_eq]
  push_cast
  convert h using 2 <;> ring

theorem rising_scale_step {n j : ℕ} (hj : j ≤ n) {z : ℂ} (hz : (n:ℝ)+2 < ‖z‖)
    (hp : 0 < ‖Ring.multichoose (z-n) j‖) :
    ‖Ring.multichoose (z-n) j‖ / (j+1 : ℝ) <
      ‖Ring.multichoose (z-n) (j+1)‖ / (j+2 : ℝ) := by
  have ht : (j+2 : ℝ) < ‖z - n + j‖ := by
    have hn := norm_sub_norm_le z ((n-j : ℕ) : ℂ)
    rw [Complex.norm_natCast, Nat.cast_sub hj] at hn
    have hh : z-n+j = z-((n-j : ℕ) : ℂ) := by rw [Nat.cast_sub hj]; ring
    rw [hh]
    linarith
  have h := congrArg norm (rising_step (z-n) j)
  rw [norm_mul, norm_mul, ← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ] at h
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [h, mul_lt_mul_of_pos_right ht hp]

private theorem rising_scale_grows {n : ℕ} {z : ℂ} (hz : (n:ℝ)+2 < ‖z‖) :
    ∀ k ≤ n+1, 0 < ‖Ring.multichoose (z-n) k‖ ∧
      ∀ j < k, ‖Ring.multichoose (z-n) j‖ / (j+1 : ℝ) <
        ‖Ring.multichoose (z-n) k‖ / (k+1 : ℝ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    obtain ⟨hpos, hlt⟩ := ih (by omega)
    have h := rising_scale_step (by omega : k ≤ n) hz hpos
    have hn : (↑(k+1 : ℕ) + 1 : ℝ) = k+2 := by push_cast; ring
    rw [hn]
    constructor
    · exact (div_pos_iff_of_pos_right (by positivity)).mp ((div_pos hpos (by positivity)).trans h)
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj|rfl
      · exact (hlt j hj).trans h
      · exact h

theorem disk_nonzero {n : ℕ} {z : ℂ} (hz : (n:ℝ)+2 < ‖z‖) (b : ℕ → ℝ)
    (hneg : ∀ j ≤ n, b j ≤ 0) (hpos : 0 < b (n+1))
    (hzero : ∑ j ∈ range (n+2), b j * (j+1 : ℝ) = 0) :
    ∑ j ∈ range (n+2), (b j : ℂ) * Ring.multichoose (z-n) j ≠ 0 := by
  let s (j : ℕ) := ‖Ring.multichoose (z-n) j‖ / (j+1 : ℝ)
  have scale_eq (j : ℕ) : (j+1:ℝ)*s j = ‖Ring.multichoose (z-n) j‖ := by
    dsimp [s]; field_simp
  have hsn : s n < s (n+1) := (rising_scale_grows hz (n+1) le_rfl).2 n (by omega)
  have hle (j : ℕ) (hj : j ≤ n) : s j ≤ s n := by
    rcases hj.lt_or_eq with h|rfl
    · exact ((rising_scale_grows hz n (by omega)).2 j h).le
    · rfl
  have heq : ∑ j ∈ range (n+1), -b j * (j+1 : ℝ) = b (n+1) * (↑(n+1 : ℕ)+1) := by
    rw [sum_range_succ] at hzero
    simp_rw [neg_mul, sum_neg_distrib]
    linarith
  have hsmall : ‖∑ j ∈ range (n+1), (b j : ℂ) * Ring.multichoose (z-n) j‖ <
      ‖(b (n+1) : ℂ) * Ring.multichoose (z-n) (n+1)‖ := by
    calc
      _ ≤ ∑ j ∈ range (n+1), ‖(b j : ℂ) * Ring.multichoose (z-n) j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range (n+1), (-b j * (j+1 : ℝ)) * s n := by
        apply sum_le_sum
        intro j hj
        have h := hneg j (by simpa using hj)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos h, ← scale_eq j, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left (hle j (by simpa using hj)) (mul_nonneg (neg_nonneg.mpr h) (by positivity))
      _ = (b (n+1) * (↑(n+1 : ℕ)+1)) * s n := by rw [← sum_mul, heq]
      _ < (b (n+1) * (↑(n+1 : ℕ)+1)) * s (n+1) := mul_lt_mul_of_pos_left hsn (mul_pos hpos (by positivity))
      _ = _ := by rw [mul_assoc, scale_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  intro H
  rw [sum_range_succ, add_eq_zero_iff_eq_neg] at H
  rw [H, norm_neg] at hsmall
  exact lt_irrefl _ hsmall

end PeakRootBounds
