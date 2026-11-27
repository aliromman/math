module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Alternating sums for one gap in a peak set -/

@[expose] public section
namespace PeakRootBounds

/-- The constant in the recurrence occurs at alternate indices. -/
theorem gap_sum_norm {a r : ℕ} (har : a ≤ r) (P : ℂ) (T g : ℕ → ℂ)
    (h0 : T a = 0) (hrec : ∀ j, a ≤ j → T (j + 1) = g j - 2 * P - T j) :
    ‖T r‖ ≤ (if Even (r - a) then 0 else 2 * ‖P‖) + ∑ j ∈ Finset.Ico a r, ‖g j‖ := by
  have h : ‖T r + (if Even (r - a) then 0 else 2 * P)‖ ≤ ∑ j ∈ Finset.Ico a r, ‖g j‖ := by
    induction r, har using Nat.le_induction with
    | base => simp [h0]
    | succ r hr ih =>
      have hsub : r + 1 - a = (r - a) + 1 := by omega
      simp only [hsub, Nat.even_add_one, hrec r hr, Finset.sum_Ico_succ_top hr]
      by_cases he : Even (r - a)
      · simp [he] at ih ⊢
        calc
          _ = ‖g r - T r‖ := by congr 1; ring
          _ ≤ _ := by linarith [norm_sub_le (g r) (T r)]
      · simp [he] at ih ⊢
        calc
          _ = ‖g r - (T r + 2 * P)‖ := by congr 1; ring
          _ ≤ _ := by linarith [norm_sub_le (g r) (T r + 2 * P)]
  split_ifs at h ⊢ with he
  · simpa using h
  · have ht := norm_sub_le (T r + 2 * P) (2 * P)
    simp only [add_sub_cancel_right, norm_mul, Complex.norm_ofNat] at ht
    linarith

/-- Subtracting the shifted leading term replaces the suffix values by first differences. -/
theorem shifted_gap_recurrence {a : ℕ} (z P : ℂ) (f : ℕ → ℝ) (Q : ℕ → ℂ)
    (hrec : ∀ n, a + 1 ≤ n → Q (n + 1) = (f n : ℂ) * Ring.choose z n - 2 * P - Q n)
    (j : ℕ) (hj : a ≤ j) :
    Q (j + 1 + 1) - (f (j + 1) : ℂ) * Ring.choose (z - 1) (j + 1) =
      ((f (j + 1) - f j : ℝ) : ℂ) * Ring.choose (z - 1) j - 2 * P -
        (Q (j + 1) - (f j : ℂ) * Ring.choose (z - 1) j) := by
  have hpas := Ring.choose_succ_succ (z - 1) j
  rw [sub_add_cancel] at hpas
  rw [hrec (j + 1) (by omega), hpas, Complex.ofReal_sub]
  ring

end PeakRootBounds
