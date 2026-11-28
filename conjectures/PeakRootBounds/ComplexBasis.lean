module

public import conjectures.PeakRootBounds.Estimates
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Norm estimates for the binomial basis on the left of the line `Re z = -3`. -/

@[expose] public section
namespace PeakRootBounds

noncomputable def scale (z : ℂ) (w : ℕ → ℝ) (i : ℕ) : ℝ := ‖Ring.choose z i‖ / w i

theorem choose_step_mul (z : ℂ) (j : ℕ) :
    (j + 1 : ℂ) * Ring.choose z (j+1) = Ring.choose z j * (z-j) := by
  simpa [Nat.choose_succ_self_right, nsmul_eq_mul] using
    (Ring.choose_smul_choose z (Nat.le_succ j))

theorem choose_norm_step (z : ℂ) (j : ℕ) :
    (j + 1 : ℝ) * ‖Ring.choose z (j+1)‖ = ‖Ring.choose z j‖ * ‖z-j‖ := by
  have h := congrArg norm (choose_step_mul z j)
  rw [norm_mul, norm_mul, ← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ] at h
  exact h

theorem scale_mono_of_factors (z : ℂ) (w : ℕ → ℝ) (s : ℝ)
    (hw : ∀ j, 0 < w j) (hs : 0 < s)
    (step : ∀ j : ℕ, w (j+1) * (j+1 : ℝ) = w j * (s + j))
    (bound : ∀ j : ℕ, s + j < ‖z-j‖) : StrictMono (scale z w) := by
  have hp (j : ℕ) : 0 < ‖Ring.choose z j‖ := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := choose_norm_step z j
      have hfac : 0 < ‖z-j‖ := (by positivity : 0 < s+(j:ℝ)).trans (bound j)
      exact pos_of_mul_pos_right (h.symm ▸ mul_pos ih hfac) (by positivity)
  apply strictMono_nat_of_lt_succ
  intro j
  rw [scale, scale, div_lt_div_iff₀ (hw j) (hw (j+1))]
  apply lt_of_mul_lt_mul_right (a := (j:ℝ)+1) _ (by positivity)
  calc
    ‖Ring.choose z j‖ * w (j+1) * (j+1 : ℝ) = ‖Ring.choose z j‖ * (w j * (s+j)) := by rw [mul_assoc, step]
    _ < ‖Ring.choose z j‖ * (w j * ‖z-j‖) := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (bound j) (hw j)) (hp j)
    _ = ‖Ring.choose z (j+1)‖ * w j * (j+1 : ℝ) := by linarith only [congrArg (· * w j) (choose_norm_step z j)]

theorem dWeight_pos (j : ℕ) : 0 < dWeight j := by rw [dWeight_formula]; positivity

theorem wWeight_pos (j : ℕ) : 0 < wWeight j := by rw [wWeight_formula]; positivity

theorem left_factor (z : ℂ) {s : ℝ} (hz : z.re < -s) (j : ℕ) : s + j < ‖z-j‖ := by
  have h := Complex.re_le_norm ((j : ℂ)-z)
  rw [norm_sub_rev, Complex.sub_re, Complex.natCast_re] at h
  linarith

theorem unshifted_scale_mono {z : ℂ} (hz : z.re < -3) : StrictMono (scale z dWeight) := by
  apply scale_mono_of_factors z dWeight 3 dWeight_pos (by norm_num) _ (left_factor z hz)
  intro j
  rw [dWeight_formula, dWeight_formula]; push_cast; ring

theorem shifted_scale_mono {z : ℂ} (hz : z.re < -3) : StrictMono (scale (z-1) wWeight) := by
  have hz' : (z-1).re < -(4 : ℝ) := by simp only [Complex.sub_re, Complex.one_re]; linarith
  apply scale_mono_of_factors (z-1) wWeight 4 wWeight_pos (by norm_num) _ (left_factor _ hz')
  intro j
  rw [wWeight_formula, wWeight_formula]; push_cast; ring

theorem weight_scale (z : ℂ) (w : ℕ → ℝ) {i : ℕ} (hw : 0 < w i) :
    w i * scale z w i = ‖Ring.choose z i‖ := by
  simp [scale, mul_div_cancel₀, hw.ne']

end PeakRootBounds
