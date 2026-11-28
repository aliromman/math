module

public import conjectures.PeakRootBounds.ComplexBasis
public import conjectures.PeakRootBounds.GapRecurrence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Propagation of the zero-free half-plane across a peak gap -/

@[expose] public section
namespace PeakRootBounds

/-- Bounds for a peak polynomial, first in the ordinary basis and then with the shifted leading term removed. -/
structure PeakBounds (z : ℂ) (a : ℕ) (M : ℝ) (P : ℂ) : Prop where
  unshifted : ‖P‖ ≤ (wWeight (a - 1) + 1) * M * scale z dWeight (a - 1)
  shifted : ‖P - (M : ℂ) * Ring.choose (z - 1) (a - 1)‖ ≤
    (if a = 2 then M else 2 * wWeight (a - 1) * M) * scale (z - 1) wWeight (a - 2)

private theorem scale_nonneg' (z : ℂ) {w : ℕ → ℝ} (hw : ∀ j, 0 < w j) (i : ℕ) :
    0 ≤ scale z w i := div_nonneg (norm_nonneg _) (hw i).le

private theorem norm_real_choose (z : ℂ) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    ‖(t : ℂ) * Ring.choose z j‖ = t * ‖Ring.choose z j‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]

private theorem suffix_norm_le (z : ℂ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hm : Monotone (scale z w)) (s : Finset ℕ) (idx : ℕ → ℕ) (f : ℕ → ℝ) (k : ℕ)
    (hi : ∀ j ∈ s, idx j ≤ k) (hf : ∀ j ∈ s, 0 ≤ f j) :
    (∑ j ∈ s, ‖(f j : ℂ) * Ring.choose z (idx j)‖) ≤
      (∑ j ∈ s, w (idx j) * f j) * scale z w k := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_real_choose z (hf j hj), ← weight_scale z w (hw _)]
  calc
    _ = (w (idx j) * f j) * scale z w (idx j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hm (hi j hj)) (mul_nonneg (hw _).le (hf j hj))

private theorem shifted_previous {a : ℕ} {z P : ℂ} {M : ℝ} (hz : z.re < -3) (hM : 0 ≤ M)
    (h : PeakBounds z a M P) :
    ‖P‖ ≤ ((if a = 2 then M else 2 * wWeight (a - 1) * M) + wWeight (a - 1) * M) *
      scale (z - 1) wWeight (a - 1) := by
  let V := if a = 2 then M else 2 * wWeight (a - 1) * M
  have hV : 0 ≤ V := by dsimp [V]; split_ifs <;> positivity [wWeight_nonneg (a - 1)]
  have hh := mul_le_mul_of_nonneg_left ((shifted_scale_mono hz).monotone (show a - 2 ≤ a - 1 by omega)) hV
  have ht := norm_add_le (P - (M : ℂ) * Ring.choose (z-1) (a-1)) ((M : ℂ) * Ring.choose (z-1) (a-1))
  rw [sub_add_cancel, norm_real_choose _ hM, ← weight_scale _ _ (wWeight_pos _)] at ht
  change ‖P‖ ≤ (V + wWeight (a - 1) * M) * _
  have hs : ‖P - (M : ℂ) * Ring.choose (z-1) (a-1)‖ ≤ V * scale (z-1) wWeight (a-2) := h.shifted
  linarith

private theorem strict_leading {z : ℂ} {w : ℕ → ℝ} (hw : ∀ j, 0 < w j)
    (hmono : StrictMono (scale z w)) {i j : ℕ} (hij : i < j) {A : ℝ} (hA : 0 < A) :
    w j * A * scale z w i < ‖(A : ℂ) * Ring.choose z j‖ := by
  rw [norm_real_choose _ hA.le, ← weight_scale _ _ (hw j)]
  calc
    _ < w j * A * scale z w j := mul_lt_mul_of_pos_left (hmono hij) (mul_pos (hw j) hA)
    _ = _ := by ring

private theorem gap_at_successor {a r : ℕ} {z P : ℂ} {M : ℝ} {f : ℕ → ℝ} {Q : ℕ → ℂ}
    (hz : z.re < -3) (ha : 2 ≤ a) (hr : a + 1 ≤ r) (hM : 0 < M) (hf0 : f a = 0)
    (hf : MonotoneOn f (Set.Ici a)) (hg : ((a : ℝ) - 1) * M ≤ f (a + 1))
    (hP : PeakBounds z a M P) (hQ0 : Q (a + 1) = 0)
    (hrec : ∀ n, a + 1 ≤ n → Q (n + 1) = (f n : ℂ) * Ring.choose z n - 2 * P - Q n) :
    PeakBounds z (r + 1) (f r) (Q (r + 1)) ∧ Q (r + 1) ≠ 0 := by
  let U := (wWeight (a - 1) + 1) * M
  let V := if a = 2 then M else 2 * wWeight (a - 1) * M
  let E := Q (r + 1) - (f r : ℂ) * Ring.choose (z - 1) r
  let su := ∑ j ∈ Finset.Ico a r, dWeight (j + 1) * f (j + 1)
  let sv := ∑ j ∈ Finset.Ico a r, wWeight j * (f (j + 1) - f j)
  let du := scale z dWeight r
  let dv := scale (z - 1) wWeight (r - 1)
  have har : a ≤ r := by omega
  have hf' {i j : ℕ} (hi : a ≤ i) (hj : i ≤ j) : f i ≤ f j :=
    hf (by simpa using hi) (by simpa using hi.trans hj) hj
  have hfpos {i : ℕ} (hi : a ≤ i) : 0 ≤ f i := hf0 ▸ hf' (Nat.le_refl _) hi
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hfr : 0 < f r := (mul_pos (by linarith : 0 < (a : ℝ) - 1) hM).trans_le (hg.trans (hf' (by omega) hr))
  have hg' := hg.trans (hf' (by omega) hr)
  have hdu : 0 ≤ du := scale_nonneg' z dWeight_pos _
  have hdv : 0 ≤ dv := scale_nonneg' _ wWeight_pos _
  have hU : 0 ≤ U := mul_nonneg (by linarith [wWeight_nonneg (a-1)]) hM.le
  have hV : 0 ≤ V := by dsimp [V]; split_ifs <;> positivity [wWeight_nonneg (a - 1)]
  have hVup : V ≤ 2 * wWeight (a - 1) * M := by
    dsimp [V]; split_ifs with h
    · subst a; norm_num [wWeight, Nat.choose]; linarith
    · exact le_rfl
  have hV2 (h : a = 2) : V ≤ M := by simp [V, h]
  have hu0 := gap_sum_norm har P (fun j => Q (j+1)) (fun j => (f (j+1) : ℂ) * Ring.choose z (j+1))
    hQ0 (fun j hj => hrec (j+1) (by omega))
  have hv0 := gap_sum_norm har P (fun j => Q (j+1) - (f j : ℂ) * Ring.choose (z-1) j)
    (fun j => ((f (j+1) - f j : ℝ) : ℂ) * Ring.choose (z-1) j)
    (by simp [hQ0, hf0]) (shifted_gap_recurrence z P f Q hrec)
  have hsu := suffix_norm_le z dWeight dWeight_pos (unshifted_scale_mono hz).monotone
    (Finset.Ico a r) (fun j => j+1) (fun j => f (j+1)) r
    (fun j hj => by have := (Finset.mem_Ico.mp hj).2; omega)
    (fun j hj => hfpos (by have := (Finset.mem_Ico.mp hj).1; omega))
  have hsv := suffix_norm_le (z-1) wWeight wWeight_pos (shifted_scale_mono hz).monotone
    (Finset.Ico a r) id (fun j => f (j+1) - f j) (r-1)
    (fun j hj => by change j ≤ _; have := (Finset.mem_Ico.mp hj).2; omega)
    (fun j hj => sub_nonneg.mpr (hf' (Finset.mem_Ico.mp hj).1 (by omega)))
  have hu1 : ‖Q (r+1)‖ ≤ 2 * ‖P‖ + su * du := by
    exact hu0.trans (add_le_add (by split_ifs <;> first | exact le_rfl | positivity) hsu)
  have hv1 : ‖E‖ ≤ (if Even (r-a) then 0 else 2 * ‖P‖) + sv * dv := hv0.trans (add_le_add le_rfl hsv)
  have hpd : ‖P‖ ≤ U * du := hP.unshifted.trans (mul_le_mul_of_nonneg_left
    ((unshifted_scale_mono hz).monotone (by omega)) hU)
  have hpw : ‖P‖ ≤ (V + wWeight (a-1)*M) * dv := (shifted_previous hz hM.le hP).trans
    (mul_le_mul_of_nonneg_left ((shifted_scale_mono hz).monotone (by omega))
      (add_nonneg hV (mul_nonneg (wWeight_nonneg _) hM.le)))
  have hQU : ‖Q (r+1)‖ ≤ (2 * U + su) * du := by linarith
  have hEV : ‖E‖ ≤ (2 * (V + wWeight (a-1)*M) + sv) * dv := by
    by_cases he : Even (r-a) <;> simp [he] at hv1 <;> linarith [norm_nonneg P]
  have hus : su ≤ (wWeight r - wWeight a) * f r := unshifted_suffix_le f har hf
  have hvs : sv ≤ wWeight (r-1) * f r := by simpa [sv, hf0] using shifted_suffix_le f har hf
  constructor
  · constructor
    · simp only [Nat.add_sub_cancel]
      apply hQU.trans (mul_le_mul_of_nonneg_right _ hdu)
      have h := u_prefix_le ha hM.le hg' (le_refl U)
      linarith
    · have hne : r+1 ≠ 2 := by omega
      simp only [hne, ite_false, Nat.add_sub_cancel, show r+1-2=r-1 by omega]
      apply hEV.trans (mul_le_mul_of_nonneg_right _ hdv)
      have hv := v_prefix_le ha (a := r+1) (by omega) hM.le hg' hVup hV2
      simp only [Nat.add_sub_cancel] at hv
      have hw := mul_le_mul_of_nonneg_right (wWeight_mono (show r-1≤r by omega)) hfr.le
      linarith
  · by_cases hshort : r = a + 1
    · subst r
      intro hzq
      have hc := hrec (a+1) (by omega)
      rw [hzq, hQ0, sub_zero] at hc
      have hn := congrArg norm (sub_eq_zero.mp hc.symm)
      rw [norm_mul (2 : ℂ) P, Complex.norm_ofNat] at hn
      have hu := gap_two_le ha hM.le hg (le_refl U)
      have hbound := mul_le_mul_of_nonneg_right hu (scale_nonneg' z dWeight_pos (a-1))
      have hstrict := strict_leading dWeight_pos (unshifted_scale_mono hz) (show a-1<a+1 by omega) hfr
      linarith [hP.unshifted]
    · have hsum : ‖E‖ ≤ wWeight r * f r * dv := by
        by_cases he : Even (r - a)
        · simp only [he, ite_true, zero_add] at hv1
          apply hv1.trans (mul_le_mul_of_nonneg_right _ hdv)
          exact hvs.trans (mul_le_mul_of_nonneg_right (wWeight_mono (by omega)) hfr.le)
        · have hlong : a + 3 ≤ r := by
            by_contra! h
            have heq : r-a=2 := by omega
            exact he (heq ▸ even_two)
          have ht := three_suffix_terms f hlong hf (hfpos (by omega))
          have hab := weighted_differences f har
          rw [hf0, mul_zero, sub_zero] at hab
          change sv + su = _ at hab
          change _ ≤ su at ht
          have hfour := gap_four_le ha hM.le hg hVup
          apply hEV.trans (mul_le_mul_of_nonneg_right _ hdv)
          linarith
      have ht := strict_leading wWeight_pos (shifted_scale_mono hz) (show r-1<r by omega) hfr
      intro hzero
      simp only [E, hzero, zero_sub, norm_neg] at hsum
      exact (not_lt_of_ge hsum) ht

/-- Extend the bounds across any gap of at least two positions. -/
theorem gap_bounds_and_ne_zero {a m : ℕ} {z P : ℂ} {M : ℝ} {f : ℕ → ℝ} {Q : ℕ → ℂ}
    (hz : z.re < -3) (ha : 2 ≤ a) (hm : a + 2 ≤ m) (hM : 0 < M) (hf0 : f a = 0)
    (hf : MonotoneOn f (Set.Ici a)) (hg : ((a : ℝ) - 1) * M ≤ f (a + 1))
    (hP : PeakBounds z a M P) (hQ0 : Q (a + 1) = 0)
    (hrec : ∀ n, a + 1 ≤ n → Q (n + 1) = (f n : ℂ) * Ring.choose z n - 2 * P - Q n) :
    PeakBounds z m (f (m - 1)) (Q m) ∧ Q m ≠ 0 := by
  have h := gap_at_successor (r := m-1) hz ha (by omega) hM hf0 hf hg hP hQ0 hrec
  simpa only [show m-1+1=m by omega] using h

end PeakRootBounds
