module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Weight estimates for the left half-plane

The two weights are the absolute values of the binomial basis at `-3` and `-4`.
-/

@[expose] public section

namespace PeakRootBounds

/-- The absolute value of the degree `j` binomial basis polynomial at `-3`. -/
def dWeight (j : ℕ) : ℝ := (j + 2).choose 2

/-- The absolute value of the degree `j` binomial basis polynomial at `-4`. -/
def wWeight (j : ℕ) : ℝ := (j + 3).choose 3

theorem dWeight_nonneg (j : ℕ) : 0 ≤ dWeight j := Nat.cast_nonneg _

theorem wWeight_nonneg (j : ℕ) : 0 ≤ wWeight j := Nat.cast_nonneg _

theorem wWeight_step (j : ℕ) : wWeight (j + 1) = wWeight j + dWeight (j + 1) := by
  unfold wWeight dWeight
  rw [Nat.choose_succ_succ (j + 3) 2, Nat.cast_add]
  ring

theorem sum_dWeight (j : ℕ) : ∑ k ∈ Finset.range (j + 1), dWeight k = wWeight j := by
  induction j with
  | zero => norm_num [dWeight, wWeight, Nat.choose]
  | succ j ih => rw [Finset.sum_range_succ, ih, wWeight_step]

theorem wWeight_mono : Monotone wWeight := by
  apply monotone_nat_of_le_succ
  intro j
  linarith [wWeight_step j, dWeight_nonneg (j + 1)]

theorem dWeight_formula (j : ℕ) : dWeight j = (j + 1 : ℝ) * (j + 2) / 2 := by
  unfold dWeight
  rw [Nat.cast_choose_two]
  push_cast
  ring

theorem wWeight_formula (j : ℕ) : wWeight j = (j + 1 : ℝ) * (j + 2) * (j + 3) / 6 := by
  induction j with
  | zero => norm_num [wWeight, Nat.choose]
  | succ j ih => rw [wWeight_step, ih, dWeight_formula]; push_cast; ring

theorem dWeight_mono : Monotone dWeight := by
  apply monotone_nat_of_le_succ
  intro j
  rw [dWeight_formula, dWeight_formula]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

/-- Summation by parts for a suffix of coefficients. -/
theorem weighted_differences (p : ℕ → ℝ) {a r : ℕ} (h : a ≤ r) :
    (∑ j ∈ Finset.Ico a r, wWeight j * (p (j + 1) - p j)) +
        ∑ j ∈ Finset.Ico a r, dWeight (j + 1) * p (j + 1) =
      wWeight r * p r - wWeight a * p a := by
  induction r, h using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    rw [Finset.sum_Ico_succ_top hr, Finset.sum_Ico_succ_top hr, wWeight_step]
    linarith

/-- If three indices remain, their unshifted terms give a lower bound for the whole suffix. -/
theorem three_suffix_terms (p : ℕ → ℝ) {a r : ℕ} (hr : a + 3 ≤ r)
    (hp : MonotoneOn p (Set.Ici a)) (h0 : 0 ≤ p (a + 1)) :
    3 * dWeight (a + 1) * p (a + 1) ≤ ∑ j ∈ Finset.Ico a r, dWeight (j + 1) * p (j + 1) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico a r) :
      dWeight (a + 1) * p (a + 1) ≤ dWeight (j + 1) * p (j + 1) := by
    have haj := (Finset.mem_Ico.mp hj).1
    exact mul_le_mul (dWeight_mono (by omega))
      (hp (by simp) (by simpa using (show a ≤ j + 1 by omega)) (by omega))
      h0 (dWeight_nonneg _)
  have hn : (3 : ℝ) ≤ ↑(r - a) := by exact_mod_cast (show 3 ≤ r - a by omega)
  have hc := Finset.sum_le_sum hterm
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hc
  calc
    3 * dWeight (a + 1) * p (a + 1) = 3 * (dWeight (a + 1) * p (a + 1)) := mul_assoc _ _ _
    _ ≤ ↑(r - a) * (dWeight (a + 1) * p (a + 1)) :=
      mul_le_mul_of_nonneg_right hn (mul_nonneg (dWeight_nonneg _) h0)
    _ ≤ _ := hc

/-- The unshifted sum is at most the last value times the sum of its weights. -/
theorem unshifted_suffix_le (p : ℕ → ℝ) {a r : ℕ} (hr : a ≤ r)
    (hp : MonotoneOn p (Set.Ici a)) :
    (∑ j ∈ Finset.Ico a r, dWeight (j + 1) * p (j + 1)) ≤ (wWeight r - wWeight a) * p r := by
  have hw := weighted_differences (fun _ => (1 : ℝ)) hr
  simp at hw
  calc
    _ ≤ ∑ j ∈ Finset.Ico a r, dWeight (j + 1) * p r := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨ha, hjr⟩ := Finset.mem_Ico.mp hj
      exact mul_le_mul_of_nonneg_left (hp (by simpa using (show a ≤ j + 1 by omega))
        (by simpa using hr) (by omega)) (dWeight_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, hw]

/-- The difference sum is at most its largest weight times the total increase. -/
theorem shifted_suffix_le (p : ℕ → ℝ) {a r : ℕ} (hr : a ≤ r)
    (hp : MonotoneOn p (Set.Ici a)) :
    (∑ j ∈ Finset.Ico a r, wWeight j * (p (j + 1) - p j)) ≤ wWeight (r - 1) * (p r - p a) := by
  have hsum : (∑ j ∈ Finset.Ico a r, (p (j + 1) - p j)) = p r - p a := by
    induction r, hr using Nat.le_induction with
    | base => simp
    | succ r har ih => rw [Finset.sum_Ico_succ_top har, ih]; ring
  calc
    _ ≤ ∑ j ∈ Finset.Ico a r, wWeight (r - 1) * (p (j + 1) - p j) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨ha, hjr⟩ := Finset.mem_Ico.mp hj
      exact mul_le_mul_of_nonneg_right (wWeight_mono (by omega)) (sub_nonneg.mpr
        (hp (by simpa using ha) (by simpa using (show a ≤ j + 1 by omega)) (by omega)))
    _ = _ := by rw [← Finset.mul_sum, hsum]

private theorem u_factor {b : ℕ} (hb : 2 ≤ b) :
    2 * (wWeight (b - 1) + 1) ≤ wWeight b * ((b : ℝ) - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [show 2 + n - 1 = n + 1 by omega]
  simp only [wWeight_formula, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem gap_two_factor {b : ℕ} (hb : 2 ≤ b) :
    2 * (wWeight (b - 1) + 1) ≤ dWeight (b + 1) * ((b : ℝ) - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [show 2 + n - 1 = n + 1 by omega]
  simp only [dWeight_formula, wWeight_formula, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem v_factor {b : ℕ} (hb : 3 ≤ b) :
    6 * wWeight (b - 1) ≤ wWeight (b + 1) * ((b : ℝ) - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [show 3 + n - 1 = n + 2 by omega]
  simp only [wWeight_formula, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- The omitted lower weights cover the unshifted contribution from the previous peak set. -/
theorem u_prefix_le {b : ℕ} (hb : 2 ≤ b) {U B A : ℝ} (hB : 0 ≤ B)
    (hg : ((b : ℝ) - 1) * B ≤ A) (hU : U ≤ (wWeight (b - 1) + 1) * B) :
    2 * U ≤ wWeight b * A := by
  calc
    2 * U ≤ (2 * (wWeight (b - 1) + 1)) * B := by linarith
    _ ≤ (wWeight b * ((b : ℝ) - 1)) * B := mul_le_mul_of_nonneg_right (u_factor hb) hB
    _ ≤ wWeight b * A := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hg (wWeight_nonneg _)

/-- The shifted contribution from the previous peak set fits below the new leading weight. -/
theorem v_prefix_le {b a : ℕ} (hb : 2 ≤ b) (ha : b + 2 ≤ a) {V B A : ℝ}
    (hB : 0 ≤ B) (hg : ((b : ℝ) - 1) * B ≤ A) (hV : V ≤ 2 * wWeight (b - 1) * B)
    (h2 : b = 2 → V ≤ B) : 2 * (V + wWeight (b - 1) * B) ≤ wWeight (a - 1) * A := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hA : 0 ≤ A := (mul_nonneg (by linarith) hB).trans hg
  suffices h : 2 * (V + wWeight (b - 1) * B) ≤ wWeight (b + 1) * A by
    exact h.trans (mul_le_mul_of_nonneg_right (wWeight_mono (by omega)) hA)
  by_cases hs : b = 2
  · subst b
    norm_num [wWeight, Nat.choose] at hg ⊢
    linarith [h2 rfl]
  · calc
      2 * (V + wWeight (b - 1) * B) ≤ (6 * wWeight (b - 1)) * B := by linarith
      _ ≤ (wWeight (b + 1) * ((b : ℝ) - 1)) * B :=
        mul_le_mul_of_nonneg_right (v_factor (by omega)) hB
      _ ≤ wWeight (b + 1) * A := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hg (wWeight_nonneg _)

/-- A gap of two contributes one leading term in the unshifted basis. -/
theorem gap_two_le {b : ℕ} (hb : 2 ≤ b) {U B A : ℝ} (hB : 0 ≤ B)
    (hg : ((b : ℝ) - 1) * B ≤ A) (hU : U ≤ (wWeight (b - 1) + 1) * B) :
    2 * U ≤ dWeight (b + 1) * A := by
  calc
    2 * U ≤ (2 * (wWeight (b - 1) + 1)) * B := by linarith
    _ ≤ (dWeight (b + 1) * ((b : ℝ) - 1)) * B := mul_le_mul_of_nonneg_right (gap_two_factor hb) hB
    _ ≤ dWeight (b + 1) * A := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hg (dWeight_nonneg _)

/-- Three terms in a gap of at least four cover the shifted contribution from the previous peak set. -/
theorem gap_four_le {b : ℕ} (hb : 2 ≤ b) {V B A : ℝ} (hB : 0 ≤ B)
    (hg : ((b : ℝ) - 1) * B ≤ A) (hV : V ≤ 2 * wWeight (b - 1) * B) :
    2 * (V + wWeight (b - 1) * B) ≤ 3 * dWeight (b + 1) * A := by
  have h := gap_two_le hb hB hg (le_refl ((wWeight (b - 1) + 1) * B))
  linarith

/-- Add the upper bound for the unshifted suffix to the bound for its prefix. -/
theorem u_step_le {b a : ℕ} (hb : 2 ≤ b) {U U' B A : ℝ} (hB : 0 ≤ B)
    (hg : ((b : ℝ) - 1) * B ≤ A) (hU : U ≤ (wWeight (b - 1) + 1) * B)
    (hsum : U' ≤ 2 * U + (wWeight (a - 1) - wWeight b) * A) :
    U' ≤ (wWeight (a - 1) + 1) * A := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hA : 0 ≤ A := (mul_nonneg (by linarith) hB).trans hg
  linarith [u_prefix_le hb hB hg hU]

/-- Add the upper bound for the shifted suffix to the bound for its prefix. -/
theorem v_step_le {b a : ℕ} (hb : 2 ≤ b) (ha : b + 2 ≤ a) {V V' B A : ℝ}
    (hB : 0 ≤ B) (hg : ((b : ℝ) - 1) * B ≤ A) (hV : V ≤ 2 * wWeight (b - 1) * B)
    (h2 : b = 2 → V ≤ B) (hsum : V' ≤ 2 * (V + wWeight (b - 1) * B) + wWeight (a - 2) * A) :
    V' ≤ 2 * wWeight (a - 1) * A := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hA : 0 ≤ A := (mul_nonneg (by linarith) hB).trans hg
  have hw := mul_le_mul_of_nonneg_right (wWeight_mono (show a - 2 ≤ a - 1 by omega)) hA
  linarith [v_prefix_le hb ha hB hg hV h2]

end PeakRootBounds
