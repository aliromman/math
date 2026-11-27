module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace BekkOrder

open Finset

noncomputable def binWeight (n x : ℕ) (p : ℝ) : ℝ :=
  n.choose x * p ^ x * (1 - p) ^ (n - x)

noncomputable def avg (n : ℕ) (p : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ x ∈ range (n + 1), binWeight n x p * f x

theorem binWeight_pos {n x : ℕ} {p : ℝ} (hx : x ≤ n) (hp : 0 < p) (hp' : p < 1) :
    0 < binWeight n x p :=
  mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hx)) (pow_pos hp _))
    (pow_pos (sub_pos.mpr hp') _)

private theorem tilt {n x : ℕ} {p q a r : ℝ} (hx : x ≤ n)
    (hq : q = p * a * r) (ha : 1 - q = (1 - p) * a) :
    binWeight n x q = a ^ n * r ^ x * binWeight n x p := by
  unfold binWeight
  conv_lhs => rw [ha, hq]
  rw [show a ^ n = a ^ x * a ^ (n - x) by rw [← pow_add, Nat.add_sub_of_le hx]]
  simp only [mul_pow]
  ring

private theorem tilt_strict {r : ℝ} (hr : 1 < r) {x c : ℕ} (hne : x ≠ c) :
    0 < (r ^ x - r ^ c) * ((x : ℝ) - c) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr (pow_lt_pow_right₀ hr h))
      (sub_neg.mpr (Nat.cast_lt.mpr h))
  · exact mul_pos (sub_pos.mpr (pow_lt_pow_right₀ hr h)) (sub_pos.mpr (Nat.cast_lt.mpr h))

/-- A binomial average of a single-crossing function crosses zero at most once. -/
theorem avg_crossing {n c : ℕ} {p q : ℝ} {h : ℕ → ℝ}
    (hp : 0 < p) (hpq : p < q) (hq : q < 1)
    (h0 : ∀ x ≤ n, 0 ≤ h x) (hpos : ∃ x ≤ n, x ≠ c ∧ 0 < h x)
    (havg : 0 ≤ avg n p (fun x ↦ ((x : ℝ) - c) * h x)) :
    0 < avg n q (fun x ↦ ((x : ℝ) - c) * h x) := by
  let a := (1 - q) / (1 - p)
  let r := q / (p * a)
  have hp' := hpq.trans hq
  have ha : 0 < a := div_pos (sub_pos.mpr hq) (sub_pos.mpr hp')
  have ha' : a < 1 := (div_lt_one (sub_pos.mpr hp')).mpr (by linarith)
  have hr : 1 < r :=
    (one_lt_div (mul_pos hp ha)).mpr ((mul_lt_of_lt_one_right hp ha').trans hpq)
  have heq (x : ℕ) (hx : x ≤ n) : binWeight n x q = a ^ n * r ^ x * binWeight n x p :=
    tilt hx (by dsimp [r]; field_simp [ha.ne', hp.ne'])
      (by dsimp [a]; field_simp [(sub_pos.mpr hp').ne'])
  let gap (x : ℕ) := (a ^ n * binWeight n x p * h x) * ((r ^ x - r ^ c) * ((x : ℝ) - c))
  have hgap : 0 < ∑ x ∈ range (n + 1), gap x := by
    apply sum_pos'
    · intro x hx
      have hxn := Nat.le_of_lt_succ (mem_range.mp hx)
      by_cases hc : x = c
      · simp [gap, hc]
      exact (mul_nonneg (mul_nonneg (mul_nonneg (pow_pos ha _).le
        (binWeight_pos hxn hp hp').le) (h0 x hxn)) (tilt_strict hr hc).le)
    · obtain ⟨x, hx, hne, hx'⟩ := hpos
      exact ⟨x, mem_range.mpr (Nat.lt_succ_of_le hx),
        mul_pos (mul_pos (mul_pos (pow_pos ha _) (binWeight_pos hx hp hp')) hx') (tilt_strict hr hne)⟩
  have hav : avg n q (fun x ↦ ((x : ℝ) - c) * h x) =
      a ^ n * r ^ c * avg n p (fun x ↦ ((x : ℝ) - c) * h x) + ∑ x ∈ range (n + 1), gap x := by
    simp only [avg, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun x hx ↦ ?_
    rw [heq x (Nat.le_of_lt_succ (mem_range.mp hx))]
    dsimp [gap]
    ring
  rw [hav]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (mul_pos (pow_pos ha _)
    (pow_pos (zero_lt_one.trans hr) _)).le havg) hgap

end BekkOrder
