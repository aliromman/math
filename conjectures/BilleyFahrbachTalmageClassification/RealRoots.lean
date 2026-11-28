module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.Linarith

/-! # Two inequalities for polynomials with real roots -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial

/-- Moving a real argument vertically increases its distance from each real zero. -/
theorem norm_eval_le_aeval (p : ℝ[X]) (hp : p.Splits) (z : ℂ) :
    |p.eval z.re| ≤ ‖aeval z p‖ := by
  obtain ⟨roots, h⟩ := splits_iff_exists_multiset.mp hp
  have hprod (r : Multiset ℝ) :
      |(r.map (fun t => z.re - t)).prod| ≤ ‖(r.map (fun t : ℝ => z - (t : ℂ))).prod‖ := by
    induction r using Multiset.induction_on with
    | empty => simp
    | cons t r ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, abs_mul, norm_mul]
      exact mul_le_mul (by simpa using Complex.abs_re_le_norm (z - (t : ℂ))) ih
        (abs_nonneg _) (norm_nonneg _)
  conv_lhs => rw [h]
  conv_rhs => rw [h]
  simpa [eval_multiset_prod, map_multiset_prod, Multiset.map_map, Function.comp_def, abs_mul] using
    mul_le_mul_of_nonneg_left (hprod roots) (abs_nonneg p.leadingCoeff)

/-- On an interval with no root, the central value satisfies the discrete log-concavity inequality. -/
theorem eval_midpoint (p : ℝ[X]) (hp : p.Splits) (x : ℝ)
    (h : ∀ t ∈ Set.Icc (x-1) (x+1), p.eval t ≠ 0) :
    |p.eval (x-1)| * |p.eval (x+1)| ≤ (p.eval x)^2 := by
  classical
  by_cases hz : p = 0
  · simp [hz]
  have one (t : ℝ) (ht : t ∈ p.roots) : |x-1-t| * |x+1-t| ≤ (x-t)^2 := by
    have hn : t ∉ Set.Icc (x-1) (x+1) := fun hc => h t hc ((mem_roots hz).mp ht)
    rcases lt_or_ge t (x-1) with hl | hl
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      nlinarith
    · have hr : x+1 < t := lt_of_not_ge fun hh => hn ⟨hl, hh⟩
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      nlinarith
  have product (r : Multiset ℝ) (hr : ∀ t ∈ r, t ∈ p.roots) :
      |(r.map (fun t => x-1-t)).prod| * |(r.map (fun t => x+1-t)).prod| ≤
        ((r.map (fun t => x-t)).prod)^2 := by
    induction r using Multiset.induction_on with
    | empty => simp
    | cons t r ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, abs_mul, mul_pow]
      rw [mul_mul_mul_comm]
      exact mul_le_mul (one t (hr _ (by simp)))
        (ih (by intro t ht; exact hr t (by simp [ht])))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (sq_nonneg _)
  simp only [hp.eval_eq_prod_roots, abs_mul, mul_pow]
  rw [mul_mul_mul_comm, ← sq, sq_abs]
  exact mul_le_mul_of_nonneg_left (product p.roots fun _ ht => ht) (sq_nonneg _)

end BilleyFahrbachTalmageClassification
