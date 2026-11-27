module

public import conjectures.WeinbergerShayevitz.Gini
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace WeinbergerShayevitz
open Finset
open scoped BigOperators

private theorem rank_sum (a t : ℕ) :
    2*(∑ i ∈ range t, ((a:ℝ)+i+1)) = t*(2*a+t+1) := by
  induction t with
  | zero => simp
  | succ t h => rw [sum_range_succ]; push_cast; linarith

private theorem rank_one (a t : ℕ) (ht : 0<t) :
    rankCost 1 a t = a + ((t:ℝ)+1)/2 := by
  unfold rankCost
  simp only [Real.rpow_one]
  have hp : (t:ℝ)≠0 := by positivity
  field_simp
  linarith [rank_sum a t]

private theorem row {n : ℕ} (z : Word n → ℝ) (x : Word n) :
    (1+z x)/2*rankCost 1 (univ.filter (fun y ↦ z x < z y)).card
        (univ.filter (fun y ↦ z y = z x)).card +
      (1-z x)/2*rankCost 1 (univ.filter (fun y ↦ z y < z x)).card
        (univ.filter (fun y ↦ z y = z x)).card =
    (2^n+1)/2-(2^n/2)*(z x*(𝔼 y, cmp (z x) (z y))) := by
  classical
  let A := (univ.filter (fun y ↦ z x < z y)).card
  let B := (univ.filter (fun y ↦ z y < z x)).card
  let T := (univ.filter (fun y ↦ z y = z x)).card
  have hT : 0 < T := card_pos.mpr ⟨x,by simp⟩
  have hc : (A:ℝ)+B+T=2^n := by
    change ((univ.filter _).card:ℝ)+((univ.filter _).card:ℝ)+((univ.filter _).card:ℝ)=2^n
    rw [←sum_boole,←sum_boole,←sum_boole,←sum_add_distrib,←sum_add_distrib]
    calc
      _ = ∑ _ : Word n, (1:ℝ) := by
        apply sum_congr rfl
        intro y _
        rcases lt_trichotomy (z y) (z x) with h|h|h <;> simp [*,lt_asymm,ne_of_lt,ne_of_gt]
      _ = _ := by simp [Word]
  have hd : (𝔼 y, cmp (z x) (z y)) = ((B:ℝ)-A)/2^n := by
    simp [Fintype.expect_eq_sum_div_card,cmp,sum_sub_distrib,Word,A,B]
  change (1+z x)/2 * rankCost 1 A T + (1-z x)/2 * rankCost 1 B T = _
  rw [rank_one _ _ hT,rank_one _ _ hT,hd]
  have hp : (2:ℝ)^n ≠ 0 := by positivity
  field_simp
  nlinarith [hc,congrArg (fun u : ℝ ↦ u*(2:ℝ)^n) hc]

theorem guessingRatio_one {n : ℕ} (z : Word n → ℝ) :
    guessingRatio 1 z = 1-(2^n/(2^n+1))*alignment z z := by
  classical
  unfold guessingRatio
  simp only [row,expect_sub_distrib,←mul_expect,expect_const univ_nonempty,alignment]
  rw [rank_one 0 _ (by positivity)]
  push_cast
  have hp : (2:ℝ)^n+1≠0 := by positivity
  field_simp
  ring

end WeinbergerShayevitz
