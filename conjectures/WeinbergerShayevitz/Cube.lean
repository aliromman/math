module

public import conjectures.WeinbergerShayevitz.Statement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace WeinbergerShayevitz
open Finset
open scoped BigOperators

theorem expect_succ {n : ℕ} (f : Word (n+1) → ℝ) :
    (𝔼 x, f x) = ((𝔼 x, f (Fin.cons false x)) + (𝔼 x, f (Fin.cons true x)))/2 := by
  let E := Fin.consEquiv (fun _ : Fin (n+1) ↦ Bool)
  rw [← Fintype.expect_equiv E (fun bc ↦ f (Fin.cons bc.1 bc.2)) f (fun _ ↦ rfl)]
  simp only [Fintype.expect_eq_sum_div_card,Fintype.sum_prod_type,Fintype.sum_bool,
    Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,div_mul_eq_div_div]
  ring

theorem channel_const (e : ℝ) (n : ℕ) (r : ℝ) (x : Word n) :
    channel e n (fun _ ↦ r) x = r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [channel, ih]; ring

theorem greedy_step (e : ℝ) (n : ℕ) (b : Bool) (x : Word n) :
    channel e (n+1) (greedy (n+1)) (Fin.cons b x) =
      (1-e)*signBit b + e*channel e n (greedy n) x := by
  simp only [channel,greedy,Fin.cons_zero,Fin.tail_cons,channel_const]

theorem greedy_variance (n : ℕ) :
    (𝔼 x, channel (3/4) n (greedy n) x ^ 2) ≤ (1:ℝ)/7 := by
  induction n with
  | zero => norm_num [channel,greedy]
  | succ n ih =>
    rw [expect_succ,← expect_add_distrib]
    simp only [greedy_step]
    have point (x : Word n) :
        ((1-(3/4:ℝ))*signBit false + (3/4)*channel (3/4) n (greedy n) x)^2 +
        ((1-3/4)*signBit true + (3/4)*channel (3/4) n (greedy n) x)^2 =
          1/8 + (9/8)*channel (3/4) n (greedy n) x ^ 2 := by norm_num [signBit]; ring
    simp_rw [point,expect_add_distrib,← mul_expect,expect_const univ_nonempty]
    linarith

end WeinbergerShayevitz
