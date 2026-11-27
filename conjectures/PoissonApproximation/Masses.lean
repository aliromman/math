module

public import conjectures.PoissonApproximation.Statement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace PoissonApproximation
open Real ProbabilityTheory MeasureTheory
open scoped unitInterval

noncomputable def bmass (n : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  (n.choose k) * (r/n)^k * (1-r/n)^(n-k)
noncomputable def pmass (r : ℝ) (k : ℕ) : ℝ := exp (-r)*r^k/k.factorial

theorem zero_deficit (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (h1 : r≤1) :
    (1-r/n)^n ≤ exp (-r) := by
  have np : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have q : 0≤1-r/n := sub_nonneg.mpr ((div_le_one np).mpr (by exact h1.trans (by exact_mod_cast (show 1≤n by omega))))
  have H := pow_le_pow_left₀ q (show 1-r/n ≤ exp (-(r/n)) by
    linarith [Real.add_one_le_exp (-(r/n))]) n
  rw [← Real.exp_nat_mul] at H
  simpa [show (n:ℝ)*(-(r/n)) = -r by field_simp] using H

theorem first_excess (n : ℕ) (hn : 2≤n) {r : ℝ} (h0 : 0≤r) (h1 : r≤1) :
    pmass r 1 ≤ bmass n r 1 := by
  have N : (2:ℝ)≤n := by exact_mod_cast hn
  have np : (0:ℝ)<n := by linarith
  have qp : 0<1-r/n := sub_pos.mpr ((div_lt_one np).mpr (by linarith))
  have L := Real.log_le_sub_one_of_pos (inv_pos.mpr qp)
  rw [Real.log_inv] at L
  have Z : (0:ℝ)≤n-1 := by linarith
  have g := mul_le_mul_of_nonneg_left L Z
  have d : (n-1:ℝ)*((1-r/n)⁻¹-1)≤r := by
    have nr : 0<(n:ℝ)-r := by linarith
    have ratio : (1-r/n)⁻¹-1=r/(n-r) := by field_simp; ring
    rw [ratio, ←mul_div_assoc]
    apply (div_le_iff₀ nr).mpr
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have E : exp (-r) ≤ (1-r/n)^(n-1) := by
    rw [← Real.exp_log qp,←Real.exp_nat_mul,exp_le_exp,Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
    linarith
  simp only [bmass,pmass,Nat.choose_one_right,Nat.factorial_one,Nat.cast_one,pow_one,div_one]
  calc
    _ ≤ (1-r/n)^(n-1)*r := mul_le_mul_of_nonneg_right E h0
    _ = _ := by field_simp

private theorem falling_bound (n : ℕ) (hn : 2≤n) (k : ℕ) (hk : 3≤k) :
    n.descFactorial k ≤ (n-1)^k := by
  induction k, hk using Nat.le_induction with
  | base =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
    simp [Nat.descFactorial, Nat.add_comm 2 m, Nat.pow_succ]
    nlinarith
  | succ k hk ih =>
    rw [Nat.descFactorial_succ,pow_succ']
    exact Nat.mul_le_mul (by omega) ih

theorem tail_mass (n : ℕ) (hn : 2≤n) {r : ℝ} (h0 : 0≤r) (h1 : r≤1)
    (k : ℕ) (hk : 3≤k) : bmass n r k ≤ pmass r k := by
  by_cases hkn : k≤n
  · have N : (2:ℝ)≤n := by exact_mod_cast hn
    have np : (0:ℝ)<n := by linarith
    have q : 0≤1-r/n := sub_nonneg.mpr ((div_le_one np).mpr (by linarith))
    have desc : (n.descFactorial k:ℝ) ≤ (n-r:ℝ)^k := by
      have h : (n.descFactorial k:ℝ) ≤ ((n-1:ℕ):ℝ)^k := by exact_mod_cast falling_bound n hn k hk
      apply h.trans
      rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have join : (n-r)^k*(r/n)^k*(1-r/n)^(n-k)=r^k*(1-r/n)^n := by
      rw [←mul_pow,show ((n:ℝ)-r)*(r/n)=r*(1-r/n) by field_simp,mul_pow,mul_assoc,←pow_add]
      rw [Nat.add_sub_of_le hkn]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<k.factorial)).mpr
    unfold bmass
    calc
      _ = (n.descFactorial k:ℝ)*(r/n)^k*(1-r/n)^(n-k) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
        ring
      _ ≤ (n-r)^k*(r/n)^k*(1-r/n)^(n-k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right desc (by positivity)) (by positivity)
      _ = _ := join
      _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_left (zero_deficit n hn h1) (pow_nonneg h0 k)
  · rw [bmass,Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul,zero_mul,pmass]
    positivity

end PoissonApproximation
