module

public import conjectures.SunPrimePowers.Statement
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

public section

namespace SunPrimePowers

private theorem ninth_prime : primeAt 9 = 23 :=
  Nat.nth_count (by decide : Nat.Prime 23)

/-- An integer inequality certifies the comparison of the geometric mean with Sun's bound. -/
private theorem prime_product_bound :
    (23 : ℝ) ^ (2000 : ℝ)⁻¹ / (2001 / 2000) < (223092870 : ℝ) ^ (18000 : ℝ)⁻¹ := by
  apply (Real.lt_rpow_inv_iff_of_pos (by positivity) (by norm_num) (by norm_num)).2
  rw [Real.rpow_ofNat, div_pow, ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (23 : ℝ))]
  rw [show (2000 : ℝ)⁻¹ * (18000 : ℕ) = 9 by norm_num, Real.rpow_ofNat,
    div_lt_iff₀ (by positivity)]
  have h₁ : (1301 / 1250 : ℝ) ≤ (2001 / 2000 : ℝ) ^ 80 := by norm_num
  have h₂ : (125 / 46 : ℝ) ≤ (2001 / 2000 : ℝ) ^ 2000 := calc
    _ ≤ (1301 / 1250 : ℝ) ^ 25 := by norm_num
    _ ≤ ((2001 / 2000 : ℝ) ^ 80) ^ 25 := pow_le_pow_left₀ (by norm_num) h₁ 25
    _ = _ := by rw [← pow_mul]
  calc
    _ < 223092870 * (125 / 46 : ℝ) ^ 9 := by norm_num
    _ ≤ 223092870 * ((2001 / 2000 : ℝ) ^ 2000) ^ 9 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h₂ 9) (by norm_num)
    _ = _ := by rw [← pow_mul]

/-- At `n = 9` and exponent `1/2000`, even the geometric mean exceeds the proposed bound. -/
theorem counterexample : ¬ Conjecture := by
  intro h
  have hceil : ⌈(2000 : ℝ)⁻¹⌉₊ = 1 := (Nat.ceil_eq_iff (by decide)).2 (by norm_num)
  have claimed := h (2000 : ℝ)⁻¹ (by positivity) 9 (by rw [hceil]; decide)
  rw [ninth_prime] at claimed
  let s := (Finset.range 24).filter Nat.Prime
  have hc : s.card = 9 := by decide
  have hp : ∏ p ∈ s, p = 223092870 := by decide
  have hr : ∏ p ∈ s, (p : ℝ) = 223092870 := by
    simpa only [Nat.cast_prod, Nat.cast_ofNat] using congrArg (Nat.cast : ℕ → ℝ) hp
  have gm := Real.geom_mean_le_arith_mean s (fun _ => 1)
    (fun p => (p : ℝ) ^ (2000 : ℝ)⁻¹) (by simp) (by simp [hc]) (by intros; positivity)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_mul, hc, Nat.cast_ofNat,
    Real.rpow_one] at gm
  rw [Real.finsetProd_rpow s (fun p => (p : ℝ)) (by intros; positivity), hr,
    ← Real.rpow_mul (by norm_num : 0 ≤ (223092870 : ℝ))] at gm
  rw [show (2000 : ℝ)⁻¹ * (9 : ℝ)⁻¹ = (18000 : ℝ)⁻¹ by norm_num] at gm
  rw [show (2000 : ℝ)⁻¹ + 1 = 2001 / 2000 by norm_num] at claimed
  exact (not_lt_of_ge (prime_product_bound.le.trans gm)) claimed

/-- info: 'SunPrimePowers.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample

end SunPrimePowers
