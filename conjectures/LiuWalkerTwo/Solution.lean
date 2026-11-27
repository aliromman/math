module

public import conjectures.LiuWalkerTwo.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LiuWalkerTwo

private theorem ninthPowerBounds {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) :
    ((5 * y + 13 * x) / (13 * y + 5 * x)) ^ 9 ≤ (x / y) ^ 4 ∧
    ((4 * y + 5 * x) / (5 * y + 4 * x)) ^ 9 ≤ x / y := by
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hxy
  constructor <;> simp only [div_pow] <;> rw [div_le_div_iff₀ (by positivity) (by positivity)]
  all_goals
    apply sub_nonneg.mp
    ring_nf
    positivity

private theorem endpoint {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b < c)
    (hacute : c ^ 2 ≤ a ^ 2 + b ^ 2) :
    ((c + b) / (c + a)) ^ 10 ≤
      (c - a) / (c - b) * ((c ^ 2 + b ^ 2 - a ^ 2) / (c ^ 2 + a ^ 2 - b ^ 2)) := by
  have hb := ha.trans_le hab
  have hc := hb.trans hbc
  have hca := hab.trans_lt hbc
  have hden : 0 < c ^ 2 + a ^ 2 - b ^ 2 := by
    linarith [pow_le_pow_left₀ hb.le hbc.le 2, sq_pos_of_pos ha]
  have hsq := pow_le_pow_left₀ ha.le hab 2
  have hdiff := mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr hacute)
  let H := (c + b) / (c + a)
  change H ^ 10 ≤ _
  rw [pow_succ]
  by_cases hcut : 5 * (a + b) ≤ 8 * c
  · have hH : H ≤ (5 * a + 13 * b) / (13 * a + 5 * b) := by
      dsimp [H]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hcut)]
    have h₁ : (b / a) ^ 2 * H ≤ (c - a) / (c - b) := by
      dsimp [H]
      rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (sub_pos.mpr hbc)]
      nlinarith only [hdiff]
    have h₂ : (b / a) ^ 2 ≤ (c ^ 2 + b ^ 2 - a ^ 2) / (c ^ 2 + a ^ 2 - b ^ 2) := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hden]
      nlinarith only [hdiff]
    have h9 := (pow_le_pow_left₀ (div_nonneg (by positivity) (by positivity)) hH 9).trans
      (ninthPowerBounds ha hab).1
    calc
      _ ≤ (b / a) ^ 4 * H := mul_le_mul_of_nonneg_right h9 (by dsimp [H]; positivity)
      _ = ((b / a) ^ 2 * H) * (b / a) ^ 2 := by ring
      _ ≤ _ := mul_le_mul h₁ h₂ (sq_nonneg _)
        (div_nonneg (sub_nonneg.mpr hca.le) (sub_nonneg.mpr hbc.le))
  · have hH : H ≤ (4 * (c - b) + 5 * (c - a)) / (5 * (c - b) + 4 * (c - a)) := by
      have hx := sub_pos.mpr hca
      have hy := sub_pos.mpr hbc
      dsimp [H]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (le_of_not_ge hcut))]
    have hcross : 0 ≤ (a + b) * (2 * c + a + b) - c ^ 2 := by
      nlinarith [mul_nonneg ha.le hb.le, mul_nonneg hc.le (add_nonneg ha.le hb.le)]
    have h₂ : H ≤ (c ^ 2 + b ^ 2 - a ^ 2) / (c ^ 2 + a ^ 2 - b ^ 2) := by
      dsimp [H]
      rw [div_le_div_iff₀ (by positivity) hden]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hab) hcross]
    have h9 := (pow_le_pow_left₀ (div_nonneg (by positivity) (by positivity)) hH 9).trans
      (ninthPowerBounds (sub_pos.mpr hbc) (by linarith : c - b ≤ c - a)).2
    exact mul_le_mul h9 h₂ (by dsimp [H]; positivity)
      (div_nonneg (sub_nonneg.mpr hca.le) (sub_nonneg.mpr hbc.le))

private theorem ordered {a b c k : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hacute : c ^ 2 ≤ a ^ 2 + b ^ 2) (hk : -10 ≤ k) : 0 ≤ cyclicSum a b c k := by
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  have hsq := pow_le_pow_left₀ ha.le hab 2
  rcases hbc.lt_or_eq with hbc | rfl
  · have hden : 0 < c ^ 2 + a ^ 2 - b ^ 2 := by
      linarith [pow_le_pow_left₀ hb.le hbc.le 2, sq_pos_of_pos ha]
    have hbase : 1 ≤ (c + b) / (c + a) := (one_le_div (by positivity)).mpr (by linarith)
    have hw : (c + a) ^ k / (c + b) ^ k ≤
        (c - a) / (c - b) * ((c ^ 2 + b ^ 2 - a ^ 2) / (c ^ 2 + a ^ 2 - b ^ 2)) := calc
      _ = ((c + b) / (c + a)) ^ (-k) := by
        rw [Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by positivity), inv_div]
      _ ≤ ((c + b) / (c + a)) ^ (10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ ≤ _ := by simpa using endpoint ha hab hbc hacute
    rw [div_mul_div_comm, div_le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)
      (mul_pos (sub_pos.mpr hbc) hden)] at hw
    have hpair := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hab)
    have hlast := mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr (hab.trans hbc.le))
      (sub_nonneg.mpr hbc.le)) (sub_nonneg.mpr hacute)) (Real.rpow_nonneg (add_nonneg ha.le hb.le) k)
    unfold cyclicSum
    rw [add_comm b c]
    nlinarith only [hpair, hlast]
  · unfold cyclicSum
    simp only [sub_self, zero_mul, mul_zero, add_zero]
    exact mul_nonneg (mul_nonneg (mul_self_nonneg _) (by linarith [sq_nonneg b]))
      (Real.rpow_nonneg (by positivity) _)

public theorem nonobtuse (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha' : a ^ 2 ≤ b ^ 2 + c ^ 2) (hb' : b ^ 2 ≤ c ^ 2 + a ^ 2)
    (hc' : c ^ 2 ≤ a ^ 2 + b ^ 2) (hk : -10 ≤ k) : 0 ≤ cyclicSum a b c k := by
  have rotate (x y z : ℝ) : cyclicSum x y z k = cyclicSum y z x k := by unfold cyclicSum; ring
  have reverse (x y z : ℝ) : cyclicSum x y z k = cyclicSum z y x k := by
    unfold cyclicSum
    simp only [add_comm z y, add_comm z x, add_comm y x]
    ring
  obtain hab | hba := le_total a b
  · obtain hbc | hcb := le_total b c
    · exact ordered ha hab hbc hc' hk
    · obtain hac | hca := le_total a c
      · rw [rotate, reverse]
        exact ordered ha hac hcb (by linarith) hk
      · rw [← rotate c a b]
        exact ordered hc hca hab hb' hk
  · obtain hac | hca := le_total a c
    · rw [← rotate c a b, reverse]
      exact ordered hb hba hac (by linarith) hk
    · obtain hbc | hcb := le_total b c
      · rw [rotate]
        exact ordered hb hbc hca ha' hk
      · rw [reverse]
        exact ordered hc hcb hba (by linarith) hk

public theorem result : Conjecture :=
  fun a b c k ha hb hc ha' hb' hc' hk => nonobtuse a b c k ha hb hc ha'.le hb'.le hc'.le hk

/-- info: 'LiuWalkerTwo.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

end LiuWalkerTwo
