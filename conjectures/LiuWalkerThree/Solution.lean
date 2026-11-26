module

public import conjectures.LiuWalkerThree.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LiuWalkerThree

private theorem liftExponent {A B u v k : ℝ} (hA : 0 ≤ A) (hv : 0 < v) (huv : v ≤ u)
    (hk : -3 ≤ k) (h : B * u ^ 3 ≤ A * v ^ 3) : B * v ^ k ≤ A * u ^ k := by
  have hu := hv.trans_le huv
  have hm := Real.rpow_le_rpow hv.le huv (show 0 ≤ k + 3 by linarith)
  have hh := mul_le_mul h hm (Real.rpow_nonneg hv.le _) (mul_nonneg hA (pow_nonneg hv.le 3))
  have split (x : ℝ) (hx : 0 < x) : x ^ (k + 3) = x ^ k * x ^ (3 : ℕ) := by
    simpa using Real.rpow_add_natCast hx.ne' k 3
  rw [split v hv, split u hu] at hh
  apply le_of_mul_le_mul_right (a := u ^ 3 * v ^ 3) _ (by positivity)
  linarith only [hh]

private theorem ordered {a b c k : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c ^ 2 ≤ a ^ 2 + b ^ 2) (hk : -3 ≤ k) : 0 ≤ cyclicSum a b c k := by
  have hb := ha.trans_le hab
  have hac := hab.trans hbc
  have ht : 0 < a + b - c := by
    by_contra! hh
    have := pow_le_pow_left₀ (by linarith : 0 ≤ a + b) (by linarith : a + b ≤ c) 2
    nlinarith only [this, hc, mul_pos ha hb]
  have hd := sub_nonneg.mpr hab
  have hca := sub_nonneg.mpr hac
  have hcb := sub_nonneg.mpr hbc
  have hq := sub_nonneg.mpr hc
  have hs : 0 ≤ 2 * c - a - b := by linarith
  have hA : 0 ≤ b ^ 2 + c ^ 2 - a ^ 2 := by
    linarith [pow_le_pow_left₀ ha.le hab 2, sq_nonneg c]
  have endpoint :
      (c - b) * (c ^ 2 + a ^ 2 - b ^ 2) * (b + c - a) ^ 3 ≤
      (c - a) * (b ^ 2 + c ^ 2 - a ^ 2) * (c + a - b) ^ 3 := by
    apply sub_nonneg.mp
    calc
      _ = (b - a) * ((a + b - c) ^ 3 * (c ^ 2 + (b - a) ^ 2) +
          2 * (a ^ 2 + b ^ 2 - c ^ 2) *
            ((a + b - c) ^ 2 * (2 * c - a - b) + 4 * (a + b) * (c - a) * (c - b))) := by ring
      _ ≥ 0 := by positivity
  have weighted := liftExponent (mul_nonneg hca hA) (by linarith : 0 < c + a - b)
    (by linarith : c + a - b ≤ b + c - a) hk endpoint
  have paired := mul_le_mul_of_nonneg_left weighted hd
  have last := mul_nonneg (mul_nonneg (mul_nonneg hca hcb) hq) (Real.rpow_nonneg ht.le k)
  unfold cyclicSum
  linarith only [paired, last]

public theorem nonobtuse (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha' : a ^ 2 ≤ b ^ 2 + c ^ 2) (hb' : b ^ 2 ≤ c ^ 2 + a ^ 2)
    (hc' : c ^ 2 ≤ a ^ 2 + b ^ 2) (hk : -3 ≤ k) : 0 ≤ cyclicSum a b c k := by
  have rotate (x y z : ℝ) : cyclicSum x y z k = cyclicSum y z x k := by
    unfold cyclicSum
    ring
  have reverse (x y z : ℝ) : cyclicSum x y z k = cyclicSum z y x k := by
    simp only [cyclicSum, add_comm x z, add_comm y x, add_comm z y]
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

/-- info: 'LiuWalkerThree.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

end LiuWalkerThree
