module

public import conjectures.LiuWalkerOne.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LiuWalkerOne

private theorem ordered {a b c k : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hacute : c ^ 2 ≤ a ^ 2 + b ^ 2) (hk : k ≤ 4) : 0 ≤ cyclicSum a b c k := by
  have hb := ha.trans_le hab
  have hac := hab.trans hbc
  have hsq : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hcommon := mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr hacute)
  have h₁ : (c - b) * b ^ 2 ≤ (c - a) * a ^ 2 := by
    apply le_of_mul_le_mul_right (a := c + a) _ (by linarith)
    calc
      _ ≤ (c - b) * b ^ 2 * (c + b) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (sub_nonneg.mpr hbc) (sq_nonneg _))
      _ ≤ _ := by nlinarith only [hcommon]
  have h₂ : (c ^ 2 + a ^ 2 - b ^ 2) * b ^ 2 ≤ (b ^ 2 + c ^ 2 - a ^ 2) * a ^ 2 := by
    nlinarith only [hcommon]
  have hm : 0 ≤ c ^ 2 + a ^ 2 - b ^ 2 := by
    linarith [pow_le_pow_left₀ hb.le hbc 2, sq_nonneg a]
  have hpow := Real.rpow_le_rpow_of_nonpos ha hab (sub_nonpos.mpr hk)
  have hp (x : ℝ) (hx : 0 < x) : x ^ (k - 4) * x ^ (4 : ℕ) = x ^ k := by
    simpa using (Real.rpow_add_natCast hx.ne' (k - 4) 4).symm
  have hca := sub_nonneg.mpr hac
  have hside : 0 ≤ b ^ 2 + c ^ 2 - a ^ 2 := by linarith [sq_nonneg c]
  have hprod := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have hweighted := mul_le_mul hprod hpow (Real.rpow_nonneg hb.le _)
    (by positivity)
  have hpair := mul_le_mul_of_nonneg_left hweighted (sub_nonneg.mpr hab)
  have hlast := mul_nonneg (mul_nonneg (mul_nonneg hca (sub_nonneg.mpr hbc))
    (sub_nonneg.mpr hacute)) (Real.rpow_nonneg (ha.le.trans hac) k)
  unfold cyclicSum
  rw [← hp a ha, ← hp b hb]
  nlinarith only [hpair, hlast]

public theorem nonobtuse (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha' : a ^ 2 ≤ b ^ 2 + c ^ 2) (hb' : b ^ 2 ≤ c ^ 2 + a ^ 2)
    (hc' : c ^ 2 ≤ a ^ 2 + b ^ 2) (hk : k ≤ 4) : 0 ≤ cyclicSum a b c k := by
  have rotate (x y z : ℝ) : cyclicSum x y z k = cyclicSum y z x k := by
    unfold cyclicSum
    ring
  have reverse (x y z : ℝ) : cyclicSum x y z k = cyclicSum z y x k := by
    unfold cyclicSum
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

/-- info: 'LiuWalkerOne.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

end LiuWalkerOne
