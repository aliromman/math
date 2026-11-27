module

public import conjectures.LiuMedianRatio.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity

namespace LiuMedianRatio

public theorem result : ¬ Conjecture := by
  intro claim
  have h := claim (0, 0) (9, 0) (4, 1/10) (4, 1/1000) (by norm_num [Inside, cross])
  norm_num [circumradius, length, median, altitude, cross, Real.sq_sqrt] at h
  let a := Real.sqrt 2501 / 10
  let b := Real.sqrt 1601 / 10
  let m := Real.sqrt 16901 / 20 + Real.sqrt 19601 / 20 + Real.sqrt 13 / Real.sqrt 50
  let v := Real.sqrt 16000001 / 1000 + Real.sqrt 25000001 / 1000 + 99 / 1000
  change 4 * (a*b*9/(9/5)) * m / (a^2+b^2+81) ≤
      v / (99/200/a + 99/250/b + 1/1000) at h
  have ha : 5 ≤ a := by
    apply (le_div_iff₀ (by norm_num)).mpr
    apply Real.le_sqrt_of_sq_le; norm_num
  have hb : 4 ≤ b := by
    apply (le_div_iff₀ (by norm_num)).mpr
    apply Real.le_sqrt_of_sq_le; norm_num
  have ha' : a ≤ 501/100 := by
    apply (div_le_iff₀ (by norm_num)).mpr
    rw [Real.sqrt_le_iff]; norm_num
  have hb' : b ≤ 401/100 := by
    apply (div_le_iff₀ (by norm_num)).mpr
    rw [Real.sqrt_le_iff]; norm_num
  have hsq : a^2+b^2+81 = 12202/100 := by norm_num [a, b, div_pow, Real.sq_sqrt]
  have hm : 14 ≤ m := by
    have h1 : 130 ≤ Real.sqrt 16901 := Real.le_sqrt_of_sq_le (by norm_num)
    have h2 : 140 ≤ Real.sqrt 19601 := Real.le_sqrt_of_sq_le (by norm_num)
    have h3 : 1/2 ≤ Real.sqrt 13 / Real.sqrt 50 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 13),
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 50), Real.sqrt_nonneg 13, Real.sqrt_nonneg 50]
    dsimp [m]; linarith
  have hv : v ≤ 9101/1000 := by
    have h1 : Real.sqrt 16000001 ≤ 4001 := Real.sqrt_le_iff.mpr (by norm_num)
    have h2 : Real.sqrt 25000001 ≤ 5001 := Real.sqrt_le_iff.mpr (by norm_num)
    dsimp [v]; linarith
  have ap : 0 < a := by linarith
  have bp : 0 < b := by linarith
  have hcross := (div_le_div_iff₀ (by positivity : 0 < a^2+b^2+81)
    (by positivity : 0 < 99/200/a + 99/250/b + 1/1000)).mp h
  have hab : 5*4 ≤ a*b := mul_le_mul ha hb (by norm_num) ap.le
  have hnum : 4*(5*4*9/(9/5))*(14:ℝ) ≤ 4*(a*b*9/(9/5))*m := by
    gcongr
  have hden : 99/200/(501/100) + 99/250/(401/100) + 1/1000 ≤
      99/200/a + 99/250/b + 1/1000 := by gcongr
  have hh := mul_le_mul hnum hden (by norm_num) (by positivity)
  rw [hsq] at hcross
  linarith

/-- info: 'LiuMedianRatio.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

end LiuMedianRatio
