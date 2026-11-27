module

public import conjectures.LiuWeightedRadicals.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity

namespace LiuWeightedRadicals

/-- The triangle and the interior point both have rational vertex distances. -/
public theorem result : ¬ Conjecture := by
  intro claim
  have h := (claim (-1, 0) (1, 0) (0, 84/13) (0, 60/11) (3999/1000)
    (by norm_num [Inside, cross]) (by norm_num) (by norm_num)).1
  norm_num [middle, weight, length, altitude, cross] at h
  let u := Real.sqrt 791286207077 / Real.sqrt 18468003125
  let v := Real.sqrt 74402 / Real.sqrt 605
  change 2 * (5329 / 935 * u + 5329 / 935 * u + 84 / 13 * v) / (u + u + v) ≤
    1730 / 143 at h
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hrel : (118 / 143 : ℝ) * v ≤ (16992 / 12155 : ℝ) * u := by
    linarith [(div_le_iff₀ (by positivity : 0 < u + u + v)).mp h]
  have hs := pow_le_pow_left₀ (by positivity) hrel 2
  norm_num [u, v, mul_pow, div_pow, Real.sq_sqrt] at hs

/-- info: 'LiuWeightedRadicals.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

end LiuWeightedRadicals
