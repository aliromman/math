module

public import conjectures.SunLucasRatios.Statement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

public section

namespace SunLucasRatios

/-- The ratios at indices five and six contradict the proposed strict decrease. -/
theorem counterexample : ¬ Conjecture := by
  intro h
  have hanti := (h.2.2 3 (-26) (by decide) (by decide) (by decide) (Or.inl (by decide))).1
  have hratio := hanti (show 5 ∈ Set.Ici 4 by decide) (show 6 ∈ Set.Ici 4 by decide)
    (by decide : 5 < 6)
  norm_num [ratio, root, lucas] at hratio
  have hmul := (div_lt_div_iff₀ (by positivity) (by positivity)).mp hratio
  have hpow := pow_le_pow_left₀ (by positivity) hmul.le 210
  norm_num [mul_pow, ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (1459 : ℝ)),
    ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (9135 : ℝ)),
    ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (65339 : ℝ)), Real.rpow_ofNat] at hpow

/-- info: 'SunLucasRatios.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample

end SunLucasRatios
