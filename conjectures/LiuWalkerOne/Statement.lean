module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace LiuWalkerOne

noncomputable def cyclicSum (a b c k : ℝ) : ℝ :=
  (a - b) * (a - c) * (b ^ 2 + c ^ 2 - a ^ 2) * a ^ k +
  (b - c) * (b - a) * (c ^ 2 + a ^ 2 - b ^ 2) * b ^ k +
  (c - a) * (c - b) * (a ^ 2 + b ^ 2 - c ^ 2) * c ^ k

/-- Jian Liu's Conjecture 1, equation (7.3), in AIMS Mathematics 5 (2020), p. 6671. -/
def Conjecture : Prop :=
  ∀ a b c k : ℝ, 0 < a → 0 < b → 0 < c →
    a ^ 2 < b ^ 2 + c ^ 2 → b ^ 2 < c ^ 2 + a ^ 2 → c ^ 2 < a ^ 2 + b ^ 2 →
    k ≤ 4 → 0 ≤ cyclicSum a b c k

end LiuWalkerOne
