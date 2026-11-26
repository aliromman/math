module

public import conjectures.LiuWeightedRadicals.CartesianTriangle

@[expose] public section
namespace LiuWeightedRadicals

export LiuTriangle (Point length cross Inside altitude)

noncomputable def weight (k : ℝ) (P A B : Point) : ℝ :=
  Real.sqrt (length A B ^ 2 + k * altitude P A B ^ 2)

noncomputable def middle (k : ℝ) (A B C P : Point) : ℝ :=
  let term X Y Z := (length P X + altitude P Y Z) * weight k P Y Z
  2 * (term A B C + term B C A + term C A B) /
    (weight k P B C + weight k P C A + weight k P A B)

/-- Jian Liu, Conjecture 6.4, equation (6.6), J. Inequal. Appl. 2016, 9. -/
def Conjecture : Prop :=
  ∀ (A B C P : Point) (k : ℝ), Inside A B C P → 0 < k → k < 4 →
    middle k A B C P ≤ length P A + length P B + length P C ∧
    2 * (altitude P B C + altitude P C A + altitude P A B) ≤ middle k A B C P

end LiuWeightedRadicals
