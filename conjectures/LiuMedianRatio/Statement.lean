module

public import conjectures.LiuWeightedRadicals.CartesianTriangle

@[expose] public section
namespace LiuMedianRatio

export LiuTriangle (Point length cross Inside altitude)

noncomputable def median (A B C : Point) : ℝ :=
  length A ((B.1 + C.1) / 2, (B.2 + C.2) / 2)

noncomputable def circumradius (A B C : Point) : ℝ :=
  length B C * length C A * length A B / (2 * |cross A B C|)

/-- Jian Liu, Conjecture 1, equation (68), J. Math. Inequal. 14 (2020), 158. -/
def Conjecture : Prop :=
  ∀ A B C P : Point, Inside A B C P →
    4 * circumradius A B C * (median A B C + median B C A + median C A B) /
      (length B C ^ 2 + length C A ^ 2 + length A B ^ 2) ≤
    (length P A + length P B + length P C) /
      (altitude P B C + altitude P C A + altitude P A B)

end LiuMedianRatio
