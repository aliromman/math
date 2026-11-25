module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
namespace LiuMedianRatio

abbrev Point := ℝ × ℝ

noncomputable def length (A B : Point) : ℝ :=
  Real.sqrt ((A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2)

/-- Signed area of the parallelogram on AB and AC. -/
def cross (A B C : Point) : ℝ :=
  (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)

/-- The point lies strictly on the triangle side of each of its three lines. -/
def Inside (A B C P : Point) : Prop :=
  0 < cross A B C * cross A B P ∧ 0 < cross B C A * cross B C P ∧
    0 < cross C A B * cross C A P

noncomputable def altitude (P A B : Point) : ℝ := |cross A B P| / length A B

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
