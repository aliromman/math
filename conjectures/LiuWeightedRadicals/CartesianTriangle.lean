module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace LiuTriangle

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

/-- For distinct A and B, the perpendicular distance from P to the line through A and B. -/
noncomputable def altitude (P A B : Point) : ℝ := |cross A B P| / length A B

end LiuTriangle
