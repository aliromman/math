module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
namespace LiuWeightedRadicals

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
