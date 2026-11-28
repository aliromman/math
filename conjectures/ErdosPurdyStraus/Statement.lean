module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
noncomputable section
namespace ErdosPurdyStraus
open Set MeasureTheory

/-- The real plane with its product coordinates and Lebesgue area. -/
abbrev Plane := ℝ × ℝ

/-- The signed double area of the oriented triangle with vertices `a`, `b`, and `c`. -/
def cross (a b c : Plane) : ℝ := (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

/-- The ordinary nonnegative area of the triangle. -/
def triangleArea (a b c : Plane) : ℝ := |cross a b c|/2

/-- A largest triangle in a compact convex body, with the side from a to b on its boundary. -/
structure Admissible (K : Set Plane) (a b c : Plane) : Prop where
  convex : Convex ℝ K
  compact : IsCompact K
  a_mem : a ∈ K
  b_mem : b ∈ K
  c_mem : c ∈ frontier K
  side : segment ℝ a b ⊆ frontier K
  positive : 0 < triangleArea a b c
  largest : ∀ p ∈ K, ∀ q ∈ K, ∀ v ∈ K, triangleArea p q v ≤ triangleArea a b c

/-- All area ratios in Erdős, Purdy and Straus's Problem 3.4 (1982). -/
noncomputable def ratios : Set ℝ := {r | ∃ (K : Set Plane) (a b c : Plane),
  Admissible K a b c ∧ r = volume.real K / triangleArea a b c}

/-- The proposed area ratio is attained and bounds every admissible ratio from above. -/
def IsAnswer (r : ℝ) : Prop := IsGreatest ratios r

/-- The root of the quartic that lies strictly between zero and one quarter. -/
def Parameter (t : ℝ) : Prop := 0<t ∧ t<1/4 ∧ (1+t)^4=2*(1+t^2)

end ErdosPurdyStraus
end
