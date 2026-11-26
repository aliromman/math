module

public import conjectures.StrausBoundaryPolygon.NonagonArea
public import conjectures.StrausBoundaryPolygon.Heptagon

public section
namespace StrausBoundaryPolygon
open MeasureTheory

theorem nonagon_ratio : polygonArea Example.quadrilateral / volume.real Example.body = 2/3 := by
  rw [Example.quad_area,Example.area]
  norm_num

theorem heptagon_comparison : (2:ℝ)/3 < polygonArea Heptagon.quadrilateral / volume.real (regularBody 7) := by
  rw [lt_div_iff₀ Heptagon.area_positive]
  linarith [Heptagon.area_upper,Heptagon.area_lower]

/-- A nine-vertex convex polygon has a lower maximum quadrilateral ratio
    than the regular heptagon. Its maximizing trapezoid shares one edge. -/
theorem conjecture1_false : ¬ Conjecture := by
  intro claim
  obtain ⟨r,maximum,_,minimum⟩ := claim 4 (by decide)
  have m := minimum Example.body Example.convex Example.compact Example.interior_nonempty
    Example.quadrilateral Example.maximal Example.shares
  have test := maximum.2 Heptagon.quadrilateral Heptagon.inscribed
  change polygonArea Heptagon.quadrilateral ≤ polygonArea r at test
  change polygonArea r/volume.real (regularBody 7) ≤ _ at m
  rw [nonagon_ratio] at m
  have lower := div_le_div_of_nonneg_right test (le_of_lt Heptagon.area_positive)
  exact (not_lt_of_ge (lower.trans m)) heptagon_comparison

/-- info: 'StrausBoundaryPolygon.conjecture1_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conjecture1_false

end StrausBoundaryPolygon
