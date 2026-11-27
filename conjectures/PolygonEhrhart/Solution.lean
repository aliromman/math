module

public import conjectures.PolygonEhrhart.Samples
public import conjectures.PolygonEhrhart.Interpolation

@[expose] public section
namespace PolygonEhrhart
open Polynomial

private theorem slope_value :
    slope (fun i ↦ (samples i : ℚ)) = -298495711/35302608 := by decide +kernel

/-- The linear coefficient of the degree-28 Ehrhart polynomial of the 13-gon face lattice. -/
theorem linear_coefficient (P : ℚ[X])
    (counts : ∀ t : ℕ, P.eval (t:ℚ) = pointCount 13 t) :
    P.coeff 1 = -298495711/35302608 := by
  have deg := counting_natDegree_le (P := P) (fun t ↦ by
    rw [counts]
    exact_mod_cast pointCount_pos 13 t) (fun t ↦ by
    rw [counts]
    exact_mod_cast pointCount_bound 13 t)
  have vals : (fun t : Fin 29 ↦ P.eval (t.val:ℚ)) = fun i ↦ (samples i:ℚ) := by
    funext i
    rw [counts,sample_counts]
  rw [← slope_eq_coeff P deg,vals]
  exact slope_value

theorem resolution : ¬Conjecture := by
  intro h
  obtain ⟨P,counts,nn⟩ := h 13 (by decide)
  have neg := linear_coefficient P counts
  have pos := nn 1
  rw [neg] at pos
  norm_num at pos

/-- info: 'PolygonEhrhart.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'PolygonEhrhart.linear_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linear_coefficient

end PolygonEhrhart
