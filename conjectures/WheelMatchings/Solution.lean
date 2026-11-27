module

public import conjectures.WheelMatchings.Counts
public import conjectures.WheelMatchings.Enumeration
public import conjectures.WheelMatchings.OneInterior

public section

namespace WheelMatchings

/-- Twelve points on the parabola have more ten-crossing matchings than the regular wheel. -/
theorem counterexample : General (@parabola 12) ∧ count (m := 6) parabola 10 = 252 ∧
    count (wheel 6) 10 = 176 :=
  ⟨parabola_general _, (parabola_count 6 10).trans convex_count,
    (regular_wheel_count 6 10 (by decide)).trans wheel_count⟩

theorem resolution : ¬Conjecture := by
  intro h
  have hm := (h 6 (by decide)).2 parabola counterexample.1
  change count (m := 6) parabola 10 ≤ count (wheel 6) 10 at hm
  rw [counterexample.2.1, counterexample.2.2] at hm
  omega

theorem no_proposed_bound : ¬ProposedUpperBound := by
  intro h
  have hm := h 6 (by decide) oneInterior oneInterior_general
  change count (m := 6) oneInterior 10 ≤ 176 at hm
  rw [oneInterior_count] at hm
  omega

/-- info: 'WheelMatchings.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'WheelMatchings.no_proposed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_proposed_bound

end WheelMatchings
