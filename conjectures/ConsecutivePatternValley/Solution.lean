module

public import conjectures.ConsecutivePatternValley.Statement
import Mathlib.Tactic.NormNum

@[expose] public section
namespace ConsecutivePatternValley

/-- The consecutive pattern 51234 in one-based notation. -/
def witness : List ℕ := [4,0,1,2,3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem counts : layerCounts witness 7 7 = (12,359) ∧
    layerCounts witness 7 8 = (15,455) ∧ layerCounts witness 7 9 = (18,531) := by
  decide +kernel

theorem three_means : expectation witness 7 7 = 12/359 ∧
    expectation witness 7 8 = 3/91 ∧ expectation witness 7 9 = 2/59 := by
  obtain ⟨a,b,c⟩ := counts
  norm_num [expectation,a,b,c]

theorem resolution : ¬ Conjecture := by
  intro h
  obtain ⟨peak,_,up,down⟩ := h 5 (by decide) witness (by decide) 7 (by decide)
  obtain ⟨a,b,c⟩ := three_means
  by_cases mid : 8 ≤ peak
  · have step := up 7 8 (by decide) mid
    rw [a,b] at step
    norm_num at step
  · have step := down 8 9 (by omega) (by decide) (by decide)
    rw [b,c] at step
    norm_num at step

/-- info: 'ConsecutivePatternValley.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end ConsecutivePatternValley
