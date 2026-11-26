module

public import conjectures.PresuttiStromquist.Block
public import conjectures.PresuttiStromquist.Construction

public section
namespace PresuttiStromquist
open MeasureTheory

/-- No choice of the two positive bubble sizes can give an optimal measure. -/
theorem TwoBubble.not_optimal {u v J : ℝ} {μ : Measure Point} (h : TwoBubble u v J μ) :
    ¬Optimal μ := by
  intro opt
  let : IsProbabilityMeasure μ := opt.1
  exact corner_obstruction h.bounds h.separation h.corner (h.internal_positive opt.positive) opt

theorem resolution : ¬Conjecture := by
  rintro ⟨μ,⟨u,v,J,h,_⟩,_,optimal⟩
  exact h.not_optimal optimal

/-- info: 'PresuttiStromquist.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end PresuttiStromquist
