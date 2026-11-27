module

public import conjectures.PresuttiStromquist.Atomic
public import conjectures.PresuttiStromquist.RationalWitness
import Mathlib.Tactic.NormNum

public section
namespace PresuttiStromquist.Discrete

set_option maxRecDepth 100000 in
private theorem example_valid : exampleCloud.valid := by decide +kernel

set_option maxRecDepth 100000 in
private theorem example_weight : exampleCloud.frame.weight = 30720 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem example_count :
    lower 42 exampleCloud exampleCloud exampleCloud exampleCloud = 3886611419267072 := by
  decide +kernel

/-- An explicit finite distribution beats the decimal proposed in Conjecture 10.1. -/
theorem quantitative_witness :
    ∃ μ : MeasureTheory.Measure Point, MeasureTheory.IsProbabilityMeasure μ ∧ μ squareᶜ=0 ∧
      118609967629/1132462080000 ≤ rate μ := by
  have hp : 0<exampleCloud.frame.weight := by rw [example_weight]; decide
  obtain ⟨μ,hμ,hs,hr⟩ := certified exampleCloud example_valid hp 42
  refine ⟨μ,hμ,hs,?_⟩
  rw [example_count,example_weight] at hr
  norm_num at hr ⊢
  exact hr

/-- info: 'PresuttiStromquist.Discrete.quantitative_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quantitative_witness

end PresuttiStromquist.Discrete
