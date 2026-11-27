module

public import conjectures.SavchenkoDiameter.Statement

@[expose] public section
namespace SavchenkoDiameter

/-- Block sizes (7,1,1,1,2,1,1,1,7) along the nine-vertex path. -/
def competitor : Tournament 22 :=
  blowup (fun i ↦ if i.val ≤ 10 then i.val-6 else min 8 (i.val-7))

/-- Block sizes (4,1,1,1,1,2,1,1,1,1,4) along the eleven-vertex path. -/
def competitorFive : Tournament 18 :=
  blowup (fun i ↦ if i.val ≤ 8 then i.val-3 else min 10 (i.val-4))

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem competitor_diameter : DiameterAtMost competitor 8 := by
  unfold DiameterAtMost
  decide +kernel

theorem model_four : cycles (model 22 8) 4 = 68 := by decide +kernel

theorem competitor_four : cycles competitor 4 = 67 := by decide +kernel

theorem competitor_diameter_exact : Fin.last 21 ∉ reachable competitor 0 7 := by decide +kernel

theorem five_witness : DiameterAtMost competitorFive 10 ∧
    Fin.last 17 ∉ reachable competitorFive 0 9 ∧
    cycles (model 18 10) 5 = 44 ∧ cycles competitorFive 5 = 42 := by
  unfold DiameterAtMost
  decide +kernel

theorem resolution : ¬Conjecture := by
  intro h
  have gap := (h 22 (by decide) 8 (by decide) (by decide) competitor
    competitor_diameter 4 (by decide) (by decide)).1
  rw [model_four, competitor_four] at gap
  omega

/-- info: 'SavchenkoDiameter.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'SavchenkoDiameter.five_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms five_witness

end SavchenkoDiameter
