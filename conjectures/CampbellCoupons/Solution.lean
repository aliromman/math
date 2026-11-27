module

public import conjectures.CampbellCoupons.Asymptotic
public import conjectures.CampbellCoupons.Tails
import Mathlib.Tactic.NormNum

@[expose] public section
namespace CampbellCoupons

theorem four_draws : success 2 2 4 = 3 / 8 ∧ success 1 3 4 = 4 / 9 := by
  have ha : winning 2 2 4 = 6 := by decide +kernel
  have hb : winning 1 3 4 = 36 := by decide +kernel
  norm_num [success, ha, hb]

theorem five_draws : success 2 2 5 = 5 / 8 ∧ success 1 3 5 = 50 / 81 := by
  have ha : winning 2 2 5 = 20 := by decide +kernel
  have hb : winning 1 3 5 = 150 := by decide +kernel
  norm_num [success, ha, hb]

theorem resolution : ¬Conjecture := by
  intro h
  have hn := h 2 2 4 (by decide) (by decide) (by decide) (by decide)
  change success 1 3 4 ≤ success 2 2 4 at hn
  norm_num [four_draws.1, four_draws.2] at hn

/--
info: 'CampbellCoupons.resolution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms resolution

/--
info: 'CampbellCoupons.square_frontier_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms square_frontier_limit

/--
info: 'CampbellCoupons.unbounded_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms unbounded_ratio

/--
info: 'CampbellCoupons.eventual_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eventual_comparison

end CampbellCoupons
