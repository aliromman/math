module

public import conjectures.MarkovNearestFour.Coefficient
public import conjectures.MarkovNearestFour.Convergents
public import Mathlib.Util.AssertNoSorry

@[expose] public section
namespace MarkovNearestFour

/-- Evans, Veselov and Winn, Conjecture 8.4. -/
theorem resolution : Conjecture := by
  intro ds pos
  rcases hn : continuants ds with ⟨⟨p,q⟩,b,a⟩
  intro ha hab
  obtain ⟨cop,hw⟩ := convergent_location pos hn ha
  split at hw <;> rename_i parity
  · simpa only [ite_eq_left parity] using coefficient_four a b q (b-p) ha hab cop hw
  · simpa only [ite_eq_right parity] using coefficient_four a b (a-q) p ha hab cop hw

end MarkovNearestFour

/-- info: 'MarkovNearestFour.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MarkovNearestFour.resolution
assert_no_sorry MarkovNearestFour.resolution
