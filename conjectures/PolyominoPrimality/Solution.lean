module

public import conjectures.PolyominoPrimality.Nonprime
public import conjectures.PolyominoPrimality.Walks

public section
namespace PolyominoPrimality

/-- The same thirteen cells disprove the conjecture over every field. -/
theorem resolution (K : Type*) [Field K] : ¬ Conjecture K :=
  fun h => nonprime K ((h exampleCells connectedExample).mpr noZigzag)

/-- info: 'PolyominoPrimality.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end PolyominoPrimality
