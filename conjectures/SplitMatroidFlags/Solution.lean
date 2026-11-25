module

public import conjectures.SplitMatroidFlags.Result
public import conjectures.SplitMatroidFlags.CountsA
public import conjectures.SplitMatroidFlags.CountsB

namespace SplitMatroidFlags

/-- The ordinary face vector does not determine the flag face vector, even in rank three. -/
public theorem resolution : ¬ Conjecture := different_flags censusA censusB

/-- info: 'SplitMatroidFlags.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end SplitMatroidFlags
