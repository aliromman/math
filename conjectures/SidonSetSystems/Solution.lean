module

public import conjectures.SidonSetSystems.ErrorTerm
public import conjectures.SidonSetSystems.Asymptotic

public section
namespace SidonSetSystems

theorem resolution : Conjecture := resolution_of_sparse sparse_shapes

/-- info: 'SidonSetSystems.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end SidonSetSystems
