module

public import conjectures.MatrixWidth.TailRate

@[expose] public section
namespace MatrixWidth

theorem resolution : Conjecture := fun _ _ hd hk => recurrent hd hk

/-- info: 'MatrixWidth.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'MatrixWidth.width_tail_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms width_tail_rate

end MatrixWidth
