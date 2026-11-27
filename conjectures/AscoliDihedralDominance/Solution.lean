module

public import conjectures.AscoliDihedralDominance.Quantitative
public import conjectures.AscoliDihedralDominance.Small

@[expose] public section
namespace AscoliDihedral

universe u

/-- Every generalized dihedral group in the conjecture has a strict product surplus. -/
theorem proved : Conjecture.{u} := by
  intro H _ _ _ ht
  by_cases hn : 32 ≤ Fintype.card H
  · exact generalized_dihedral_large H ht hn
  · exact small_of_models H (Nat.lt_of_not_ge hn) ht small_models_dominant

/-- info: 'AscoliDihedral.proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms proved

end AscoliDihedral
