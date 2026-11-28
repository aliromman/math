module

public import conjectures.BajnokRestrictedMinimum.Statement

@[expose] public section
namespace BajnokRestrictedMinimum

/-- The subgroup of order twelve and the translate of Bajnok's seven-element example. -/
def witness : Finset (ZMod 444) :=
  {0, 37, 74, 111, 148, 185, 222, 259, 296, 333, 370, 407,
    1, 38, 149, 186, 223, 334, 371}

theorem witness_card : witness.card = 19 := by decide

theorem restricted_card : (BajnokRestrictedInverse.restricted 2 witness).card = 34 := by
  decide +kernel

theorem restrictedMinimum_le : restrictedMinimum 444 19 ≤ 34 := by
  apply csInf_le (OrderBot.bddBelow _)
  exact ⟨witness, witness_card, restricted_card⟩

end BajnokRestrictedMinimum
