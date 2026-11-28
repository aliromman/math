module

public import conjectures.BajnokRestrictedMinimum.Ordinary
public import conjectures.BajnokRestrictedMinimum.Witness

@[expose] public section
namespace BajnokRestrictedMinimum
open scoped Pointwise

/-- A set of nineteen residues disproves Bajnok’s twofold restricted-sumset formula. -/
theorem conjecture_false : ¬ Conjecture := by
  intro claim
  have bound : 35 ≤ ordinaryMinimum 444 19 := by
    unfold ordinaryMinimum
    refine le_csInf ?_ ?_
    · exact ⟨(witness + witness).card, witness, witness_card, rfl⟩
    rintro r ⟨A, hA, rfl⟩
    exact ordinary_lower A hA
  have formula := claim 444 19 (by decide) (by decide) (by decide)
  have h₁ : ¬ 2 ∣ 19 := by decide
  have h₂ : ¬ (2 * 19 - 2) ∣ 444 := by decide
  simp [h₁, h₂, min_eq_right bound] at formula
  have upper := restrictedMinimum_le
  rw [formula] at upper
  exact (by decide : ¬ 35 ≤ 34) upper

end BajnokRestrictedMinimum
