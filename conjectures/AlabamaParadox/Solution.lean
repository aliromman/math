module

public import conjectures.AlabamaParadox.Bound
public import conjectures.AlabamaParadox.Limit

open Filter Finset
namespace AlabamaParadox

/-- The upper bound on the limiting probability that any state loses a seat. -/
public theorem resolution : Conjecture := by
  intro m p hp hs hi
  rcases subsingleton_or_nontrivial (Fin m) with h|h
  · refine ⟨0, frequency_subsingleton p ▸ tendsto_const_nhds, sub_nonneg.mpr ?_⟩
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    linarith [Real.add_one_le_exp (1:ℝ)]
  · have : NeZero m := ⟨by rintro rfl; exact not_nontrivial (Fin 0) h⟩
    have hlt (i : Fin m) : p i < 1 := by
      obtain ⟨j,hj⟩ := exists_ne i
      have : Nonempty (Other i) := ⟨j,hj⟩
      have e := (Equiv.optionSubtypeNe i).sum_comp p
      rw [Fintype.sum_option,hs] at e
      have pos : 0 < ∑ j : Other i, p j := sum_pos (fun j _ => hp j) univ_nonempty
      change p i + ∑ j : Other i, p j = 1 at e
      linarith
    obtain ⟨q,hq⟩ := frequency_exists p hp hs hi
    exact ⟨q,hq,frequency_bound p hp hlt hs hi hq⟩

/-- info: 'AlabamaParadox.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end AlabamaParadox
