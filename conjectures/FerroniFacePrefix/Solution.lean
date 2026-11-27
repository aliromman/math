module

public import conjectures.FerroniFacePrefix.Parity

@[expose] public section

namespace FerroniFacePrefix

open Finset

lemma parity_matroid (m : ℕ) (p : Bool) : IsMatroidOn (ground m p) (bases color (ground m p)) := by
  have h := enough_colors m p
  have f := full_isFace (show Full color (ground m p) (bases color (ground m p)) from
    ⟨_,Subset.rfl,h,rfl⟩)
  exact ⟨isMatroid_bases f.1,fun _ hb => (mem_powersetCard.mp (mem_filter.mp hb).1).1⟩

/-- Every basis has size two, and any two elements can be exchanged while the third is fixed. -/
theorem connected_rank_two (m : ℕ) (p : Bool) :
    (∀ b ∈ bases color (ground m p), b.card = 2) ∧
    ∀ x ∈ ground m p, ∀ y ∈ ground m p, ∃ q ∈ ground m p,
      {x,q} ∈ bases color (ground m p) ∧ {y,q} ∈ bases color (ground m p) := by
  refine ⟨fun _ hb => (mem_powersetCard.mp (mem_filter.mp hb).1).2,?_⟩
  intro x hx y hy
  obtain ⟨q,hq,hxq,hyq⟩ := third_color (enough_colors m p) (color x) (color y)
  exact ⟨q,hq,pair_mem.mpr ⟨hx,hq,hxq.symm⟩,pair_mem.mpr ⟨hy,hq,hyq.symm⟩⟩

theorem facet_difference (m : ℕ) :
    faceNumber (bases color (ground m false)) ((ground m false).card - 2) + 1 =
    faceNumber (bases color (ground m true)) ((ground m false).card - 2) := by
  conv_rhs => rw [ground_card m]
  rw [facet_number (enough_colors m false) duplicated,facet_number (enough_colors m true) duplicated,
    ground_card m, Nat.add_assoc,color_count]

theorem resolution : ¬ Conjecture := by
  rintro ⟨m,H⟩
  have he := H (Cell m) (Cell m) (ground m false) (ground m true) _ _
    (parity_matroid m false) (parity_matroid m true) (fun k hk => prefix_equal m k (by omega)) ((ground m false).card-2)
  have hd := facet_difference m
  omega

/-- info: 'FerroniFacePrefix.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end FerroniFacePrefix
