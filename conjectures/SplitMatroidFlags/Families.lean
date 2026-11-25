module

public import conjectures.SplitMatroidFlags.Tables
import Mathlib.Tactic

@[expose] public section

namespace SplitMatroidFlags

open Finset

def capacities (H : Lines) := H.image fun L => (L,2)

lemma intersection_two {X L : Finset G} (hx : X.card = 3) : (X ∩ L).card ≤ 2 ↔ ¬ X ⊆ L := by
  constructor
  · intro small sub
    rw [inter_eq_left.mpr sub,hx] at small
    omega
  · intro hs
    have diff : X ∩ L ≠ X := fun e => hs (inter_eq_left.mp e)
    have h := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left,diff⟩)
    omega

def ConnectedPairs (H : Lines) : Prop := ∀ i j : G, i = j ∨
  ∃ x y : G, x ≠ y ∧ i ≠ x ∧ i ≠ y ∧ j ≠ x ∧ j ≠ y ∧ allowed H {i,x,y} ∧ allowed H {j,x,y}

instance (H : Lines) : Decidable (ConnectedPairs H) := by unfold ConnectedPairs; infer_instance

lemma example_split {H : Lines} (sparse : ∀ L ∈ H, ∀ J ∈ H, L ≠ J → (L ∩ J).card ≤ 1)
    (proper : ∀ L ∈ H, 1 ≤ (univ \ L).card) (conn : ConnectedPairs H) :
    ConnectedSplit univ (bases H) := by
  refine ⟨⟨3,by decide,capacities H,?_,?_,?_⟩,univ_nonempty,?_⟩
  · intro h hh
    obtain ⟨L,hL,rfl⟩ := mem_image.mp hh
    refine ⟨subset_univ _,?_⟩
    change 3 ≤ (univ \ L).card + 2
    have := proper L hL
    omega
  · intro h hh g hg ne
    obtain ⟨L,hL,rfl⟩ := mem_image.mp hh
    obtain ⟨J,hJ,rfl⟩ := mem_image.mp hg
    have le := sparse L hL J hJ (fun e => ne (e ▸ rfl))
    change (L ∩ J).card + 3 ≤ 2 + 2
    omega
  · intro b
    rw [mem_bases]
    constructor
    · rintro ⟨hb,allowed⟩
      refine ⟨subset_univ _,hb,fun h hh => ?_⟩
      obtain ⟨L,hL,rfl⟩ := mem_image.mp hh
      exact (intersection_two hb).mpr (allowed _ hL)
    · rintro ⟨_,hb,cap⟩
      exact ⟨hb,fun L hL => (intersection_two hb).mp (cap (L,2) (mem_image_of_mem _ hL))⟩
  · intro i _ j _
    rcases conn i j with eq|⟨x,y,xy,ix,iy,jx,jy,hi,hj⟩
    · exact .inl eq
    · refine .inr ⟨{x,y},by simp [ix,iy],by simp [jx,jy],?_,?_⟩
      · exact mem_bases.mpr ⟨by simp [xy,ix,iy],hi⟩
      · exact mem_bases.mpr ⟨by simp [xy,jx,jy],hj⟩

lemma live_outside {H : Lines} (conn : ConnectedPairs H) {a : Three G}
    (hm : HasMatches (bases H) a.coords) (j : G) (hj : j ∉ a.coords) :
    ∃ i, Swap (bases H) a.coords i j := by
  have hjx : j ≠ a.x := fun he => hj (by simp [he,Three.coords])
  obtain eq | ⟨x,y,xy,jx,jy,_,_,h,_⟩ := conn j a.x
  · exact False.elim (hjx eq)
  · have base : {j,x,y} ∈ bases H := mem_bases.mpr ⟨by simp [jx,jy,xy],h⟩
    obtain ⟨f,hf⟩ := hm _ base
    have hit : j ∈ a.coords.image f := by rw [hf.image_eq]; simp
    obtain ⟨i,hi,fi⟩ := mem_image.mp hit
    rcases hf.permitted i hi with eq|sw
    · exact False.elim (hj ((eq.symm.trans fi) ▸ hi))
    · exact ⟨i,fi ▸ sw⟩

def matchTest (H : Lines) : Prop := ∀ a ∈ charts H,
  let N := (rows H a).masks
  ∀ c ∈ charts H, ∃ p ∈ perms c, (p.x = a.x ∨ N.x.testBit p.x.val = true) ∧
    (p.y = a.y ∨ N.y.testBit p.y.val = true) ∧ (p.z = a.z ∨ N.z.testBit p.z.val = true)

instance (H : Lines) : Decidable (matchTest H) := by unfold matchTest; infer_instance

lemma checked_matches {H : Lines} (h : matchTest H) : ∀ b ∈ bases H, HasMatches (bases H) b := by
  apply all_matches
  intro a ha c hc
  obtain ⟨p,hp,hx,hy,hz⟩ := h a ha c hc
  refine ⟨p,hp,?_,?_,?_⟩
  · simpa [rows,Three.masks,Three.map] using hx
  · simpa [rows,Three.masks,Three.map] using hy
  · simpa [rows,Three.masks,Three.map] using hz

end SplitMatroidFlags
