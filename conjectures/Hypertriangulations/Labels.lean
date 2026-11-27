module

public import conjectures.Hypertriangulations.SignedAreas
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace Hypertriangulations
open Finset
variable {α : Type*} [DecidableEq α] {I J K : Finset α}

noncomputable def average {α : Type*} (P : α→Plane) (k : ℕ) (I : Finset α) : Plane :=
  (k : ℝ)⁻¹ • ∑ i ∈ I,P i

/-- The geometric edge exchanges one point and retains every other point. -/
def Exchange (I J : Finset α) : Prop := ∃ U a b, a∉U ∧ b∉U ∧ a≠b ∧ I=insert a U ∧ J=insert b U

theorem Exchange.symm (h : Exchange I J) : Exchange J I := by
  obtain ⟨U,a,b,au,bu,ab,rfl,rfl⟩ := h
  exact ⟨U,b,a,bu,au,ab.symm,rfl,rfl⟩

theorem Exchange.card_eq (h : Exchange I J) : I.card=J.card := by
  obtain ⟨U,a,b,au,bu,_,rfl,rfl⟩ := h
  simp [au,bu]

theorem Exchange.ne (h : Exchange I J) : I≠J := by
  obtain ⟨U,a,b,au,_,ab,rfl,rfl⟩ := h
  intro eq
  have m : a∈insert b U := eq ▸ mem_insert_self a U
  simp [au,ab] at m

theorem Exchange.unique_loss (h : Exchange I J) {a b : α} (ai : a∈I) (aj : a∉J) (bi : b∈I) (bj : b∉J) : a=b := by
  obtain ⟨U,x,y,_,_,_,rfl,rfl⟩ := h
  grind

theorem exchange_iff (cards : I.card=J.card) : Exchange I J ↔ (I∩J).card+1=I.card := by
  constructor
  · rintro ⟨U,a,b,au,bu,ab,rfl,rfl⟩
    have eq : insert a U∩insert b U=U := by ext; grind
    simp [eq,au]
  · intro h
    have ci : (I\J).card=1 := by rw [card_sdiff,inter_comm J I];omega
    have cj : (J\I).card=1 := by rw [card_sdiff];omega
    obtain ⟨a,ea⟩ := card_eq_one.mp ci
    obtain ⟨b,eb⟩ := card_eq_one.mp cj
    have ai : a∈I\J := ea ▸ mem_singleton_self a
    have bj : b∈J\I := eb ▸ mem_singleton_self b
    refine ⟨I∩J,a,b,by grind,by grind,by grind,?_,?_⟩
    · ext x
      have fact : x∈I\J ↔ x=a := by rw [ea,mem_singleton]
      grind
    · ext x
      have fact : x∈J\I ↔ x=b := by rw [eb,mem_singleton]
      grind

/-- The first three labels are in cyclic order, with the missing point indexing each black vertex. -/
def WhiteLabels (I J K : Finset α) : Prop := ∃ U a b c, a∉U ∧ b∉U ∧ c∉U ∧ a≠b ∧ a≠c ∧ b≠c ∧
  I=insert a U ∧ J=insert b U ∧ K=insert c U

def BlackLabels (I J K : Finset α) : Prop := ∃ X a b c, a∉X ∧ b∉X ∧ c∉X ∧ a≠b ∧ a≠c ∧ b≠c ∧
  I=insert b (insert c X) ∧ J=insert c (insert a X) ∧ K=insert a (insert b X)

theorem classify_triangle (ij : Exchange I J) (jk : Exchange J K) (ki : Exchange K I) :
    WhiteLabels I J K ∨ BlackLabels I J K := by
  obtain ⟨U,a,b,au,bu,ab,rfl,rfl⟩ := ij
  have size : K.card=U.card+1 := by simpa [au] using ki.card_eq
  by_cases sub : U⊆K
  · left
    have one : (K\U).card=1 := by rw [card_sdiff_of_subset sub,size];omega
    obtain ⟨c,e⟩ := card_eq_one.mp one
    have ci : c∈K\U := e ▸ mem_singleton_self c
    have eq : K=insert c U := by
      ext x
      have : x∈K\U ↔ x=c := by rw [e,mem_singleton]
      grind
    exact ⟨U,a,b,c,au,bu,by grind,ab,(by have :=ki.ne;grind),(by have := jk.ne;grind),rfl,rfl,eq⟩
  · right
    obtain ⟨c,cu,ck⟩ := not_subset.mp sub
    have contain {x : α} (hx : x∈insert a U ∨ x∈insert b U) (xc : x≠c) : x∈K := by
      by_contra miss
      rcases hx with m|m
      · exact xc (ki.symm.unique_loss m miss (mem_insert_of_mem cu) ck)
      · exact xc (jk.unique_loss m miss (mem_insert_of_mem cu) ck)
    have ac : a≠c := by grind
    have bc : b≠c := by grind
    have Eq : insert b (insert a (U.erase c))=K := by
      apply eq_of_subset_of_card_le
      · intro x hx
        apply contain (by grind)
        grind
      · simp [au,bu,ab.symm,ac,bc,card_erase_of_mem cu,size]
        have := card_pos.mpr ⟨c,cu⟩;omega
    refine ⟨U.erase c,b,a,c,by grind,by grind,by simp,ab.symm,bc,ac,?_,?_,Eq.symm⟩
    · rw [insert_erase cu]
    · rw [insert_comm c b,insert_erase cu]

end Hypertriangulations
