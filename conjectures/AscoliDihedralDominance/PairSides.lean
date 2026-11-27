module

public import conjectures.AscoliDihedralDominance.PairEvaluation

@[expose] public section
open Finset
namespace AscoliDihedral
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Two commuting involutions give squares with opposite pairs of vertices. -/
noncomputable def commutingSides {g h : G} (g₀ : g≠1) (h₀ : h≠1)
    (g₂ : g*g=1) (h₂ : h*h=1) (hc : Commute g h) : TwoMatchings g h := by
  classical
  let E (x : G) : Finset G := {x,(g*h)*x}
  let O (x : G) : Finset G := {g*x,h*x}
  let index := Fintype.equivFin (Finset G)
  have swap (x : G) : g*(h*x)=h*(g*x) := by rw [←mul_assoc,←mul_assoc,hc.eq]
  have gg (x : G) : g*(g*x)=x := by rw [←mul_assoc,g₂,one_mul]
  have hh (x : G) : h*(h*x)=x := by rw [←mul_assoc,h₂,one_mul]
  have Eg (x : G) : E (g*x)=O x := by
    simp only [E,O,mul_assoc,swap (g*x),gg]
  have Eh (x : G) : E (h*x)=O x := by
    simp only [E,O,mul_assoc,hh,pair_comm (h*x)]
  have Og (x : G) : O (g*x)=E x := by simp only [E,O,gg,mul_assoc,swap]
  have Oh (x : G) : O (h*x)=E x := by simp only [E,O,hh,mul_assoc,pair_comm x]
  have diff (x : G) : E x≠O x := by
    intro he
    have hx : x∈O x := he ▸ mem_insert_self _ _
    simp only [O,mem_insert,mem_singleton] at hx
    rcases hx with hx|hx
    · exact g₀ (mul_right_cancel (show g*x=1*x by simpa using hx.symm))
    · exact h₀ (mul_right_cancel (show h*x=1*x by simpa using hx.symm))
  have flip (x : G) : decide (index (O x) < index (E x)) = !decide (index (E x) < index (O x)) := by
    have hn : index (E x)≠index (O x) := fun he => diff x (index.injective he)
    rcases lt_or_gt_of_ne hn with h|h <;> simp [h,not_lt_of_gt h]
  refine ⟨fun x => decide (index (E x) < index (O x)),g₂,h₂,?_,?_⟩
  · intro x
    rw [Eg,Og]
    exact flip x
  · intro x
    rw [Eh,Oh]
    exact flip x

namespace Dih
variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
theorem commuting_rotation (g h : Dih H) (b : g.reflection=false) (g₂ : g*g=1) :
    Commute g h := by
  obtain ⟨r,a⟩ := g
  change r=false at b
  subst r
  have ha : a+a=0 := congrArg Dih.position g₂
  obtain ⟨s,t⟩ := h
  cases s
  · change Dih.mk false (a+t) = Dih.mk false (t+a)
    rw [add_comm]
  · change Dih.mk true (a+t) = Dih.mk true (t-a)
    rw [sub_eq_add_neg,neg_eq_iff_add_eq_zero.mpr ha,add_comm]

noncomputable def pairSides {g h : Dih H} (g₀ : g≠1) (h₀ : h≠1) (g₂ : g*g=1) (h₂ : h*h=1) :
    TwoMatchings g h := by
  by_cases bg : g.reflection=false
  · exact commutingSides g₀ h₀ g₂ h₂ (commuting_rotation g h bg g₂)
  by_cases bh : h.reflection=false
  · exact commutingSides g₀ h₀ g₂ h₂ (commuting_rotation h g bh h₂).symm
  have flip (t : Dih H) (ht : t.reflection≠false) (x : Dih H) : (t*x).reflection = !x.reflection := by
    have := Bool.eq_true_of_not_eq_false ht
    change (t.reflection ^^ x.reflection) = _
    simp [this]
  exact ⟨Dih.reflection,g₂,h₂,flip _ bg,flip _ bh⟩

end Dih
end AscoliDihedral
