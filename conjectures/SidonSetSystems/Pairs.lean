module
public import conjectures.SidonSetSystems.Upper

public section
namespace SidonSetSystems
open Finset
open scoped Classical Pointwise

private def two (a : ℕ) : Finset ℕ := {0,a}
private theorem two_zero (a : ℕ) : 0∈two a := by simp [two]
private theorem two_inj {a b : ℕ} (h : two a=two b) : a=b := by
  have ha : a∈two b := h ▸ (show a∈two a by simp [two])
  have hb : b∈two a := h.symm ▸ (show b∈two b by simp [two])
  simp only [two,mem_insert,mem_singleton] at ha hb
  omega

private theorem two_sums (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (h : two a+two b=two c+two d) : (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have terms (x y z : ℕ) : z∈two x+two y ↔ z=0 ∨ z=x ∨ z=y ∨ z=x+y := by
    constructor
    · intro hz
      obtain ⟨v,hv,w,hw,rfl⟩ := mem_add.mp hz
      simp only [two,mem_insert,mem_singleton] at hv hw
      omega
    · rintro (hz|hz|hz|hz) <;> subst z
      · exact mem_add.mpr ⟨0,two_zero _,0,two_zero _,rfl⟩
      · exact mem_add.mpr ⟨x,by simp [two],0,two_zero _,Nat.add_zero _⟩
      · exact mem_add.mpr ⟨0,two_zero _,y,by simp [two],Nat.zero_add _⟩
      · exact mem_add.mpr ⟨x,by simp [two],y,by simp [two],rfl⟩
  have eq (x : ℕ) := (terms a b x).symm.trans ((Iff.of_eq (congrArg (fun t => x∈t) h)).trans (terms c d x))
  have e₁ := eq a
  have e₂ := eq b
  have e₃ := eq c
  have e₄ := eq d
  have e₅ := eq (a+b)
  have e₆ := eq (c+d)
  omega

/-- The two endpoint families attain the upper bound for pairs. -/
theorem pairs_exact {n : ℕ} (hn : 2≤n) : extremal 2 n=upperBound 2 n := by
  let left (a : ℕ) := shift 1 (two a)
  let right (a : ℕ) := shift (n-a) (two a)
  let L := (Icc 1 (n-1)).image left
  let R := (Icc 1 (n-2)).image right
  let F := L∪R
  have injL : Function.Injective left := fun _ _ h => two_inj (shift_inj 1 h)
  have injR : Function.Injective right := fun _ _ h => two_inj (shift_rigid (two_zero _) (two_zero _) h).2
  have dis : Disjoint L R := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,_,h₁⟩ := mem_image.mp hx
    obtain ⟨b,hb,h₂⟩ := mem_image.mp hy
    have h := (shift_rigid (two_zero _) (two_zero _) (h₁.trans h₂.symm)).1
    have lo := (mem_Icc.mp hb).2
    omega
  have card : F.card=upperBound 2 n := by
    dsimp only [F,L,R]
    rw [card_union_of_disjoint dis,card_image_of_injective _ injL,card_image_of_injective _ injR]
    simp [upperBound,Nat.card_Icc]
  have form {X} (hX : X∈F) : ∃ a x : ℕ, 0<a ∧ 0<x ∧ x+a≤n ∧ (x=1 ∨ x+a=n) ∧ X=shift x (two a) := by
    rcases mem_union.mp hX with l|r
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp l
      obtain ⟨a₀,a₁⟩ := mem_Icc.mp ha
      exact ⟨a,1,a₀,by decide,by omega,Or.inl rfl,rfl⟩
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp r
      obtain ⟨a₀,a₁⟩ := mem_Icc.mp ha
      exact ⟨a,n-a,a₀,by omega,by omega,Or.inr (by omega),rfl⟩
  apply le_antisymm (extremal_upper (by decide) (by omega))
  rw [←card]
  apply le_extremal
  · intro X hX
    obtain ⟨a,x,ha,hx,hax,_,rfl⟩ := form hX
    apply mem_powersetCard.mpr
    refine ⟨?_,?_⟩
    · intro t ht
      obtain ⟨v,hv,rfl⟩ := mem_image.mp ht
      simp only [two,mem_insert,mem_singleton] at hv
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    · rw [card_shift]
      simp [two,Ne.symm (ne_of_gt ha)]
  · intro A ha B hb C hc E he eq
    obtain ⟨a,x,ap,_,_,xe,rfl⟩ := form ha
    obtain ⟨b,y,bp,_,_,ye,rfl⟩ := form hb
    obtain ⟨c,z,cp,_,_,ze,rfl⟩ := form hc
    obtain ⟨d,w,dp,_,_,we,rfl⟩ := form he
    rw [shift_add,shift_add] at eq
    have zero (i j : ℕ) : 0∈two i+two j := mem_add.mpr ⟨0,two_zero _,0,two_zero _,rfl⟩
    obtain ⟨sum,gaps⟩ := shift_rigid (zero _ _) (zero _ _) eq
    rcases two_sums a b c d ap bp cp dp gaps with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have choices : (x=z ∧ y=w) ∨ (a=b ∧ x=w ∧ y=z) := by omega
      rcases choices with ⟨rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> simp
    · have choices : (x=w ∧ y=z) ∨ (a=b ∧ x=z ∧ y=w) := by omega
      rcases choices with ⟨rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> simp

end SidonSetSystems
