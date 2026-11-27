module

public import conjectures.AscoliDihedralDominance.Moments
import Mathlib.Tactic.Abel

@[expose] public section
open Finset
namespace AscoliDihedral
namespace Dih
variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

private def pairEquiv (H : Type*) : Dih H ≃ Bool × H where
  toFun x := (x.reflection,x.position)
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card (H : Type*) [Fintype H] : Fintype.card (Dih H) = 2 * Fintype.card H := by
  rw [Fintype.card_congr (pairEquiv H), Fintype.card_prod,Fintype.card_bool]

def twoTorsion (H : Type*) [AddCommGroup H] : AddSubgroup H :=
  (2 • AddMonoidHom.id H).ker

omit [Fintype H] [DecidableEq H] in
theorem mem_twoTorsion (x : H) : x ∈ twoTorsion H ↔ x+x=0 := by
  simp [twoTorsion,two_nsmul]

omit [Fintype H] [DecidableEq H] in
theorem center_iff (ht : ∃ h : H, h+h≠0) (x : Dih H) :
    x ∈ Subgroup.center (Dih H) ↔ x.reflection=false ∧ x.position∈twoTorsion H := by
  obtain ⟨b,a⟩ := x
  rcases ht with ⟨h,hh⟩
  cases b
  · simp only [true_and,mem_twoTorsion,Subgroup.mem_center_iff]
    constructor
    · intro hc
      have he := congrArg Dih.position (hc ⟨true,0⟩)
      change 0-a = a+0 at he
      simpa using neg_eq_iff_add_eq_zero.mp (by simpa using he : -a=a)
    · intro ha y
      obtain ⟨b,y⟩ := y
      cases b
      · change Dih.mk false (y+a) = Dih.mk false (a+y)
        rw [add_comm]
      · change Dih.mk true (y-a) = Dih.mk true (a+y)
        have he := neg_eq_iff_add_eq_zero.mpr ha
        simp [sub_eq_add_neg,he,add_comm]
  · simp only [Bool.true_eq_false, false_and,iff_false,Subgroup.mem_center_iff]
    intro hc
    have he := congrArg Dih.position (hc ⟨false,h⟩)
    change h+a = a-h at he
    apply hh
    have : h = -h := add_right_cancel (he.trans (by abel : a-h = -h+a))
    simpa using eq_neg_iff_add_eq_zero.mp this

omit [Fintype H] [DecidableEq H] in
theorem exists_moved (ht : ∃ h : H, 3 ≤ addOrderOf h) : ∃ h : H, h+h≠0 := by
  obtain ⟨h,hh⟩ := ht
  refine ⟨h,fun he => ?_⟩
  have hd : addOrderOf h ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by simpa [two_nsmul] using he)
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

noncomputable def centerEquiv (hm : ∃ h : H, h+h≠0) : Subgroup.center (Dih H) ≃ twoTorsion H where
  toFun x := ⟨x.val.position,((center_iff hm _).mp x.property).2⟩
  invFun x := ⟨⟨false,x.val⟩,(center_iff hm _).mpr ⟨rfl,x.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨⟨a,b⟩,hx⟩ := x
    have ha := ((center_iff hm _).mp hx).1
    change a=false at ha
    subst a
    rfl
  right_inv _ := rfl

omit [DecidableEq H] in
theorem twoTorsion_bound (hm : ∃ h : H, h+h≠0) : 2 * Nat.card (twoTorsion H) ≤ Fintype.card H := by
  let K := twoTorsion H
  have ht : K ≠ ⊤ := by
    obtain ⟨h,hh⟩ := hm
    intro e
    have hK : h ∈ K := by rw [e]; trivial
    exact hh ((mem_twoTorsion _).mp hK)
  have hi : 2 ≤ K.index := by
    have h₁ := K.index_ne_zero
    have h₂ : K.index ≠ 1 := fun h => ht (AddSubgroup.index_eq_one.mp h)
    omega
  rw [←Nat.card_eq_fintype_card,←K.index_mul_card]
  exact Nat.mul_le_mul_right _ hi

private def invWithOne : Finset (Dih H) := univ.filter fun x => x*x=1

private theorem one_in : (1 : Dih H) ∈ invWithOne := by simp [invWithOne]

private theorem erase_one :
    involutions (Dih H) = invWithOne.erase 1 := by ext; simp [involutions,invWithOne]

private def invEquiv : invWithOne (H := H) ≃ twoTorsion H ⊕ H where
  toFun x := match x with
    | ⟨⟨false,a⟩,hx⟩ => Sum.inl ⟨a,(mem_twoTorsion a).mpr (congrArg Dih.position (mem_filter.mp hx).2)⟩
    | ⟨⟨true,a⟩,_⟩ => Sum.inr a
  invFun x := match x with
    | .inl a => ⟨⟨false,a.val⟩,by
        apply mem_filter.mpr ∘ And.intro (mem_univ _)
        change Dih.mk false (a.val+a.val) = Dih.mk false 0
        rw [(mem_twoTorsion _).mp a.property]⟩
    | .inr a => ⟨⟨true,a⟩,by
        apply mem_filter.mpr ∘ And.intro (mem_univ _)
        change Dih.mk false (a-a) = Dih.mk false 0
        rw [sub_self]⟩
  left_inv x := by obtain ⟨⟨b,a⟩,hx⟩ := x; cases b <;> rfl
  right_inv x := by cases x <;> rfl

theorem involutions_card :
    (involutions (Dih H)).card + 1 = Fintype.card H + Nat.card (twoTorsion H) := by
  rw [erase_one,Finset.card_erase_add_one one_in,←Fintype.card_coe,←Nat.card_eq_fintype_card,
    Nat.card_congr invEquiv,Nat.card_sum,Nat.card_eq_fintype_card (α := H),add_comm]

end Dih
end AscoliDihedral
