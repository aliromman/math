module

public import conjectures.AscoliDihedralDominance.WeightedEvents
public import conjectures.AscoliDihedralDominance.SubsetEvaluation
import Mathlib.Tactic.Abel

@[expose] public section
open Finset Equiv
namespace AscoliDihedral
namespace Dih
variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def common (g : Dih H) := missingProducts g ∩ missingQuotients g

private theorem reflection_common (a : H) : common (⟨true,a⟩ : Dih H) = missingProducts ⟨true,a⟩ := by
  apply inter_eq_left.mpr
  intro A hA
  have hp : avoids (productStep (⟨true,a⟩ : Dih H)) A :=
    (missing_product _ _).mp (mem_filter.mp hA).2
  apply mem_filter.mpr ∘ And.intro (mem_univ _)
  apply (missing_quotient _ _).mpr
  rintro ⟨b,x⟩ hx
  cases b
  · have hh := hp ⟨false,x⟩ hx
    change (⟨true,-x+a⟩ : Dih H) ∉ A at hh
    change (⟨true,a-x⟩ : Dih H) ∉ A
    simpa [sub_eq_add_neg,add_comm] using hh
  · change (⟨false,a-x⟩ : Dih H) ∉ A
    intro hy
    have hh := hp ⟨false,a-x⟩ hy
    change (⟨true,-(a-x)+a⟩ : Dih H) ∉ A at hh
    exact hh (by simpa using hx)

def rotationEdges (a x y : H) := decide (x+y=a ∨ x-y=a ∨ y-x=a)

omit [Fintype H] in
private theorem rotations_allowed (a : H) (A : Finset H) :
    permitted (rotationEdges a) (fun _ => true) A ↔
      avoids (fun x => a-x) A ∧ avoids (fun x => a+x) A := by
  simp only [permitted,rotationEdges,decide_eq_false_iff_not,true_and,implies_true,not_or]
  constructor
  · intro ha
    constructor <;> intro x hx hy
    · exact (ha x hx (a-x) hy).1 (by abel)
    · exact (ha x hx (a+x) hy).2.2 (by abel)
  · rintro ⟨h₁,h₂⟩ x hx y hy
    refine ⟨fun h => h₁ x hx (by rw [←h]; simpa [add_comm] using hy),?_,?_⟩
    · intro he
      apply h₂ y hy
      convert hx using 1
      rw [←he]
      abel_nf
    · intro he
      apply h₂ x hx
      convert hy using 1
      rw [←he]
      abel_nf

def halfColor : (Dih H → Bool) ≃ (H → Bool) × (H → Bool) where
  toFun f := (fun x => f ⟨false,x⟩, fun x => f ⟨true,x⟩)
  invFun f x := if x.reflection then f.2 x.position else f.1 x.position
  left_inv f := by funext ⟨b,x⟩; cases b <;> rfl
  right_inv _ := rfl

omit [AddCommGroup H] [DecidableEq H] in
private theorem halfWeight (B : ℕ) (f : Dih H→Bool) : colorWeight B f =
    colorWeight B (halfColor f).1 * colorWeight B (halfColor f).2 := by
  unfold colorWeight
  let e : Bool×H ≃ Dih H := ⟨fun v => ⟨v.1,v.2⟩,fun v => (v.reflection,v.position),fun _ => rfl,fun _ => rfl⟩
  rw [←e.prod_comp (fun x => if f x then B else 1),Fintype.prod_prod_type,Fintype.prod_bool]
  exact mul_comm _ _

def rotCheck (a : H) (f : H→Bool) :=
  coloringOK (fun x => a-x) f ∧ coloringOK (fun x => a+x) f

instance (a : H) (f : H→Bool) : Decidable (rotCheck a f) := by unfold rotCheck; infer_instance

omit [Fintype H] [DecidableEq H] in
private theorem common_checks (a : H) (f : Dih H→Bool) :
    coloringOK (productStep (⟨false,a⟩ : Dih H)) f ∧ coloringOK (quotientStep (⟨false,a⟩ : Dih H)) f ↔
       rotCheck a (halfColor f).1 ∧ coloringOK (fun x => a+x) (halfColor f).2 := by
  constructor
  · rintro ⟨hp,hq⟩
    refine ⟨⟨fun x => ?_,fun x => hq ⟨false,x⟩⟩, fun x => hq ⟨true,x⟩⟩
    have hh := hp ⟨false,x⟩
    change (!(f ⟨false,x⟩ && f ⟨false,-x+a⟩))=true at hh
    simpa [halfColor,sub_eq_add_neg,add_comm] using hh
  · rintro ⟨⟨hr,ht⟩,hs⟩
    constructor
    · rintro ⟨b,x⟩
      cases b
      · have hh := hr x
        change (!(f ⟨false,x⟩ && f ⟨false,-x+a⟩))=true
        simpa [halfColor,sub_eq_add_neg,add_comm] using hh
      · have hh := hs (x-a)
        change (!(f ⟨true,x⟩ && f ⟨true,x-a⟩))=true
        simpa [halfColor,Bool.and_comm] using hh
    · rintro ⟨b,x⟩
      cases b
      · exact ht x
      · exact hs x

private theorem eval_rotCheck (B : ℕ) (a : H) (xs : List H) (hn : xs.Nodup) (hu : xs.toFinset=univ) :
    countIndependent B (rotationEdges a) xs (fun _ => true) =
      ∑ f : H→Bool, if rotCheck a f then colorWeight B f else 0 := by
  rw [countIndependent_eq B _ xs hn,hu,powerset_univ]
  rw [←(bitsEquiv H).sum_comp (fun f => if rotCheck a f then colorWeight B f else 0)]
  apply sum_congr rfl
  intro A _
  have he : permitted (rotationEdges a) (fun _ => true) A ↔ rotCheck a (bitsEquiv H A) :=
    (rotations_allowed a A).trans (and_congr (avoids_bits _ _) (avoids_bits _ _))
  rw [bits_weight]
  by_cases h : permitted (rotationEdges a) (fun _ => true) A
  · simp only [h,he.mp h,ite_true]
  · have nh : ¬rotCheck a ((bitsEquiv H) A) := fun hr => h (he.mpr hr)
    simp only [h,nh,ite_false]

/-- A reflection obstructs a product only when it also obstructs a quotient.
For a rotation the common obstruction separates into two restrictions on H. -/
def evaluateCommon (B : ℕ) (xs : List H) (g : Dih H) : ℕ :=
  if g.reflection then evaluatePerm B (productStep g) else
    countIndependent B (rotationEdges g.position) xs (fun _ => true) *
      evaluatePerm B (Equiv.addLeft g.position)

theorem evaluateCommon_eq (B : ℕ) (xs : List H) (hn : xs.Nodup) (hu : xs.toFinset=univ) (g : Dih H) :
    evaluateCommon B xs g = familyWeight B (common g) := by
  obtain ⟨b,a⟩ := g
  cases b
  · change countIndependent B (rotationEdges a) xs _ * evaluatePerm B (Equiv.addLeft a) = _
    rw [eval_rotCheck B a xs hn hu,evaluatePerm_eq]
    symm
    rw [weight_by_equiv B (common (⟨false,a⟩ : Dih H)) (fun f =>
      rotCheck a (halfColor f).1 ∧ coloringOK (fun x => a+x) (halfColor f).2) (by
        intro A
        rw [←common_checks]
        simp [common,missingProducts,missingQuotients,missing_product,missing_quotient,avoids_bits])]
    rw [←halfColor.symm.sum_comp,Fintype.sum_prod_type]
    unfold weightPerm
    rw [sum_mul]
    apply sum_congr rfl
    intro r _
    rw [mul_sum]
    apply sum_congr rfl
    intro s _
    rw [halfWeight,halfColor.apply_symm_apply]
    by_cases hr : rotCheck a r <;> by_cases hs : coloringOK (fun x => a+x) s <;>
      simp [hr,hs]
  · rw [reflection_common,eval_missing_products]
    rfl

end Dih
end AscoliDihedral
