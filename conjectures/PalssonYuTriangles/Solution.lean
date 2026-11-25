module

public import conjectures.PalssonYuTriangles.Realizations
public import conjectures.PalssonYuTriangles.UpperBound

open Complex Finset
namespace PalssonYu
noncomputable section

private theorem seven {S : Finset ℂ} (order : S.card=7)
    (few : (triangleTypes S).card≤4) : RegularHeptagon S := by
  let e := (Finset.equivFinOfCardEq order).symm
  let p (i : Vertex) : ℂ := e i
  have inj : Function.Injective p := Subtype.val_injective.comp e.injective
  have pts : univ.image p=S := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact (e i).property
    · intro hv
      obtain ⟨i,hi⟩ := e.surjective ⟨v,hv⟩
      exact mem_image.mpr ⟨i,mem_univ _,congrArg Subtype.val hi⟩
  rw [←pts]
  apply regular_of_classification inj
  refine ⟨triangleTypes S,few,fun i j k ij ik jk => ?_⟩
  have h : triangleSides (fun i j => D (p i) (p j)) i j k=triangle (p i) (p j) (p k) := by
    unfold triangleSides triangle
    rw [D_comm (p k) (p i)]
    exact congrArg (fun m => D (p i) (p j) ::ₘ m) (Multiset.cons_swap ..)
  rw [h]
  exact mem_types.mpr ⟨_,(e i).property,_,(e j).property,_,(e k).property,
    inj.ne ij,inj.ne jk,inj.ne ik.symm,rfl⟩

private theorem all_bound {A : Set ℂ} (four : (allTypes A).encard=4) : A.encard≤7 := by
  classical
  have ft : (allTypes A).Finite := Set.finite_of_encard_le_coe (k:=4) four.le
  have bound (P : Finset ℂ) (sub : (P : Set ℂ) ⊆ A) : P.card≤7 := by
    apply upper_of_seven
    intro U hU size
    apply seven size
    have inc : triangleTypes U ⊆ ft.toFinset := by
      intro m hm
      obtain ⟨a,ha,b,hb,c,hc,h⟩ := mem_types.mp hm
      exact ft.mem_toFinset.mpr ⟨a,sub (hU ha),b,sub (hU hb),c,sub (hU hc),h⟩
    have tc : ft.toFinset.card=4 := by
      have e := Set.encard_coe_eq_coe_finsetCard ft.toFinset
      rw [ft.coe_toFinset,four] at e
      exact_mod_cast e.symm
    exact (card_le_card inc).trans tc.le
  have finite : A.Finite := by
    by_contra inf
    obtain ⟨P,sub,size⟩ := Set.Infinite.exists_subset_card_eq inf 8
    have := bound P sub
    omega
  rw [←finite.coe_toFinset,Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast bound finite.toFinset (by simp)

public theorem resolution : Conjecture := by
  classical
  let r := Complex.exp (2*Real.pi*Complex.I/7)
  have root : IsPrimitiveRoot r 7 := Complex.isPrimitiveRoot_exp 7 (by decide)
  let S := univ.image fun i : Fin 7 => (0:ℂ)+1*r^i.val
  have regular : RegularHeptagon S := ⟨0,1,r,one_ne_zero,root,rfl⟩
  refine ⟨⟨S,regular_size_types regular⟩,?_,fun T => ⟨fun h => seven h.1 h.2.le,
    regular_size_types⟩⟩
  exact fun _ => all_bound

/-- info: 'PalssonYu.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end
end PalssonYu
