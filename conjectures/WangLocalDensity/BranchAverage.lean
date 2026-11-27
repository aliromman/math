module

public import conjectures.WangLocalDensity.Branches
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

@[expose] public section
namespace WangLocalDensity
open Finset
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private noncomputable def choices (G : SimpleGraph V) (S A : Finset V) : Finset (Finset V) :=
  A.powerset.filter fun X ↦ Conn G (S∪X)

omit [Fintype V] in
private theorem choices_mem {S A X : Finset V} :
    X∈choices G S A ↔ X⊆A ∧ Conn G (S∪X) := by
  simp [choices]

omit [Fintype V] in
private theorem choices_pos {S : Finset V} (hS : Conn G S) (A : Finset V) :
    0<(choices G S A).card :=
  card_pos.mpr ⟨∅,choices_mem.mpr ⟨empty_subset _,by simpa using hS⟩⟩

private def join (S : Finset V) (P : Finset V × Finset V) := S∪P.1∪P.2

omit [Fintype V] in
private theorem recover {S A B X Y : Finset V}
    (dSA : Disjoint S A) (dSB : Disjoint S B) (dAB : Disjoint A B)
    (hX : X⊆A) (hY : Y⊆B) : (S∪X∪Y)∩A=X ∧ (S∪X∪Y)∩B=Y := by
  have dsA := Finset.disjoint_left.mp dSA
  have dsB := Finset.disjoint_left.mp dSB
  have daB := Finset.disjoint_left.mp dAB
  constructor <;> ext x <;> simp only [mem_inter,mem_union] <;> grind

omit [Fintype V] in
private theorem join_injective {S A B : Finset V}
    (dSA : Disjoint S A) (dSB : Disjoint S B) (dAB : Disjoint A B) :
    Set.InjOn (join S) ((choices G S A ×ˢ choices G S B : Finset _) : Set _) := by
  rintro ⟨X,Y⟩ hi ⟨X',Y'⟩ hj eq
  obtain ⟨x,y⟩ := Finset.mem_product.mp hi
  obtain ⟨x',y'⟩ := Finset.mem_product.mp hj
  have h := recover dSA dSB dAB (choices_mem.mp x).1 (choices_mem.mp y).1
  have h' := recover dSA dSB dAB (choices_mem.mp x').1 (choices_mem.mp y').1
  have ea := congrArg (·∩A) eq
  have eb := congrArg (·∩B) eq
  exact Prod.ext (h.1.symm.trans (ea.trans h'.1)) (h.2.symm.trans (eb.trans h'.2))

private theorem product_family {S A B : Finset V} (hs : Conn G S) (all : S∪A∪B=univ)
    (sep : ∀ a∈A,∀ b∈B,¬G.Adj a b) :
    (subtrees G).filter (fun U => S⊆U) =
      ((choices G S A) ×ˢ (choices G S B)).image (join S) := by
  classical
  ext U
  simp only [mem_filter,subtrees,mem_powerset,subset_univ,true_and,mem_image,Prod.exists,
    mem_product,choices_mem, join]
  constructor
  · rintro ⟨hU,hSU⟩
    have eq : S∪(U∩A)∪(U∩B)=U := by
      ext x
      have origin : x∈S∪A∪B := all ▸ mem_univ x
      simp only [mem_union,mem_inter] at *
      grind
    have split := (connected_split (A:=U∩A) (B:=U∩B) hs
      (fun _ hx _ hy => sep _ (mem_inter.mp hx).2 _ (mem_inter.mp hy).2)).mp (by rw [eq]; exact hU)
    exact ⟨U∩A,U∩B,⟨⟨inter_subset_right,split.1⟩,⟨inter_subset_right,split.2⟩⟩,eq⟩
  · rintro ⟨X,Y,⟨⟨hx,cx⟩,⟨hy,cy⟩⟩,rfl⟩
    exact ⟨(connected_split hs (fun _ h _ j => sep _ (hx h) _ (hy j))).mpr ⟨cx,cy⟩,
      subset_union_left.trans subset_union_left⟩

omit [Fintype V] in
private theorem join_extra {S A B X Y : Finset V}
    (dSA : Disjoint S A) (dSB : Disjoint S B) (dAB : Disjoint A B)
    (hx : X⊆A) (hy : Y⊆B) : (join S (X,Y)).card-S.card = X.card+Y.card := by
  have H : Disjoint (S∪X) Y :=
    Finset.disjoint_union_left.mpr ⟨dSB.mono_right hy,(dAB.mono_left hx).mono_right hy⟩
  simp only [join,card_union_of_disjoint H,card_union_of_disjoint (dSA.mono_right hx)]
  omega

private noncomputable def branchMass (G : SimpleGraph V) (S A : Finset V) : ℚ :=
  ((∑ X∈choices G S A,X.card) : ℕ) / ((choices G S A).card : ℚ)

private theorem split_div (x y p q r : ℚ) (hp : 0<p) (hq : 0<q) :
    (x*q+p*y)/(p*q*r) = (x/p+y/q)/r := by
  by_cases hr : r=0
  · simp only [hr,mul_zero,div_zero]
  · field_simp

private theorem split_formula {S A B : Finset V} (hS : Conn G S) (all : S∪A∪B=univ)
    (dSA : Disjoint S A) (dSB : Disjoint S B) (dAB : Disjoint A B)
    (sep : ∀ a∈A,∀ b∈B,¬G.Adj a b) :
    density G S = (branchMass G S A + branchMass G S B)/(A.card+B.card : ℕ) := by
  classical
  let P:= choices G S A
  let Q:= choices G S B
  have inter := join_injective (G:=G) dSA dSB dAB
  have cardv : Fintype.card V=S.card+A.card+B.card := by
    rw [←card_univ,←all,card_union_of_disjoint (disjoint_union_left.mpr ⟨dSB,dAB⟩),
      card_union_of_disjoint dSA]
  have qa : (0:ℚ)<P.card := by exact_mod_cast choices_pos hS A
  have qb : (0:ℚ)<Q.card := by exact_mod_cast choices_pos hS B
  have total : ∑ z∈P×ˢQ, ((join S z).card-S.card) =
      (∑ X∈P,X.card)*Q.card + P.card*(∑ Y∈Q,Y.card) := by
    rw [sum_product]
    calc
      _ = ∑ X∈P,∑ Y∈Q,(X.card+Y.card) := by
        apply sum_congr rfl
        intro X hx
        apply sum_congr rfl
        intro Y hy
        exact join_extra dSA dSB dAB (choices_mem.mp hx).1 (choices_mem.mp hy).1
      _ = _ := by simp [sum_add_distrib,←sum_mul,mul_comm]
  unfold density familyDensity
  dsimp only
  rw [product_family hS all sep,card_image_of_injOn inter,sum_image inter,card_product]
  change (↑(∑ z∈P×ˢQ,((join S z).card-S.card)) : ℚ) / ↑(P.card*Q.card*(Fintype.card V-S.card))=_
  rw [total,show Fintype.card V-S.card=A.card+B.card by omega]
  unfold branchMass
  change _=(((∑ X∈P,X.card) : ℕ) / (P.card : ℚ) + ((∑ Y∈Q,Y.card) : ℕ) / (Q.card : ℚ)) / ((A.card+B.card : ℕ) : ℚ)
  push_cast
  exact split_div _ _ _ _ _ qa qb

omit [Fintype V] in
private theorem choices_fill {S A B : Finset V} (hS : Conn G S) (hSB : Conn G (S∪B))
    (sep : ∀ a∈A,∀ b∈B,¬G.Adj a b) : choices G (S∪B) A = choices G S A := by
  ext X
  rw [choices_mem,choices_mem]
  apply and_congr_right
  intro hX
  rw [union_right_comm,connected_split hS (fun x hx => sep x (hX hx))]
  exact and_iff_left hSB

omit [Fintype V] in
private theorem empty_mass (S : Finset V) : branchMass G S ∅ = 0 := by
  unfold branchMass
  have num : ∑ X∈choices G S ∅,X.card=0 := sum_eq_zero fun X hx => by
    simp only [subset_empty.mp (choices_mem.mp hx).1,card_empty]
  rw [num]
  simp

private theorem one_branch {S A B : Finset V} (hS : Conn G S) (hSB : Conn G (S∪B))
    (all : S∪A∪B=univ) (dSA : Disjoint S A) (dAB : Disjoint A B)
    (sep : ∀ a∈A,∀ b∈B,¬G.Adj a b) :
    density G (S∪B) = branchMass G S A / A.card := by
  have big : S∪B∪A∪∅=univ := by simpa only [union_empty,union_right_comm] using all
  have ds : Disjoint (S∪B) A := disjoint_union_left.mpr ⟨dSA,dAB.symm⟩
  rw [split_formula hSB big ds (by simp) (by simp) (by simp),
    empty_mass,add_zero,card_empty,add_zero,branchMass,choices_fill hS hSB sep]
  rfl

/-- Splitting the complement into parts with no edges between them gives a
    size-weighted average of the two densities with one part filled. -/
theorem branch_average (hc : G.Connected) {S A B : Finset V} (hS : Conn G S)
    (all : S∪A∪B=univ) (dSA : Disjoint S A) (dSB : Disjoint S B) (dAB : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) (sep : ∀ a∈A,∀ b∈B,¬G.Adj a b) :
    (A.card+B.card : ℚ)*density G S =
      (A.card : ℚ)*density G (S∪B) + (B.card : ℚ)*density G (S∪A) := by
  have hu : Conn G (S∪A∪B) := by
    rw [Conn,all,coe_univ]
    exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hc
  obtain ⟨ca,cb⟩ := (connected_split hS sep).mp hu
  have all' : S∪B∪A=univ := by rwa [union_right_comm]
  have sep' : ∀ b∈B,∀ a∈A,¬G.Adj b a := fun _ hb _ ha edge => sep _ ha _ hb edge.symm
  rw [split_formula hS all dSA dSB dAB sep,one_branch hS cb all dSA dAB sep,
    one_branch hS ca all' dSB dAB.symm sep']
  push_cast
  have ap : 0<(A.card:ℚ) := by exact_mod_cast hA.card_pos
  have bp : 0<(B.card:ℚ) := by exact_mod_cast hB.card_pos
  rw [mul_div_cancel₀ _ (ne_of_gt (add_pos ap bp)),mul_div_cancel₀ _ ap.ne',
    mul_div_cancel₀ _ bp.ne']

end WangLocalDensity
