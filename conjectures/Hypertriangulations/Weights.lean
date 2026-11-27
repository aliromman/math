module

public import conjectures.Hypertriangulations.SignedAreas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
namespace Hypertriangulations
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] (P : α→Plane)

/-- The signed weight counts each eligible point in the open triangle twice. -/
noncomputable def score (S : Finset α) (a b c : α) : ℤ :=
  sign (P a) (P b) (P c)+2*∑ x ∈ S,winding (P a) (P b) (P c) (P x)

omit [Fintype α] [DecidableEq α] in
theorem score_count (S : Finset α) (a b c : α) : score P S a b c=sign (P a) (P b) (P c)*
    (1+2*((S.filter (fun x ↦ StrictInside (P a) (P b) (P c) (P x))).card : ℤ)) := by
  simp only [score,winding_inside,←Finset.sum_filter,sum_const,nsmul_eq_mul]
  ring

noncomputable def white (U : Finset α) := score P (Finset.univ\U)
noncomputable def black (U : Finset α) := score P U

omit [Fintype α] [DecidableEq α] in
theorem score_cycle (S : Finset α) (a b c : α) : score P S b c a=score P S a b c := by
  simp only [score,sign_cycle (P a) (P b) (P c),winding_cycle (P a) (P b) (P c)]

omit [Fintype α] [DecidableEq α] in
theorem score_swap (S : Finset α) (a b c : α) : score P S b a c= -score P S a b c := by
  simp only [score,sign_swap (P a) (P b) (P c),winding_swap (P a) (P b) (P c),sum_neg_distrib]
  omega

omit [Fintype α] [DecidableEq α] in
@[simp] theorem score_degenerate (S : Finset α) (a b : α) : score P S a a b=0 := by simp [score]

omit [Fintype α] in
private theorem score_congr {S T : Finset α} {a b c : α}
    (h : ∀ x, x≠a → x≠b → x≠c → (x∈S ↔ x∈T)) : score P S a b c=score P T a b c := by
  classical
  have cut (S : Finset α) : ∑ x ∈ S,winding (P a) (P b) (P c) (P x) =
      ∑ x ∈ S\{a,b,c},winding (P a) (P b) (P c) (P x) := by
    symm
    apply sum_subset sdiff_subset
    intro i hi miss
    simp_all only [mem_sdiff,mem_insert,mem_singleton,true_and,not_not]
    rcases miss with rfl|rfl|rfl <;> simp
  have e : S\{a,b,c}=T\{a,b,c} := by ext x; simp only [mem_sdiff,mem_insert,mem_singleton]; grind
  simp only [score,cut S,cut T,e]

private def delta (f : α→α→α→ℤ) (a b c d : α) : ℤ := f b c d-f a c d+f a b d-f a b c

omit [Fintype α] [DecidableEq α] in
private theorem delta_expand (S : Finset α) (a b c d : α) :
    delta (score P S) a b c d = delta (fun x y z ↦ sign (P x) (P y) (P z)) a b c d+
      2*∑ p ∈ S,delta (fun x y z ↦ winding (P x) (P y) (P z) (P p)) a b c d := by
  simp only [delta,score,sum_sub_distrib,sum_add_distrib];omega

omit [Fintype α] [DecidableEq α] in
private theorem delta_repeat (S : Finset α) {a b c d : α}
    (h : a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d) : delta (score P S) a b c d=0 := by
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold delta <;>
    grind [score_swap,score_cycle,score_degenerate]

omit [Fintype α] in
private theorem outside_zero (gp : GeneralPosition P) {a b c d p : α}
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (out : p∉({a,b,c,d} : Finset α)) : delta (fun x y z ↦ winding (P x) (P y) (P z) (P p)) a b c d=0 := by
  simp only [mem_insert,mem_singleton,not_or] at out
  exact winding_boundary _ _ _ _ _ (gp _ _ _ out.1 out.2.1 hab) (gp _ _ _ out.1 out.2.2.1 hac)
    (gp _ _ _ out.1 out.2.2.2 had) (gp _ _ _ out.2.1 out.2.2.1 hbc)
    (gp _ _ _ out.2.1 out.2.2.2 hbd) (gp _ _ _ out.2.2.1 out.2.2.2 hcd)

omit [Fintype α] in
private theorem tetra (gp : GeneralPosition P) (S : Finset α) {a b c d : α}
    (h : ({a,b,c,d} : Finset α)⊆S) : delta (score P S) a b c d=0 := by
  by_cases rep : a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d
  · exact delta_repeat P S rep
  simp only [not_or] at rep
  obtain ⟨ab,ac,ad,bc,bd,cd⟩ := rep
  have restrict := sum_subset h fun p _ out ↦ outside_zero P gp ab ac ad bc bd cd out
  rw [delta_expand,←restrict]
  have a0 : a∉({b,c,d} : Finset α) := by simp [ab,ac,ad]
  have b0 : b∉({c,d} : Finset α) := by simp [bc,bd]
  have c0 : c∉({d} : Finset α) := by simp [cd]
  simp only [sum_insert a0,sum_insert b0,sum_insert c0,sum_singleton,delta,
    winding_at_first,winding_at_second,winding_at_third,zero_sub,sub_zero,add_zero,zero_add]
  linarith only [active_boundary _ _ _ _ (gp _ _ _ ab ac bc) (gp _ _ _ ab ad bd) (gp _ _ _ ac ad cd) (gp _ _ _ bc bd cd)]

/-- The four faces of a white tetrahedron. -/
theorem white_faces (gp : GeneralPosition P) (U : Finset α) {a b c d : α}
    (ha : a∉U) (hb : b∉U) (hc : c∉U) (hd : d∉U) :
    white P U b c d-white P U a c d+white P U a b d-white P U a b c=0 := by
  exact tetra P gp _ (by intro x hx; simp only [mem_insert,mem_singleton] at hx; grind : ({a,b,c,d} : Finset α)⊆univ\U)

omit [Fintype α] in
/-- The four faces of a black tetrahedron. -/
theorem black_faces (gp : GeneralPosition P) (U : Finset α) (a b c d : α) :
    black P (insert a U) b c d-black P (insert b U) a c d+
    black P (insert c U) a b d-black P (insert d U) a b c=0 := by
  let S := U∪{a,b,c,d}
  have h := tetra P gp S (subset_union_right : ({a,b,c,d} : Finset α)⊆S)
  unfold delta at h
  unfold black
  have eq (a b c d : α) (v : U∪{a,b,c,d}=S) :
      score P (insert a U) b c d=score P S b c d := by
    apply score_congr
    intro x l m n
    rw [←v]
    simp [l,m,n]
  rwa [eq a b c d rfl,eq b a c d (by ext; simp [S];grind),
    eq c a b d (by ext; simp [S];grind),eq d a b c (by ext; simp [S];grind)]

/-- Opposite faces of an octahedron give projected triangles with the same three active points. -/
theorem octa_faces (gp : GeneralPosition P) (U : Finset α) {a b c d : α}
    (ha : a∉U) (hb : b∉U) (hc : c∉U) (hd : d∉U) :
    white P (insert a U) b c d-white P (insert b U) a c d+
    white P (insert c U) a b d-white P (insert d U) a b c=
      black P U b c d-black P U a c d+black P U a b d-black P U a b c := by
  let T : Finset α := {a,b,c,d}
  let S := univ\(U∪T)
  have cut (a b c d : α) (e : ({a,b,c,d} : Finset α)=T) :
      white P (insert a U) b c d=score P S b c d := by
    apply score_congr
    intro x l m n
    simp [S,←e,l,m,n]
  rw [cut a b c d rfl,cut b a c d (by ext; simp [T];grind),cut c a b d (by ext; simp [T];grind),
    cut d a b c (by ext; simp [T];grind)]
  change delta (score P S) a b c d=delta (score P U) a b c d
  by_cases rep : a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d
  · rw [delta_repeat P S rep,delta_repeat P U rep]
  simp only [not_or] at rep
  obtain ⟨ab,ac,ad,bc,bd,cd⟩ := rep
  rw [delta_expand,delta_expand]
  have zero (R : Finset α) (hr : ∀ p∈R,p∉T) : ∑ p ∈ R,delta (fun x y z ↦ winding (P x) (P y) (P z) (P p)) a b c d=0 :=
    sum_eq_zero fun p h ↦ outside_zero P gp ab ac ad bc bd cd (hr p h)
  rw [zero S (by simp [S]),zero U (by simp [T];grind)]

end Hypertriangulations
