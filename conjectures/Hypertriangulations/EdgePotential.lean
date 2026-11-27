module

public import conjectures.Hypertriangulations.Weights
import Mathlib.Tactic.Linarith

@[expose] public section
namespace Hypertriangulations
open Finset
variable {α : Type*} [DecidableEq α]

abbrev EdgeWeight (α : Type*) := Finset α→α→α→ℤ

def whiteBoundary (f : EdgeWeight α) (U : Finset α) (a b c : α) := f U a b+f U b c+f U c a

def blackBoundary (f : EdgeWeight α) (U : Finset α) (a b c : α) :=
  f (insert c U) b a+f (insert a U) c b+f (insert b U) a c

private def Applies (A : Finset α) (R : Finset α→α→α→α→Prop) := ∀ {U a b c}, U⊆A →
  a∈A → b∈A → c∈A → a∉U → b∉U → c∉U → R U a b c

private theorem extend_triangles {A : Finset α} {n : α} (R : Finset α→α→α→α→Prop)
    (cycle : ∀ U a b c, R U a b c ↔ R U b c a)
    (same : ∀ U a b, R U a a b) (old : Applies A R)
    (new : Applies A (fun U a b c ↦ R (insert n U) a b c))
    (mixed : ∀ {U a b}, U⊆A → a∈A → b∈A → a∉U → b∉U → R U a b n) : Applies (insert n A) R := by
  intro U a b c sub am bm cm au bu cu
  by_cases nu : n∈U
  · have sub' : U.erase n⊆A := by
      intro x hx
      have m := sub (mem_of_mem_erase hx)
      simpa [ne_of_mem_erase hx] using m
    rw [←insert_erase nu]
    exact new sub' (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
  have sub' : U⊆A := by intro x hx; have := sub hx; grind
  rcases eq_or_ne a b with rfl|ab
  · exact same _ _ _
  rcases eq_or_ne b c with rfl|bc
  · exact (cycle _ _ _ _).mpr (same _ _ _)
  rcases eq_or_ne c a with rfl|ca
  · exact (cycle _ _ _ _).mp (same _ _ _)
  rcases eq_or_ne c n with rfl|cn
  · exact mixed sub' (by grind) (by grind) au bu
  rcases eq_or_ne a n with rfl|an
  · exact (cycle _ _ _ _).mpr (mixed sub' (by grind) (by grind) bu cu)
  rcases eq_or_ne b n with rfl|bn
  · exact (cycle _ _ _ _).mp (mixed sub' (by grind) (by grind) cu au)
  exact old sub' (by grind) (by grind) (by grind) au bu cu

variable [Fintype α] (P : α→Plane)

private def Valid (A : Finset α) (f : EdgeWeight α) :=
  (∀ U a b,f U b a= -f U a b) ∧
  Applies A (fun U a b c ↦ whiteBoundary f U a b c=white P U a b c) ∧
  Applies A (fun U a b c ↦ blackBoundary f U a b c=black P U a b c)

set_option maxHeartbeats 600000 in
private theorem extend_potential (gp : GeneralPosition P) {A : Finset α} {n : α} (hn : n∉A)
    (f : EdgeWeight α) (valid : Valid P A f) : ∃ F,Valid P (insert n A) F := by
  classical
  obtain ⟨anti,oldW,oldB⟩ := valid
  let base (U : Finset α) := if h : ∃ a∈A,a∉U then h.choose else n
  let g (U : Finset α) (a : α) := white P U (base U) a n-f U (base U) a
  let h (U : Finset α) (a b : α) := -black P U a b n-g (insert a U) b+g (insert b U) a
  let F : EdgeWeight α := fun U a b ↦ if n∈U then h (U.erase n) a b else
    if b=n then (if a=n then 0 else g U a) else if a=n then -g U b else f U a b
  have Fanti (U : Finset α) (a b : α) : F U b a= -F U a b := by
    by_cases nu : n∈U
    · simp only [F,nu,ite_true,h,black,score_swap P (U.erase n) a b n];omega
    · by_cases an : a=n <;> by_cases bn : b=n <;> simp [F,nu,an,bn]; exact anti U a b
  have ext (U : Finset α) {a b : α} (nu : n∉U) (an : a≠n) (bn : b≠n) : F U a b=f U a b := by simp [F,nu,an,bn]
  have left (U : Finset α) {a : α} (nu : n∉U) (an : a≠n) : F U a n=g U a := by simp [F,nu,an]
  have right (U : Finset α) {a : α} (nu : n∉U) (an : a≠n) : F U n a= -g U a := by simp [F,nu,an]
  have upper (U : Finset α) (nu : n∉U) (a b : α) : F (insert n U) a b=h U a b := by simp [F,nu]
  have glue {U : Finset α} {a b : α} (sub : U⊆A) (am : a∈A) (bm : b∈A) (au : a∉U) (bu : b∉U) :
      f U a b+g U b-g U a=white P U a b n := by
    have exists' : ∃ x∈A,x∉U := ⟨a,am,au⟩
    have rm : base U∈A := by simpa [base,exists'] using exists'.choose_spec.1
    have ru : base U∉U := by simpa [base,exists'] using exists'.choose_spec.2
    have w := white_faces P gp U ru au bu (fun e ↦ hn (sub e))
    have lower := oldW sub rm am bm ru au bu
    unfold whiteBoundary at lower
    dsimp only [g]
    linarith only [w,lower,anti U (base U) b]
  refine ⟨F,Fanti,?_,?_⟩
  · apply extend_triangles
    · intro U a b c
      simp only [whiteBoundary,white,score_cycle P _ a b c];omega
    · intro U a b
      have := Fanti U a b;have := Fanti U a a
      simp only [whiteBoundary,white,score_degenerate];omega
    · intro U a b c sub am bm cm au bu cu
      have nu : n∉U := fun e ↦ hn (sub e)
      have an : a≠n := by grind
      have bn : b≠n := by grind
      have cn : c≠n := by grind
      simpa only [whiteBoundary,ext U nu an bn,ext U nu bn cn,ext U nu cn an] using oldW sub am bm cm au bu cu
    · intro U a b c sub am bm cm au bu cu
      by_cases rep : a=b ∨ a=c ∨ b=c
      · rcases rep with rfl|rfl|rfl <;> unfold whiteBoundary white <;> grind [score_swap,score_cycle,score_degenerate]
      simp only [not_or] at rep
      have nu : n∉U := fun e ↦ hn (sub e)
      have wa := glue (insert_subset am sub) bm cm (by simp [bu];grind) (by simp [cu];grind)
      have wb := glue (insert_subset bm sub) cm am (by simp [cu];grind) (by simp [au];grind)
      have wc := glue (insert_subset cm sub) am bm (by simp [au];grind) (by simp [bu];grind)
      have oct := octa_faces P gp U au bu cu nu
      have b0 := oldB sub am bm cm au bu cu
      simp only [whiteBoundary,upper U nu,h]
      unfold blackBoundary at b0
      -- Each lower black edge occurs with the opposite orientation in an adjacent white face.
      have wrot := score_swap P (univ\insert b U) a c n
      have brot := score_swap P U a c n
      unfold black white at *
      linarith only [oct,b0,wa,wb,wc,wrot,brot,anti (insert a U) b c,anti (insert b U) c a,anti (insert c U) a b]
    · intro U a b sub am bm au bu
      have nu : n∉U := fun e ↦ hn (sub e)
      have an : a≠n := by grind
      have bn : b≠n := by grind
      simpa only [whiteBoundary,ext U nu an bn,left U nu bn,right U nu an,sub_eq_add_neg] using glue sub am bm au bu
  · apply extend_triangles
    · intro U a b c
      simp only [blackBoundary,black,score_cycle P _ a b c];omega
    · intro U a b
      have := Fanti (insert b U) a a;have := Fanti (insert a U) a b
      simp only [blackBoundary,black,score_degenerate];omega
    · intro U a b c sub am bm cm au bu cu
      have nu : n∉U := fun e ↦ hn (sub e)
      have an : a≠n := by grind
      have bn : b≠n := by grind
      have cn : c≠n := by grind
      simpa only [blackBoundary,ext (insert c U) (by simp [cn.symm,nu]) bn an,ext (insert a U) (by simp [an.symm,nu]) cn bn,
        ext (insert b U) (by simp [bn.symm,nu]) an cn] using oldB sub am bm cm au bu cu
    · intro U a b c sub am bm cm au bu cu
      have nu : n∉U := fun e ↦ hn (sub e)
      have an : a≠n := by grind
      have bn : b≠n := by grind
      have cn : c≠n := by grind
      have face := black_faces P gp U a b c n
      have rot := score_swap P (insert b U) a c n
      unfold blackBoundary
      rw [insert_comm c n,insert_comm a n,insert_comm b n,upper _ (by simp [cn.symm,nu]),
        upper _ (by simp [an.symm,nu]),upper _ (by simp [bn.symm,nu])]
      dsimp only [h]
      have s₁ := score_swap P (insert c U) a b n
      have s₂ := score_swap P (insert a U) b c n
      unfold black at *
      rw [insert_comm b c,insert_comm c a,insert_comm a b]
      linarith only [face,rot,s₁,s₂]
    · intro U a b sub am bm au bu
      have nu : n∉U := fun e ↦ hn (sub e)
      have an : a≠n := by grind
      have bn : b≠n := by grind
      simp only [blackBoundary,upper U nu,right (insert a U) (by simp [an.symm,nu]) bn,left (insert b U) (by simp [bn.symm,nu]) an,h]
      have := score_swap P U a b n
      unfold black at *;omega

/-- Every white and black face weight is the signed sum of three edge weights. -/
theorem edge_potential (gp : GeneralPosition P) : ∃ f : EdgeWeight α,
    (∀ U a b,f U b a= -f U a b) ∧
    (∀ U a b c, a∉U → b∉U → c∉U → whiteBoundary f U a b c=white P U a b c) ∧
    (∀ U a b c, a∉U → b∉U → c∉U → blackBoundary f U a b c=black P U a b c) := by
  classical
  have build (A : Finset α) : ∃ f,Valid P A f := by
    induction A using Finset.induction_on with
    | empty => exact ⟨fun _ _ _ ↦ 0,by simp [Valid,Applies]⟩
    | insert n A hn ih => obtain ⟨f,h⟩ := ih; exact extend_potential P gp hn f h
  obtain ⟨f,anti,fw,fb⟩ := build univ
  exact ⟨f,anti,fun U a b c ↦ fw (subset_univ U) (mem_univ a) (mem_univ b) (mem_univ c),
    fun U a b c ↦ fb (subset_univ U) (mem_univ a) (mem_univ b) (mem_univ c)⟩

end Hypertriangulations
