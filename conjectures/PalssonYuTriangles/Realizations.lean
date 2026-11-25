module

public import conjectures.PalssonYuTriangles.Motion
public import conjectures.PalssonYuTriangles.Classification
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

@[expose] public section
open Complex Finset
namespace PalssonYu
noncomputable section

private def Matches (p : Vertex → ℂ) (s : Row) := ∀ a b c d, a≠b → c≠d →
  (D (p a) (p b) = D (p c) (p d) ↔ entry s a b = entry s c d)

private theorem edge {p s} (h : Matches p s) (a b c d : Vertex)
    (cert : a≠b ∧ c≠d ∧ entry s a b=entry s c d) : D (p a) (p b) = D (p c) (p d) :=
  (h a b c d cert.1 cert.2.1).mpr cert.2.2

private abbrev Mid (s : Row) (a b u x v : Vertex) : Prop :=
  [a,b,u,x,v].Nodup ∧ entry s u a=entry s u b ∧ entry s v a=entry s v b ∧
    entry s x a=entry s x b ∧ entry s x u=entry s x v

private theorem mid {p s} (inj : Function.Injective p) (h : Matches p s)
    (a b u x v : Vertex) (cert : Mid s a b u x v) : 2*p x=p u+p v := by
  obtain ⟨nd,e₁,e₂,e₃,e₄⟩ := cert
  simp only [List.nodup_cons,List.mem_cons,not_or,List.nodup_nil,
    and_true] at nd
  apply bisector_midpoint (a:=p a) (b:=p b) (inj.ne (by tauto)) (inj.ne (by tauto))
  all_goals apply edge h; tauto

private theorem scaled_length {u v x y : ℂ} (h : u-v=2*(x-y)) : D u v=4*D x y := by
  unfold D; rw [h,normSq_mul]; norm_num [normSq_apply]

private abbrev row (j : Fin 6) := patterns[j.val]!

/-- The first five abstract patterns contradict the midpoint identities on bisectors. -/
private theorem only_last {p} (inj : Function.Injective p) {j : Fin 6}
    (h : Matches p (row j)) : j=5 := by
  fin_cases j
  · have a := mid inj h 3 5 4 1 6 (by decide)
    have b := mid inj h 3 4 5 0 6 (by decide)
    have t := scaled_length (show p 4-p 5=2*(p 1-p 0) by linear_combination b-a)
    have u := scaled_length (show p 5-p 6=2*(p 5-p 0) by linear_combination b)
    have e := edge h 4 5 5 0 (by decide)
    have f := edge h 5 6 1 0 (by decide)
    linarith only [t,u,e,f,D_pos (inj.ne (by decide : (1:Vertex)≠0))]
  · have a := mid inj h 2 4 0 6 3 (by decide)
    have b := mid inj h 4 6 2 1 3 (by decide)
    have t := scaled_length (show p 0-p 3=2*(p 0-p 6) by linear_combination a)
    have u := scaled_length (show p 2-p 3=2*(p 2-p 1) by linear_combination b)
    have e := edge h 0 3 2 1 (by decide)
    have f := edge h 2 3 0 6 (by decide)
    linarith only [t,u,e,f,D_pos (inj.ne (by decide : (0:Vertex)≠6))]
  · have a := mid inj h 5 6 1 0 2 (by decide)
    have t := scaled_length (show p 1-p 2=2*(p 1-p 0) by linear_combination a)
    have e := edge h 1 2 1 0 (by decide)
    linarith only [t,e,D_pos (inj.ne (by decide : (1:Vertex)≠0))]
  · have a := mid inj h 3 4 1 0 2 (by decide)
    have t := scaled_length (show p 1-p 2=2*(p 1-p 0) by linear_combination a)
    have e := edge h 1 2 1 0 (by decide)
    linarith only [t,e,D_pos (inj.ne (by decide : (1:Vertex)≠0))]
  · have a := mid inj h 0 3 1 4 2 (by decide)
    have b := mid inj h 0 3 1 5 2 (by decide)
    exact ((by decide : (4:Vertex)≠5) (inj (by linear_combination (a-b)/2))).elim
  · rfl

private def cycle : Vertex → Vertex := ![0,1,3,5,6,4,2]

theorem image_reindex {α β : Type*} [Fintype α] [DecidableEq β] (p : α → β)
    (s : α → α) (surj : Function.Surjective s) : univ.image (fun i => p (s i))=univ.image p := by
  ext x
  simp only [mem_image,mem_univ,true_and]
  exact ⟨fun ⟨i,e⟩ => ⟨s i,e⟩,fun ⟨i,e⟩ => by obtain ⟨j,rfl⟩ := surj i; exact ⟨j,e⟩⟩

theorem regular_of_classification {p : Vertex → ℂ} (inj : Function.Injective p)
    (few : FewTypes (fun i j => D (p i) (p j))) : RegularHeptagon (univ.image p) := by
  let c i j := D (p i) (p j)
  have sym (i j) : c i j=c j i := D_comm ..
  have mono : NoMonoFour c := by
    intro a b x y nd
    simp only [List.nodup_cons,List.mem_cons,not_or,
      List.nodup_nil,and_true] at nd
    rintro ⟨u,v,w,t,z⟩
    apply no_tetrahedron (a:=p a) (b:=p b) (x:=p x) (y:=p y) (inj.ne (by tauto)) (inj.ne (by tauto))
    all_goals change c _ _=c b a
    all_goals rw [sym b a]
    · rw [sym x a,u]
    · rw [sym x b,w]
    · rw [sym y a,v]
    · rw [sym y b,t]
    · exact z.symm
  have centers : TwoCenters c := by
    intro a b x y z nd
    simp only [List.nodup_cons,List.mem_cons,not_or,
      List.nodup_nil,and_true] at nd
    rintro ⟨u,v,w,t⟩
    have pair := two_circles (a:=p a) (b:=p b) (x:=p x) (y:=p y) (z:=p z)
      (inj.ne (by tauto)) (inj.ne (by tauto)) ((sym x a).trans (v.trans (sym a z)))
      ((sym x b).trans (t.trans (sym b z))) ((sym y a).trans (u.symm.trans (v.trans (sym a z))))
      ((sym y b).trans (w.symm.trans (t.trans (sym b z))))
    rcases pair with e|e <;> have := inj e <;> tauto
  obtain ⟨π,s,hs,h⟩ := classify_seven_ne c sym few mono centers
  have rs : ∃ j : Fin 6, s=row j := by
    simp only [patterns,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ |
      exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩
  obtain ⟨j,rfl⟩ := rs
  let q := fun i => p (π i)
  have hij := inj.comp π.injective
  have valid : Matches q (row j) := h
  obtain rfl := only_last hij valid
  have cyc : Function.Bijective cycle := by decide
  have shift : ∀ i j : Vertex, i≠j →
      entry (row 5) (cycle (i+1)) (cycle (j+1))=entry (row 5) (cycle i) (cycle j) := by decide
  have reg := heptagon_of_shift (p:=fun i => q (cycle i)) (hij.comp cyc.1) (fun i j => by
    by_cases e : i=j
    · subst j; simp [D]
    · apply (valid _ _ _ _ (cyc.1.ne (fun eq => e (add_right_cancel eq))) (cyc.1.ne e)).mpr
      exact shift i j e)
  rw [image_reindex q cycle cyc.2] at reg
  rw [← image_reindex p π π.surjective]
  exact reg

end
end PalssonYu
