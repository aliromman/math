module

public import conjectures.Hypertriangulations.Mesh
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace Hypertriangulations
open Finset Set
variable {V : Type*} [Fintype V] [DecidableEq V] {P : V→Plane} {E : V→V→Prop}

omit [Fintype V] in
theorem Face.card_vertices {t : Face V} (hp : 0<t.area P) : t.vertices.card=3 := by
  obtain ⟨a,b,c⟩ := t.neighbors hp
  simp [Face.vertices,a,b,c.symm]

theorem unused {T : Mesh P E} {t : Face V} (ht : t∈T.faces) {d : V} {bary : V→ℝ}
    (prob : probability bary) (sup : supported bary t.vertices) (he : eval P bary=P d)
    (positive : ∀ i∈t.vertices,0<bary i) : ∀ s∈T.faces, d∉s.vertices := by
  intro s hs hd
  have same : massAt d 1 = bary := by
    have atom : massAt d 1 ∈ weights T.faces := by
      exact ⟨⟨by intro i; simp [massAt]; split <;> norm_num, sum_massAt _ _⟩,s,hs,
        fun i hi ↦ by have ne : i≠d := fun e ↦ hi (e ▸ hd); simp [massAt,ne]⟩
    exact T.embedded atom ⟨prob,t,ht,sup⟩ (by simpa using he.symm)
  have near (j : V) (hj : j∈t.vertices) : j=d := by
    by_contra h
    have val := congrFun same j
    simp [massAt,h] at val
    linarith [positive j hj]
  have := near t.a (by simp [Face.vertices])
  have := near t.b (by simp [Face.vertices])
  exact (t.neighbors (T.positive t ht)).1 (by grind)

def star1 (f : Face V) (d : V) : Face V := ⟨f.a,f.b,d⟩
def star2 (f : Face V) (d : V) : Face V := ⟨f.b,f.c,d⟩
def star3 (f : Face V) (d : V) : Face V := ⟨f.c,f.a,d⟩
def children (f : Face V) (d : V) : Finset (Face V) := {star1 f d,star2 f d,star3 f d}
def subdivided (s : Finset (Face V)) (f : Face V) (d : V) := s.erase f ∪ children f d

def collapse (d : V) (bary w : V→ℝ) : V→ℝ := w-massAt d (w d) + w d • bary

omit [DecidableEq V] in
theorem eval_sub (P : V→Plane) (v w : V→ℝ) : eval P (v-w) = eval P v - eval P w := by
  simp [eval,sub_smul,Finset.sum_sub_distrib]

omit [Fintype V] in
private theorem collapse_eq {d : V} {bary w : V→ℝ} (zero : w d=0) : collapse d bary w=w := by
  ext i; simp [collapse,zero,massAt]

theorem collapse_eval {d : V} {bary w : V→ℝ} (he : eval P bary=P d) :
    eval P (collapse d bary w) = eval P w := by
  rw [collapse,eval_add,eval_sub,eval_massAt,eval_scale,he]; abel

theorem collapse_prob {d : V} {bary w : V→ℝ} (hp : probability bary) (hw : probability w) :
    probability (collapse d bary w) := by
  constructor
  · intro i
    by_cases h : i=d
    · subst i; simp [collapse,massAt]; exact mul_nonneg (hw.1 _) (hp.1 _)
    · simp [collapse,massAt,h]; exact add_nonneg (hw.1 _) (mul_nonneg (hw.1 _) (hp.1 _))
  · simp only [collapse,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      Finset.sum_sub_distrib,sum_massAt,←Finset.mul_sum,hp.2,hw.2,mul_one,sub_add_cancel]

omit [Fintype V] in
theorem children_contains {f s : Face V} {d : V} (h : s∈children f d) :
    d∈s.vertices ∧ s.vertices⊆insert d f.vertices := by
  simp only [children,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl <;> simp [star1,star2,star3,Face.vertices,Finset.subset_iff]

private theorem miss_vertex {T : Mesh P E} {f : Face V} (hf : f∈T.faces) {d : V}
    (fresh : ∀ s∈T.faces, d∉s.vertices) {s : Face V} (hs : s∈subdivided T.faces f d) :
    ∃ i∈f.vertices, i∉s.vertices := by
  by_contra! h
  have sub : f.vertices⊆s.vertices := h
  rcases Finset.mem_union.mp hs with old|new
  · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp old
    have eq := Finset.eq_of_subset_of_card_le sub (by rw [f.card_vertices (T.positive f hf),s.card_vertices (T.positive s mem)])
    exact ne (T.unique_faces f hf s mem eq).symm
  · have inc := (children_contains new).1
    have card : s.vertices.card≤3 := by
      unfold Face.vertices
      exact (Finset.card_insert_le _ _).trans (by have := Finset.card_insert_le s.b {s.c}; simpa using Nat.add_le_add_right this 1)
    have eq := Finset.eq_of_subset_of_card_le sub (by rwa [f.card_vertices (T.positive f hf)])
    exact fresh f hf (eq ▸ inc)

omit [Fintype V] in
theorem collapse_child {d : V} {f s : Face V} {bary w : V→ℝ} (new : s∈children f d)
    (ls : supported bary f.vertices) (sw : supported w s.vertices) : supported (collapse d bary w) f.vertices := by
  intro i hi
  by_cases e : i=d
  · subst i; simp [collapse,massAt,ls _ hi]
  · have h : i∉s.vertices := fun h ↦ hi (Finset.mem_insert.mp ((children_contains new).2 h) |>.resolve_left e)
    simp [collapse,massAt,e,ls i hi,sw i h]

theorem collapse_image {T : Mesh P E} {f : Face V} {d : V} (hf : f∈T.faces)
    (fresh : ∀ s∈T.faces,d∉s.vertices) {bary : V→ℝ} (lp : probability bary) (ls : supported bary f.vertices)
    {w : V→ℝ} (hw : w∈weights (subdivided T.faces f d)) : collapse d bary w ∈ weights T.faces := by
  obtain ⟨pr,s,hs,sw⟩ := hw
  refine ⟨collapse_prob lp pr,?_⟩
  rcases Finset.mem_union.mp hs with old|new
  · have mem := (Finset.mem_erase.mp old).2
    rw [collapse_eq (bary:=bary) (sw d (fresh s mem))]
    exact ⟨s,mem,sw⟩
  · refine ⟨f,hf,fun i hi ↦ ?_⟩
    exact collapse_child new ls sw i hi

theorem collapse_injective {T : Mesh P E} {f : Face V} {d : V} (hf : f∈T.faces)
    (fresh : ∀ s∈T.faces,d∉s.vertices) {bary : V→ℝ} (positive : ∀ i∈f.vertices,0<bary i) :
    Set.InjOn (collapse d bary) (weights (subdivided T.faces f d)) := by
  have le {w v : V→ℝ} (hw : w∈weights (subdivided T.faces f d)) (hv : v∈weights (subdivided T.faces f d))
      (eq : collapse d bary w = collapse d bary v) : v d ≤ w d := by
    obtain ⟨_,s,hs,sw⟩ := hw
    obtain ⟨i,fi,si⟩ := miss_vertex hf fresh hs
    have ne : i≠d := fun e ↦ fresh f hf (e ▸ fi)
    have value := congrFun eq i
    simp [collapse,massAt,ne,sw i si] at value
    exact le_of_mul_le_mul_right (a:=bary i) (by linarith only [hv.1.1 i,value]) (positive i fi)
  intro w hw v hv eq
  have wd := le_antisymm (le hv hw eq.symm) (le hw hv eq)
  ext i
  have h := congrFun eq i
  simp only [collapse,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,wd,add_left_inj,sub_left_inj] at h
  exact h

end Hypertriangulations
end
