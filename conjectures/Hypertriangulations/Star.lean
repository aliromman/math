module

public import conjectures.Hypertriangulations.LiftWeights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace Hypertriangulations
open Set Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {P : V→Plane} {E : V→V→Prop}

omit [Fintype V] in
private theorem children_positive {t : Face V} {d : V} (h : 0<t.area P)
    (inside : StrictInside (P t.a) (P t.b) (P t.c) (P d)) :
    ∀ u∈children t d, 0<u.area P := by
  have total : orient (P d) (P t.a) (P t.b)+orient (P d) (P t.b) (P t.c)+orient (P d) (P t.c) (P t.a)=t.area P := by
    unfold Face.area orient; ring
  have pos : 0<orient (P d) (P t.a) (P t.b) ∧ 0<orient (P d) (P t.b) (P t.c) ∧ 0<orient (P d) (P t.c) (P t.a) := by
    rcases inside with hp|hn; exact hp; linarith [hn.1,hn.2.1,hn.2.2]
  intro u hu
  simp only [children,Finset.mem_insert,Finset.mem_singleton] at hu
  rcases hu with rfl|rfl|rfl
  · change 0<orient (P t.a) (P t.b) (P d)
    rw [orient_cycle (P d) (P t.a) (P t.b)]
    exact pos.1
  · change 0<orient (P t.b) (P t.c) (P d)
    rw [orient_cycle (P d) (P t.b) (P t.c)]
    exact pos.2.1
  · change 0<orient (P t.c) (P t.a) (P d)
    rw [orient_cycle (P d) (P t.c) (P t.a)]
    exact pos.2.2

omit [Fintype V] in
private theorem unique_children {f : Face V} {d : V} (hp : 0<f.area P) (fresh : d∉f.vertices)
    {s t : Face V} (hs : s∈children f d) (ht : t∈children f d) (eq : s.vertices=t.vertices) : s=t := by
  obtain ⟨a,b,c⟩ := f.neighbors hp
  have da : d≠f.a := fun e ↦ fresh (by simp [Face.vertices,e])
  have db : d≠f.b := fun e ↦ fresh (by simp [Face.vertices,e])
  have dc : d≠f.c := fun e ↦ fresh (by simp [Face.vertices,e])
  have test (v : V) : v∈s.vertices ↔ v∈t.vertices := by rw [eq]
  have ta := test f.a
  have tb := test f.b
  have tc := test f.c
  clear test eq
  simp only [children,Finset.mem_insert,Finset.mem_singleton] at hs ht
  rcases hs with rfl|rfl|rfl <;> rcases ht with rfl|rfl|rfl
  all_goals first | rfl | (simp only [star1,star2,star3,Face.vertices,Finset.mem_insert,Finset.mem_singleton] at ta tb tc; grind)

theorem star_exists (T : Mesh P E) (symm : ∀ {i j}, E i j → E j i) {f : Face V} (hf : f∈T.faces) {d : V}
    (links : E f.a d ∧ E f.b d ∧ E f.c d) (atd : StrictInside (P f.a) (P f.b) (P f.c) (P d)) :
    ∃ S : Mesh P E, Refines S T ∧ S.faces.card=T.faces.card+2 := by
  obtain ⟨bary,lp,ls,he,positive⟩ := inside_coordinates (T.positive f hf) atd
  have fresh := unused hf lp ls he positive
  let F := subdivided T.faces f d
  have split {s} (hs : s∈F) : s∈T.faces.erase f ∨ s∈children f d := Finset.mem_union.mp hs
  have disj : Disjoint (T.faces.erase f) (children f d) := Finset.disjoint_left.mpr fun s ho hn ↦
    fresh s (Finset.mem_erase.mp ho).2 (children_contains hn).1
  let S : Mesh P E := {
    faces := F
    positive := by
      intro t ht
      rcases split ht with h|h
      · exact T.positive t (Finset.mem_erase.mp h).2
      · exact children_positive (T.positive f hf) atd t h
    unique_faces := by
      intro s hs t ht eq
      rcases split hs with a|a <;> rcases split ht with b|b
      · exact T.unique_faces s (Finset.mem_erase.mp a).2 t (Finset.mem_erase.mp b).2 eq
      · exact False.elim (fresh s (Finset.mem_erase.mp a).2 (eq ▸ (children_contains b).1))
      · exact False.elim (fresh t (Finset.mem_erase.mp b).2 (eq.symm ▸ (children_contains a).1))
      · exact unique_children (T.positive f hf) (fresh f hf) a b eq
    edges := by
      intro t ht
      rcases split ht with ho|hn
      · exact T.edges t (Finset.mem_erase.mp ho).2
      · have e := T.edges f hf
        simp only [children,Finset.mem_insert,Finset.mem_singleton] at hn
        rcases hn with rfl|rfl|rfl
        · exact ⟨e.1,links.2.1,symm links.1⟩
        · exact ⟨e.2.1,links.2.2,symm links.2.1⟩
        · exact ⟨e.2.2,links.1,symm links.2.2⟩
    cover := by
      intro nondeg x hx
      obtain ⟨w,hw,rfl⟩ := T.cover nondeg hx
      exact lift_weights lp ls he positive hw
    embedded := by
      intro w hw v hv eq
      apply collapse_injective hf fresh positive hw hv
      apply T.embedded (collapse_image hf fresh lp ls hw) (collapse_image hf fresh lp ls hv)
      simpa only [collapse_eval he] using eq }
  refine ⟨S,?_,?_⟩
  · intro s hs
    rcases split hs with old|new
    · exact ⟨s,(Finset.mem_erase.mp old).2,Set.Subset.rfl⟩
    · refine ⟨f,hf,?_⟩
      rintro x ⟨w,wp,sw,rfl⟩
      exact ⟨collapse d bary w,collapse_prob lp wp,collapse_child new ls sw,collapse_eval he⟩
  · have nc : (children f d).card=3 := by
      obtain ⟨a,b,c⟩ := f.neighbors (T.positive f hf)
      have e : star1 f d≠star2 f d := fun h ↦ a (congrArg Face.a h)
      have j : star2 f d≠star3 f d := fun h ↦ b (congrArg Face.a h)
      have k : star1 f d≠star3 f d := fun h ↦ c (congrArg Face.a h).symm
      simp [children,e,j,k]
    change (T.faces.erase f ∪ children f d).card = _
    rw [Finset.card_union_of_disjoint disj,nc]
    have := Finset.card_erase_add_one hf
    omega

/-- A maximal geometric hypertriangulation has no allowed insertion in a face interior. -/
theorem no_insert (T : Mesh P E) (symm : ∀ {i j}, E i j → E j i) (hmax : IsMaximal T) {t : Face V} (ht : t∈T.faces)
    {d : V} (links : E t.a d ∧ E t.b d ∧ E t.c d) : ¬StrictInside (P t.a) (P t.b) (P t.c) (P d) := by
  intro h
  obtain ⟨S,ref,card⟩ := star_exists T symm ht links h
  have := hmax S ref
  omega

end Hypertriangulations
end
