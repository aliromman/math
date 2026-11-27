module

public import conjectures.Hypertriangulations.StarWeights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace Hypertriangulations
open Set Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {P : V→Plane} {E : V→V→Prop}

omit [Fintype V] in
private theorem child_excluding {f : Face V} (d : V) {j : V} (hj : j∈f.vertices) :
    ∃ s∈children f d, ∀ i∈f.vertices, i≠j → i∈s.vertices := by
  simp only [Face.vertices,Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl|rfl|rfl
  · refine ⟨star2 f d,by simp [children],?_⟩
    simp [star2,Face.vertices]
  · refine ⟨star3 f d,by simp [children],?_⟩
    simp [star3,Face.vertices]
  · refine ⟨star1 f d,by simp [children],?_⟩
    simp [star1,Face.vertices]

theorem lift_weights {T : Mesh P E} {f : Face V} {d : V}
    {bary : V→ℝ} (lp : probability bary)
    (ls : supported bary f.vertices) (he : eval P bary=P d) (positive : ∀ i∈f.vertices,0<bary i)
    {w : V→ℝ} (hw : w∈weights T.faces) :
    ∃ w'∈weights (subdivided T.faces f d), eval P w'=eval P w := by
  obtain ⟨wp,g,hg,ws⟩ := hw
  by_cases eq : g=f
  · subst g
    obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image f.vertices (fun i ↦ w i / bary i)
      (show f.vertices.Nonempty from ⟨f.a,by simp [Face.vertices]⟩)
    let r := w j/bary j
    have rn : 0≤r := div_nonneg (wp.1 j) (positive j hj).le
    have rem (i : V) : r*bary i≤w i := by
      by_cases hi : i∈f.vertices
      · exact (le_div_iff₀ (positive i hi)).mp (hmin i hi)
      · simp [ls i hi,wp.1 i]
    let v := w-r • bary + massAt d r
    have vp : probability v := by
      refine ⟨fun i ↦ ?_,?_⟩
      · change 0 ≤ w i-r*bary i+(if i=d then r else 0)
        have := rem i
        split <;> linarith
      · simp only [v,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
          Finset.sum_sub_distrib,sum_massAt,←Finset.mul_sum,lp.2,wp.2,mul_one,sub_add_cancel]
    obtain ⟨s,hs,includeOther⟩ := child_excluding d hj
    refine ⟨v,⟨vp,s,Finset.mem_union.mpr (Or.inr hs),?_⟩,?_⟩
    · intro i hi
      have ne : i≠d := fun e ↦ hi (e ▸ (children_contains hs).1)
      by_cases ij : i=j
      · subst i
        have e : r*bary j=w j := div_mul_cancel₀ _ (positive _ hj).ne'
        simp [v,massAt,ne,e]
      · have old : i∉f.vertices := fun h ↦ hi (includeOther i h ij)
        simp [v,massAt,ne,ws i old,ls i old]
    · rw [show v=w-r • bary+massAt d r by rfl,eval_add,eval_sub,eval_scale,eval_massAt,he]
      abel
  · exact ⟨w,⟨wp,g,Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨eq,hg⟩)),ws⟩,rfl⟩

end Hypertriangulations
end
