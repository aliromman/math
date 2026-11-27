module

public import conjectures.SplitMatroidFlags.GraphRank

@[expose] public section

namespace SplitMatroidFlags

open Finset

variable {E : Type} [DecidableEq E] [Fintype E]

/-- Eliminate the outside vertices. Two inside vertices are joined if they share
an outside neighbor. Each active outside vertex contributes one dimension. -/
lemma bipartite_rank {I A : Finset E} {P Q : Finset (E × E)} {r : E → E}
    (disj : Disjoint I A) (ends : ∀ e ∈ P, e.1 ∈ I ∧ e.2 ∈ A)
    (hit : ∀ y ∈ A, ∃ i, (i,y) ∈ P)
    (shared : ∀ i k, i ≠ k → ((i,k) ∈ Q ∨ (k,i) ∈ Q ↔ ∃ y, (i,y) ∈ P ∧ (k,y) ∈ P))
    (noloops : ∀ i, (i,i) ∉ Q)
    (roots : Components Q r) (ri : ∀ i ∈ I, r i ∈ I) (outside : ∀ y ∉ I, r y = y) :
    Module.finrank ℝ (directions P) = A.card + (univ.filter (fun i => r i ≠ i)).card := by
  classical
  choose! near near_mem using hit
  let root y := if y ∈ A then r (near y) else r y
  have neI {i : E} (hi : i ∈ I) : i ∉ A := disjoint_left.mp disj hi
  have neA {y : E} (hy : y ∈ A) : y ∉ I := fun hh => neI hh hy
  have nearI {y : E} (hy : y ∈ A) : near y ∈ I := (ends _ (near_mem y hy)).1
  have sub : directions Q ≤ directions P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,k⟩,h,he⟩
    subst_vars
    have ne : i ≠ k := fun eq => noloops k (eq ▸ h)
    obtain ⟨y,hi,hk⟩ := (shared i k ne).mp (Or.inl h)
    change unit k - unit i ∈ directions P
    simpa only [sub_sub_sub_cancel_left] using (directions P).sub_mem (edge_mem hi) (edge_mem hk)
  have comp : Components P root := by
    refine ⟨?_,?_,?_⟩
    · intro y
      by_cases hy : y ∈ A
      · simp [root,hy,neI (ri _ (nearI hy)),roots.idempotent]
      · by_cases hi : y ∈ I
        · simp [root,hy,neI (ri _ hi),roots.idempotent]
        · simp [root,hy,outside _ hi]
    · rintro ⟨i,y⟩ he
      obtain ⟨hi,hy⟩ := ends _ he
      change root i = root y
      simp only [root,neI hi,hy,ite_false,ite_true]
      by_cases eq : i = near y
      · rw [eq]
      · rcases (shared _ _ eq).mpr ⟨_,he,near_mem y hy⟩ with e | e
        · exact roots.constant _ e
        · exact (roots.constant _ e).symm
    · intro y
      by_cases hy : y ∈ A
      · have h := (directions P).add_mem (edge_mem (near_mem y hy)) (sub (roots.path (near y)))
        simpa [root,hy] using h
      · simpa [root,hy] using sub (roots.path y)
  rw [comp.rank]
  have eq : univ.filter (fun i => root i ≠ i) = A ∪ univ.filter (fun i => r i ≠ i) := by
    ext i
    by_cases hi : i ∈ A
    · have ne : r (near i) ≠ i := fun eq => neA hi (eq ▸ ri _ (nearI hi))
      simp [root,hi,ne]
    · simp [root,hi]
  rw [eq,card_union_of_disjoint]
  exact disjoint_left.mpr fun y hy hh => (mem_filter.mp hh).2 (outside y (neA hy))

end SplitMatroidFlags
