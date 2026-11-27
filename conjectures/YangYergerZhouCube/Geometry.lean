module

public import conjectures.YangYergerZhouCube.Statement

public section
namespace YangYergerZhouCube
open Finset
open scoped symmDiff

variable {ι : Type*} [DecidableEq ι]

theorem coordinate_edge (a x : Finset ι) {i : ι} (hi : i∉x) :
    Adj a (some (a ∆ insert i x)) (some (a ∆ x)) := by
  change ((a ∆ insert i x) ∆ (a ∆ x)).card=1
  have cancel : (a ∆ insert i x) ∆ (a ∆ x) = insert i x ∆ x := by
    rw [symmDiff_right_comm,symmDiff_symmDiff_cancel_left,symmDiff_comm]
  have one : insert i x ∆ x = {i} := by
    ext j
    by_cases e : j=i <;> simp [e,hi,Finset.mem_symmDiff]
  simp [cancel,one]

private def level (a : Finset ι) : Option (Finset ι) → ℕ
  | none => 0
  | some x => (a ∆ x).card+1

private theorem edge_level (a : Finset ι) {u v} (adj : (cube a).Adj u v) : level a u ≤ level a v +1 := by
  cases u with
  | none => simp [level]
  | some x =>
    cases v with
    | none => change x=a at adj; simp [level,adj]
    | some y =>
      obtain ⟨i,hi⟩ := Finset.card_eq_one.mp adj
      have sx : a ∆ x ⊆ insert i (a ∆ y) := by
        intro j hj
        by_cases h : j=i
        · simp [h]
        · have blank : j∉x ∆ y := by simp [hi,h]
          simp only [Finset.mem_symmDiff] at blank hj
          simp only [Finset.mem_insert,Finset.mem_symmDiff]
          tauto
      have := (Finset.card_le_card sx).trans (Finset.card_insert_le i (a ∆ y))
      dsimp [level]
      omega

private theorem walk_level (a : Finset ι) {u v} (w : (cube a).Walk u v) :
    level a u ≤ w.length + level a v := by
  induction w with
  | nil => simp
  | cons e _ ih => have := edge_level a e; simp only [SimpleGraph.Walk.length_cons]; omega

private theorem short_walk (a x : Finset ι) : ∃ w : (cube a).Walk (some (a ∆ x)) none, w.length=x.card+1 := by
  induction x using Finset.induction_on with
  | empty => exact ⟨.cons (show (cube a).Adj (some (a ∆ ∅)) none by simp [cube,Adj]) .nil,by simp⟩
  | insert i x hi ih =>
    obtain ⟨w,hw⟩ := ih
    exact ⟨.cons (show (cube a).Adj _ (some (a ∆ x)) from coordinate_edge a x hi) w,by simp [hi,hw]⟩

theorem coordinate_distance (a x : Finset ι) : (cube a).dist (some (a ∆ x)) none=x.card+1 := by
  obtain ⟨w,hw⟩ := short_walk a x
  obtain ⟨p,hp⟩ := w.reachable.exists_walk_length_eq_dist
  apply le_antisymm ((SimpleGraph.dist_le w).trans_eq hw)
  simpa [level,hp] using walk_level a p

theorem coordinate_sum [Fintype ι] {M : Type*} [AddCommMonoid M] (a : Finset ι) (f : Finset ι → M) :
    (∑ x ∈ (univ : Finset ι).powerset, f (a ∆ x)) = ∑ x ∈ (univ : Finset ι).powerset, f x := by
  have allSubsets : (univ : Finset ι).powerset = univ := by ext; simp
  rw [allSubsets]
  let e : Finset ι ≃ Finset ι := ⟨(a ∆ ·),(a ∆ ·),by intro x; simp,by intro x; simp⟩
  exact e.sum_comp f

end YangYergerZhouCube
