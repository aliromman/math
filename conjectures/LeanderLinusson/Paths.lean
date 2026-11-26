module

public import conjectures.LeanderLinusson.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Union

@[expose] public section
namespace LeanderLinusson
open Finset Function

variable {V : Type*} [Fintype V] [DecidableEq V] {m r : ℕ}
private def Arc (g : Sample V m) (x y : V) := ∃ i, g (i,false) = x ∧ g (i,true) = y

omit [Fintype V] in
private theorem reached_self (g : Sample V m) (s : V) (l : ℕ) : s ∈ reached g s l := by
  induction l with
  | zero => simp [reached]
  | succ l ih => exact mem_union_left _ ih

private theorem arc_path {g : Sample V m} {s a : V} (h : Arc g s a) : PathEvent g s a := by
  have hp := Fintype.card_pos_iff.mpr (Nonempty.intro s)
  obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  obtain ⟨i,hi,ha⟩ := h
  unfold PathEvent
  rw [hl]
  apply mem_union_right
  apply mem_image.mpr
  exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi.symm ▸ reached_self _ _ _⟩,ha⟩

omit [Fintype V] in
private theorem incident {g : Sample V m} {s a : V} (l : ℕ) (h : a ∈ reached g s l) :
    a = s ∨ (∃ i, g (i,false) = s) ∧ ∃ j, g (j,true) = a := by
  induction l generalizing a with
  | zero => simpa only [reached,mem_singleton] using Or.inl h
  | succ l ih =>
    obtain old | new := mem_union.mp h
    · exact ih old
    obtain ⟨j,hj,ha⟩ := mem_image.mp new
    rcases ih (mem_filter.mp hj).2 with hs | ⟨hs,_⟩
    · exact Or.inr ⟨⟨j,hs⟩,⟨j,ha⟩⟩
    · exact Or.inr ⟨hs,⟨j,ha⟩⟩

omit [Fintype V] in
private theorem match_arc {g : Sample V m} (hg : Injective g) {s a : V} (l : ℕ)
    (h : a ∈ reached g s l) : a = s ∨ Arc g s a := by
  induction l generalizing a with
  | zero => exact Or.inl (mem_singleton.mp h)
  | succ l ih =>
    obtain old | new := mem_union.mp h
    · exact ih old
    obtain ⟨j,hj,ha⟩ := mem_image.mp new
    rcases ih (mem_filter.mp hj).2 with hs | ⟨i,_,ht⟩
    · exact Or.inr ⟨j,hs,ha⟩
    · exact Bool.noConfusion (congrArg Prod.snd (hg ht))

omit [Fintype V] [DecidableEq V] in
private theorem match_valid {g : Sample V m} (hg : Injective g) : Valid g := by
  refine ⟨fun i h ↦ Bool.noConfusion (congrArg Prod.snd (hg h)),fun i j hij ↦ ⟨?_,?_⟩⟩
  · intro h
    exact hij (congrArg Prod.fst (hg (congrArg Prod.fst h)))
  · intro h
    exact Bool.noConfusion (congrArg Prod.snd (hg (congrArg Prod.fst h)))

noncomputable def pathSamples (m : ℕ) (b : Fin r × Bool ↪ V) : Finset (Sample V m) := by
  classical exact (samples V m).filter fun g ↦ ∀ i, PathEvent g (b (i,false)) (b (i,true))

@[simp] theorem mem_pathSamples {b : Fin r × Bool ↪ V} {g : Sample V m} :
    g ∈ pathSamples m b ↔ Valid g ∧ ∀ i, PathEvent g (b (i,false)) (b (i,true)) := by
  classical simp [pathSamples,samples]

private def slots (a : Fin r ↪ Fin m) : Fin r × Bool ↪ Fin m × Bool :=
  a.prodMap (Embedding.refl Bool)

omit [Fintype V] [DecidableEq V] in
private theorem term_ne (b : Fin r × Bool ↪ V) (i : Fin r) : b (i,true) ≠ b (i,false) :=
  fun h ↦ Bool.noConfusion (congrArg Prod.snd (b.injective h))

private theorem pins_of_paths {b : Fin r × Bool ↪ V} {g : Sample V m}
    (hg : g ∈ pathSamples m b) : ∀ t, ∃ s, g s = b t := by
  rintro ⟨i,v⟩
  have h := (incident _ ((mem_pathSamples.mp hg).2 i)).resolve_left (term_ne b i)
  cases v with
  | false => obtain ⟨j,hj⟩ := h.1; exact ⟨(j,false),hj⟩
  | true => obtain ⟨j,hj⟩ := h.2; exact ⟨(j,true),hj⟩

private theorem pinned_of_match {b : Fin r × Bool ↪ V} {g : Sample V m} (hg : Injective g)
    (he : g ∈ pathSamples m b) : ∃ a : Fin r ↪ Fin m, g ∈ pinned (slots a) b := by
  have arcs (i : Fin r) : Arc g (b (i,false)) (b (i,true)) :=
    (match_arc hg _ ((mem_pathSamples.mp he).2 i)).resolve_left (term_ne b i)
  choose f hf hf' using arcs
  let a : Fin r ↪ Fin m := ⟨f,fun i j h ↦ congrArg Prod.fst
    (b.injective ((hf i).symm.trans ((congrArg (fun k ↦ g (k,false)) h).trans (hf j))))⟩
  exact ⟨a,mem_pinned.mpr fun ⟨i,z⟩ ↦ by cases z; exact hf i; exact hf' i⟩

private theorem match_of_pinned {b : Fin r × Bool ↪ V} {g : Sample V m} (hg : Injective g)
    {a : Fin r ↪ Fin m} (he : g ∈ pinned (slots a) b) : g ∈ pathSamples m b :=
  mem_pathSamples.mpr ⟨match_valid hg,fun i ↦ arc_path ⟨a i,
    mem_pinned.mp he (i,false),mem_pinned.mp he (i,true)⟩⟩

omit [DecidableEq V] in
private theorem placement_unique {b : Fin r × Bool ↪ V} {g : Sample V m} (hg : Injective g)
    {a a' : Fin r ↪ Fin m} (h : g ∈ pinned (slots a) b) (h' : g ∈ pinned (slots a') b) :
    a = a' := by
  apply Embedding.ext
  intro i
  exact congrArg Prod.fst (hg ((mem_pinned.mp h (i,false)).trans (mem_pinned.mp h' (i,false)).symm))

/-- On a matching every directed path is a single edge. The error is supported on
arrays with a repeated vertex where every one of the marked terminals occurs. -/
theorem sample_bounds (m : ℕ) (b : Fin r × Bool ↪ V) :
    let K := Fintype.card (Fin r ↪ Fin m)
    let L := K * Fintype.card V ^ (2*m-2*r)
    let E := (pathSamples m b).card
    let C := (collisions (S := Fin m × Bool) b).card
    E ≤ L + C ∧ L ≤ E + K*C := by
  classical
  let Z (a : Fin r ↪ Fin m) := pinned (slots a) b
  let G (a : Fin r ↪ Fin m) := (Z a).filter Injective
  let U := univ.biUnion G
  let C := collisions (S := Fin m × Bool) b
  have hU : U ⊆ pathSamples m b := by
    intro g hg
    obtain ⟨a,_,ha⟩ := mem_biUnion.mp hg
    exact match_of_pinned (mem_filter.mp ha).2 (mem_filter.mp ha).1
  have hE : pathSamples m b ⊆ U ∪ C := by
    intro g hg
    by_cases hi : Injective g
    · obtain ⟨a,ha⟩ := pinned_of_match hi hg
      exact mem_union_left _ (mem_biUnion.mpr ⟨a,mem_univ _,mem_filter.mpr ⟨ha,hi⟩⟩)
    exact mem_union_right _ (mem_collisions.mpr ⟨hi,pins_of_paths hg⟩)
  have hZ (a : Fin r ↪ Fin m) : Z a ⊆ G a ∪ C := by
    intro g hg
    by_cases hi : Injective g
    · exact mem_union_left _ (mem_filter.mpr ⟨hg,hi⟩)
    exact mem_union_right _ (mem_collisions.mpr ⟨hi,fun t ↦ ⟨slots a t,mem_pinned.mp hg t⟩⟩)
  have dis : (↑(univ : Finset (Fin r ↪ Fin m)) : Set _).PairwiseDisjoint G := by
    intro a _ a' _ hn
    apply disjoint_left.mpr
    intro g hg hg'
    exact hn (placement_unique (mem_filter.mp hg).2 (mem_filter.mp hg).1 (mem_filter.mp hg').1)
  have sumG : ∑ a, (G a).card = U.card := (card_biUnion dis).symm
  have sumZ : ∑ a, (Z a).card = Fintype.card (Fin r ↪ Fin m) * Fintype.card V ^ (2*m-2*r) := by
    simp [Z,pinned_card,Nat.mul_comm]
  constructor
  · have hu : U.card ≤ ∑ a, (Z a).card := by
      rw [← sumG]
      exact sum_le_sum fun a _ ↦ card_le_card (filter_subset _ _)
    exact (card_le_card hE).trans ((card_union_le ..).trans (Nat.add_le_add_right (sumZ ▸ hu) _))
  · rw [← sumZ]
    calc
      _ ≤ ∑ a, ((G a).card+C.card) := sum_le_sum fun a _ ↦ (card_le_card (hZ a)).trans (card_union_le ..)
      _ = U.card + Fintype.card (Fin r ↪ Fin m)*C.card := by simp [sum_add_distrib,sumG]
      _ ≤ _ := Nat.add_le_add_right (card_le_card hU) _

end LeanderLinusson
