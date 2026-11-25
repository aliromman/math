module

public import conjectures.SplitMatroidFlags.Exchange
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

@[expose] public section

namespace SplitMatroidFlags

open Finset

variable {E : Type} [Fintype E] [DecidableEq E] {B : Finset (Finset E)} {b : Finset E}

def neighbors (B : Finset (Finset E)) (b : Finset E) (j : E) := b.filter fun i => Swap B b i j

omit [Fintype E] in
lemma mem_neighbors {i j : E} : i ∈ neighbors B b j ↔ Swap B b i j := by
  simp only [neighbors,mem_filter]
  exact ⟨And.right,fun h => ⟨h.1,h⟩⟩

def pattern (B : Finset (Finset E)) (b T : Finset E) (u : E → ℕ) : Finset (E × E) :=
  univ.filter fun (i,j) => j ∈ T ∧ Swap B b i j ∧ ∀ k ∈ neighbors B b j, u i ≤ u k

noncomputable def activeEdges (B : Finset (Finset E)) (b : Finset E) (w : E → ℝ) : Finset (E × E) := by
  classical exact univ.filter fun (i,j) => tight B b w i j

lemma mem_activeEdges {w : E → ℝ} (i j : E) : (i,j) ∈ activeEdges B b w ↔ tight B b w i j := by
  classical simp [activeEdges]

lemma mem_pattern {T : Finset E} {u : E → ℕ} (i j : E) :
    (i,j) ∈ pattern B b T u ↔ j ∈ T ∧ Swap B b i j ∧ ∀ k ∈ neighbors B b j, u i ≤ u k := by simp [pattern]

/-- Realize the prescribed ties by lowering each inactive outside weight below all basis weights. -/
lemma realize_pattern (hb : b ∈ B) (hm : HasMatches B b) (T : Finset E) (u : E → ℕ) :
    ∃ w : E → ℝ, Maximizes B w b ∧ activeEdges B b w = pattern B b T u := by
  let vals j := (neighbors B b j).image u
  let w (i : E) : ℝ := if i ∈ b then u i else
    if i ∈ T then (if h : (vals i).Nonempty then ((vals i).min' h : ℝ) else -1) else -1
  have selected {i j : E} (hs : Swap B b i j) :
      w j ≤ w i ∧ (w j = w i ↔ j ∈ T ∧ ∀ k ∈ neighbors B b j, u i ≤ u k) := by
    have hi : u i ∈ vals j := mem_image_of_mem u (mem_neighbors.mpr hs)
    have hn : (vals j).Nonempty := ⟨_,hi⟩
    have hl := min'_le _ _ hi
    by_cases hT : j ∈ T
    · simp only [w,hs.1,hs.2.1,hT,ite_true,ite_false,dite_eq_left hn,true_and]
      refine ⟨by exact_mod_cast hl,?_⟩
      rw [Nat.cast_inj]
      constructor
      · intro he k hk
        exact he ▸ min'_le _ _ (mem_image_of_mem u hk)
      · intro he
        obtain ⟨k,hk,eq⟩ := mem_image.mp (min'_mem (vals j) hn)
        exact hl.antisymm (eq ▸ he k hk)
    · simp only [w,hs.1,hs.2.1,hT,ite_true,ite_false,false_and,iff_false]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (u i)]
  refine ⟨w,(maximizes_iff hb hm).mpr (fun _ _ h => (selected h).1),?_⟩
  ext ⟨i,j⟩
  rw [mem_activeEdges,mem_pattern]
  constructor
  · rintro ⟨hs,he⟩
    obtain ⟨hT,hu⟩ := (selected hs).2.mp he
    exact ⟨hT,hs,hu⟩
  · rintro ⟨hT,hs,hu⟩
    exact ⟨hs,(selected hs).2.mpr ⟨hT,hu⟩⟩

/-- The rank of a basis weight among the different weights on that basis. -/
noncomputable def level (b : Finset E) (w : E → ℝ) (i : E) : ℕ := ((b.image w).filter (· < w i)).card

omit [Fintype E] [DecidableEq E] in
lemma level_compare {w : E → ℝ} {i j : E} (hi : i ∈ b) (hj : j ∈ b) :
    level b w i ≤ level b w j ↔ w i ≤ w j := by
  classical
  have strict {a c : E} (ha : a ∈ b) (h : w a < w c) : level b w a < level b w c := by
    apply card_lt_card
    apply ssubset_iff_subset_ne.mpr
    refine ⟨fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.trans h⟩,?_⟩
    intro he
    have hh : w a ∈ (b.image w).filter (· < w c) := mem_filter.mpr ⟨mem_image_of_mem w ha,h⟩
    rw [← he] at hh
    exact lt_irrefl _ (mem_filter.mp hh).2
  constructor
  · intro h
    exact le_of_not_gt (fun bad => (not_lt_of_ge h) (strict hj bad))
  · intro h
    rcases h.eq_or_lt with eq | lt
    · simp [level,eq]
    · exact (strict hi lt).le

omit [Fintype E] [DecidableEq E] in
lemma level_lt {w : E → ℝ} {i : E} (hi : i ∈ b) : level b w i < b.card := by
  classical
  refine lt_of_lt_of_le ?_ (card_image_le : (b.image w).card ≤ _)
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨filter_subset ..,?_⟩
  intro he
  have h := mem_image_of_mem w hi
  rw [← he] at h
  exact lt_irrefl _ (mem_filter.mp h).2

lemma every_pattern {w : E → ℝ} (hm : HasMatches B b) (hb : Maximizes B w b) :
    ∃ T ⊆ univ \ b, activeEdges B b w = pattern B b T (level b w) := by
  classical
  let T := (univ \ b).filter fun j => ∃ i ∈ neighbors B b j, w i = w j
  refine ⟨T,filter_subset ..,?_⟩
  ext ⟨i,j⟩
  rw [mem_activeEdges,mem_pattern]
  have loc := (maximizes_iff hb.1 hm).mp hb
  constructor
  · rintro ⟨hs,he⟩
    refine ⟨mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hs.2.1⟩,i,mem_neighbors.mpr hs,he.symm⟩,hs,?_⟩
    intro k hk
    have hsk := mem_neighbors.mp hk
    exact (level_compare hs.1 hsk.1).mpr (he ▸ loc _ _ hsk)
  · rintro ⟨hT,hs,hu⟩
    obtain ⟨k,hk,he⟩ := (mem_filter.mp hT).2
    have le := (level_compare hs.1 (mem_neighbors.mp hk).1).mp (hu _ hk)
    exact ⟨hs,le_antisymm (loc _ _ hs) (he ▸ le)⟩

end SplitMatroidFlags
