module

public import conjectures.LayeredWordPacking.Statement

namespace LayeredWordPacking

private def family : Finset (List ℕ) := {[0, 0, 0, 1, 2], [0, 2, 1, 1, 1], [0, 0, 2, 1, 1]}
private def witness : List ℕ := [0, 0, 0, 2, 3, 1, 1, 1, 1]

private theorem patterns_family : Patterns 3 5 family := by
  intro p hp
  simp only [family, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> unfold IsWord <;> decide

private def words (k : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (words k n).flatMap fun w =>
    ((List.range k).map (· :: w)).filter layered

private theorem mem_words {k n : ℕ} {w : List ℕ} (hw : IsWord k n w) (hl : layered w) :
    w ∈ words k n := by
  obtain ⟨hn, ha⟩ := hw
  induction w generalizing n with
  | nil => subst n; simp [words]
  | cons a w ih =>
    subst n
    have ht : layered w := (Bool.and_eq_true_iff.mp hl).2
    apply List.mem_flatMap.mpr
    refine ⟨w, ih ht rfl (fun x hx => ha x (by simp [hx])), ?_⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨a, List.mem_range.mpr (ha a (by simp)), rfl⟩, hl⟩

private theorem all_scores : (words 4 9).all (fun w => score 5 family w ≤ 60) := by
  decide +kernel

private theorem no_maximizer : ¬ LayeredMaximizer family 5 4 9 := by
  rintro ⟨w, hw, hl, hmax⟩
  have hu := List.all_eq_true.mp all_scores w (mem_words hw hl)
  have h := hmax witness (by unfold IsWord witness; decide)
  have hw' : score 5 family witness = 61 := by decide +kernel
  rw [hw'] at h
  change decide (score 5 family w ≤ 60) = true at hu
  have := of_decide_eq_true hu
  omega

public theorem counterexample : ¬ Conjecture := by
  intro h
  exact no_maximizer (h 3 5 4 9 (by decide) (by decide) (by decide) (by decide) family patterns_family)

public theorem original_counterexample : ¬ OriginalConjecture := by
  intro h
  exact no_maximizer ((h 3 5 (by decide) (by decide) family patterns_family).2 4 9 (by decide) (by decide))

/-- info: 'LayeredWordPacking.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample

/-- info: 'LayeredWordPacking.original_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms original_counterexample

end LayeredWordPacking
