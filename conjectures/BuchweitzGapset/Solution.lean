module

public import conjectures.BuchweitzGapset.Statement
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Tactic.IntervalCases

open scoped Pointwise
namespace BuchweitzGapset

private abbrev I (a b : ℤ) := Finset.Icc a b
private def gaps := I 1 35 ∪ I 42 42 ∪ I 46 46 ∪ I 65 66 ∪ I 70 71
private def twice := I 2 108 ∪ I 111 113 ∪ I 116 117 ∪ I 130 132 ∪ I 135 137 ∪ I 140 142
private def thrice := I 3 179 ∪ I 181 184 ∪ I 186 188 ∪ I 195 198 ∪ I 200 203 ∪ I 205 208 ∪ I 210 213

private theorem gapset : IsGapset gaps := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [gaps, I, Finset.mem_union, Finset.mem_Icc] at hx
    omega
  · intro u v hu hv
    by_cases uz : u = 0
    · simpa [uz] using hv
    by_cases vz : v = 0
    · simpa [vz] using hu
    simp only [gaps, I, Finset.mem_union, Finset.mem_Icc, Nat.cast_add] at hu hv ⊢
    omega

private theorem add_I {a b c d : ℤ} (h : a ≤ b) (h' : c ≤ d) :
    I a b + I c d = I (a+c) (b+d) := by
  apply Finset.coe_injective
  simpa [I] using Set.Icc_add_Icc h h'

private theorem layers :
    gaps + gaps = twice ∧ twice + gaps = thrice ∧ thrice + gaps = I 4 284 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [gaps, twice, thrice, Finset.union_add, Finset.add_union, add_I] <;>
    ext x <;> simp only [I, Finset.mem_union, Finset.mem_Icc] <;> omega

set_option maxRecDepth 4096 in
private theorem counts : beta gaps 2 = 1 ∧ beta gaps 3 = 0 ∧ beta gaps 4 = 1 := by
  have h1 : sums gaps 1 = gaps := zero_add gaps
  have h2 : sums gaps 2 = twice := by
    change sums gaps 1 + gaps = twice
    rw [h1, layers.1]
  have h3 : sums gaps 3 = thrice := by
    change sums gaps 2 + gaps = thrice
    rw [h2, layers.2.1]
  have h4 : sums gaps 4 = I 4 284 := by
    change sums gaps 3 + gaps = I 4 284
    rw [h3, layers.2.2]
  simp only [beta, h2, h3, h4]
  decide

private theorem sum_bounds (n : ℕ) :
    sums gaps n ⊆ Finset.Icc (n : ℤ) (71 * (n : ℤ)) := by
  induction n with
  | zero => simp [sums]
  | succ n ih =>
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨hl, hh⟩ := Finset.mem_Icc.mp (ih hu)
    simp only [gaps, I, Finset.mem_union, Finset.mem_Icc] at hv
    apply Finset.mem_Icc.mpr
    push_cast
    omega

private theorem tail {n : ℕ} (hn : 5 ≤ n) : beta gaps n ≤ 0 := by
  have hc := Finset.card_le_card (sum_bounds n)
  rw [Int.card_Icc] at hc
  have hg : gaps.card = 41 := by decide
  unfold beta
  rw [hg]
  omega

/-- This gapset has precisely two Buchweitz obstructions, in orders two and four. -/
public theorem exact_example : ∃ A : Finset ℤ, IsGapset A ∧ obstruction A = {2, 4} := by
  refine ⟨gaps, gapset, ?_⟩
  ext n
  simp only [obstruction, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hn : 5 ≤ n
  · have := tail hn
    omega
  · have hc := counts
    interval_cases n <;> simp at * <;> omega

public theorem gapset_resolution : ¬ GapsetConjecture := by
  intro h
  obtain ⟨A, hA, hB⟩ := exact_example
  have hi := h A hA
  rw [hB] at hi
  have hm := hi.out (x := 2) (by decide) (y := 4) (by decide)
    (show 3 ∈ Set.Icc (2 : ℕ) 4 by decide)
  simp at hm

public theorem resolution : ¬ Conjecture :=
  fun h => gapset_resolution (fun A _ => h A)

/-- The excess of this numerical semigroup gapset has a strict valley at order three. -/
public theorem nonunimodal_gapset : ∃ A : Finset ℤ, IsGapset A ∧ ¬ UnimodalExcess A := by
  refine ⟨gaps, gapset, ?_⟩
  intro h
  have valley := h 2 3 4 (by decide) (by decide) (by decide)
  rw [counts.1, counts.2.1, counts.2.2] at valley
  exact (by decide : ¬ min (1 : ℤ) 1 ≤ 0) valley

public theorem unimodality_resolution : ¬ UnimodalityQuestion := by
  obtain ⟨A, _, hA⟩ := nonunimodal_gapset
  exact fun h => hA (h A)

/-- info: 'BuchweitzGapset.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end BuchweitzGapset
