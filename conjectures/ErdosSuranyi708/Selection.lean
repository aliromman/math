module

public import conjectures.ErdosSuranyi708.FiniteLP

@[expose] public section
namespace ErdosSuranyi708
open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private def matrixScore (a : κ → ι → ℕ) (w : κ → ℝ) (i : ι) : ℝ :=
  ∑ p, w p * a p i

omit [Fintype ι] in
private lemma clip_site (a : κ → ι → ℕ) (w : κ → ℝ) (hw : ∀ p, 0 ≤ w p) (i : ι) :
    max (matrixScore a w i - 1) 0 = max (matrixScore a (fun p => min (w p) 1) i - 1) 0 +
      (matrixScore a w i - matrixScore a (fun p => min (w p) 1) i) := by
  classical
  let c := matrixScore a (fun p => min (w p) 1) i
  have hle : c ≤ matrixScore a w i :=
    sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
  change max (_ - 1) 0 = max (c - 1) 0 + (_ - c)
  by_cases hc : 1 ≤ c
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · have heq : matrixScore a w i = c := by
      apply sum_congr rfl
      intro p hp
      by_cases h : a p i = 0
      · simp [h]
      have hone : (1 : ℝ) ≤ a p i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      have ht : min (w p) 1 * (a p i : ℝ) ≤ c := single_le_sum
        (fun j _ => mul_nonneg (le_min (hw j) zero_le_one) (Nat.cast_nonneg (a j i))) hp
      have hwp : w p ≤ 1 := by
        by_contra! hh
        rw [min_eq_right hh.le, one_mul] at ht
        linarith
      simp [min_eq_left hwp]
    rw [heq, sub_self, add_zero]

private lemma clip_objective (a : κ → ι → ℕ) (d w : κ → ℝ)
    (hw : ∀ p, 0 ≤ w p) (hcap : ∀ p, d p ≤ ∑ i, (a p i : ℝ)) :
    (∑ p, w p * d p) - ∑ i, max (matrixScore a w i - 1) 0 ≤
    (∑ p, min (w p) 1 * d p) - ∑ i, max (matrixScore a (fun p => min (w p) 1) i - 1) 0 := by
  let v := fun p => w p - min (w p) 1
  have hmain : (∑ p, v p * d p) ≤ ∑ i, matrixScore a v i := by
    calc
      _ ≤ ∑ p, v p * ∑ i, (a p i : ℝ) := sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (hcap p) (sub_nonneg.mpr (min_le_left _ _))
      _ = _ := by simp only [matrixScore, mul_sum]; rw [sum_comm]
  simp only [v, matrixScore, sub_mul, sum_sub_distrib] at hmain
  simp_rw [clip_site a w hw, sum_add_distrib, sum_sub_distrib]
  unfold matrixScore
  linarith

/-- A common upper bound for the boxed dual gives a selection of sites. Rounding
one fractional site for each row suffices. -/
theorem select_of_dual (a : κ → ι → ℕ) (d : κ → ℝ) (C : ℝ)
    (hcap : ∀ p, d p ≤ ∑ i, (a p i : ℝ))
    (hdual : ∀ w : κ → ℝ, (∀ p, 0 ≤ w p ∧ w p ≤ 1) →
      (∑ p, w p * d p) - ∑ i, max ((∑ p, w p * a p i) - 1) 0 ≤ C) :
    ∃ B : Finset ι, (B.card : ℝ) ≤ C + Fintype.card κ ∧
      ∀ p, d p ≤ ∑ i ∈ B, (a p i : ℝ) := by
  classical
  have hfrac : ∃ y : ι → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
      (∀ p, d p ≤ ∑ i, (a p i : ℝ) * y i) ∧ ∑ i, y i ≤ C := by
    by_contra hnon
    have hr (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
        (hy' : ∀ p, d p ≤ ∑ i, (a p i : ℝ) * y i) : C < ∑ i, y i :=
      lt_of_not_ge fun hc => hnon ⟨y, hy, hy', hc⟩
    obtain ⟨w, hw, hgt⟩ := separating_dual (fun p i => (a p i : ℝ)) d C
      ⟨fun _ => 1, fun _ => ⟨zero_le_one, le_rfl⟩, by simpa using hcap⟩ hr
    exact (not_le_of_gt hgt) ((clip_objective a d w hw hcap).trans
      (hdual _ fun p => ⟨le_min (hw p) zero_le_one, min_le_right _ _⟩))
  obtain ⟨y, hy, hrows, hcost⟩ := hfrac
  obtain ⟨z, hz, hsame, hsum, hcount⟩ := cube_round (fun p i => (a p i : ℝ)) y hy
  let B := univ.filter (fun i => 0 < z i)
  refine ⟨B, ?_, ?_⟩
  · have hb : (B.card : ℝ) ≤ (∑ i, z i) + (fractionalIndices z).card := by
      simp only [B, fractionalIndices, ← sum_boole, ← sum_add_distrib]
      apply sum_le_sum
      intro i _
      have hi := hz i
      split_ifs <;> simp_all
    exact hb.trans (add_le_add (hsum.trans hcost) (by exact_mod_cast hcount))
  · intro p
    apply (hrows p).trans
    rw [← hsame p]
    simp only [B, sum_filter]
    apply sum_le_sum
    intro i _
    by_cases h : 0 < z i
    · rw [ite_eq_left h]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hz i).2
    · rw [ite_eq_right h, le_antisymm (le_of_not_gt h) (hz i).1, mul_zero]

end ErdosSuranyi708
