module

public import conjectures.BipartiteScoreSets.Statement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Basic

public section
namespace BipartiteScoreSets

private theorem laps {n : ℕ} (hn : 0 < n) (s : ℕ) :
    ∑ j : Fin n, (s + j.val) / n = s := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (s + j) / n)]
  induction s with
  | zero =>
    apply Finset.sum_eq_zero
    intro j hj
    simpa using Nat.div_eq_of_lt (Finset.mem_range.mp hj)
  | succ s ih =>
    have h := Finset.sum_range_succ' (fun j => (s + j) / n) n
    rw [Finset.sum_range_succ, Nat.add_zero, Nat.add_div_right _ hn, ih] at h
    have swap : (∑ j ∈ Finset.range n, (s + (j + 1)) / n) =
        ∑ j ∈ Finset.range n, (s + 1 + j) / n :=
      Finset.sum_congr rfl fun j _ => congrArg (· / n) (by omega)
    rw [swap] at h
    omega

/-- Deal consecutive units cyclically to the right vertices. An entry receives at most two. -/
private theorem deal {n c : ℕ} (hn : 0 < n) (L : List ℕ)
    (small : ∀ d ∈ L, d + c ≤ 2 * n) (s : ℕ) :
    ∃ G : Orientation L.length n,
      (∀ i, ∑ j, (G i j : ℕ) = L.get i + c) ∧
      ∀ j, (∑ i, (G i j : ℕ)) + (s + j.val) / n =
        (s + (L.map (· + c)).sum + j.val) / n := by
  induction L generalizing s with
  | nil => exact ⟨Fin.elim0, by simp, by simp⟩
  | cons a L ih =>
    have ha := small a (by simp)
    obtain ⟨G, row, col⟩ := ih (fun d hd => small d (by simp [hd])) (s + (a + c))
    let before (j : Fin n) := (s + j.val) / n
    let after (j : Fin n) := (s + (a + c) + j.val) / n
    have low (j) : before j ≤ after j := Nat.div_le_div_right (by omega)
    have high (j) : after j ≤ before j + 2 := by
      dsimp [before, after]
      rw [← Nat.add_mul_div_left _ 2 hn]
      exact Nat.div_le_div_right (by omega)
    let head (j : Fin n) : Fin 3 := ⟨after j - before j, by have := high j; omega⟩
    refine ⟨Fin.cons head G, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · change ∑ j, (after j - before j) = a + c
        rw [Finset.sum_tsub_distrib _ (fun j _ => low j), laps hn, laps hn]
        omega
      · simpa using row k
    · intro j
      change (∑ i : Fin (L.length + 1), (Fin.cons (α := fun _ => Fin n → Fin 3)
        head G i j : ℕ)) + (s + j.val) / n = _
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, List.map_cons, List.sum_cons]
      have h := col j
      change after j - before j + _ + before j = _
      have hlow := low j
      dsimp [after, before] at *
      simp only [Nat.add_assoc] at *
      omega

theorem realize {S : Finset ℕ} {M n c : ℕ} (hM : M ∈ S) (hpos : 0 < M)
    (maximal : ∀ a ∈ S, a ≤ M) (hn : 0 < n) (width : M + c = 2 * n)
    (L : List ℕ) (valid : ∀ d ∈ L, d ≤ M ∧ M - d ∈ S)
    (cover : ∀ a ∈ S, a ≠ M → M - a ∈ L)
    (total : (L.map (· + c)).sum = n * M) :
    ∃ m : ℕ, 0 < m ∧ ∃ G : Orientation m n, scores G = S ∧ ∀ j, ∑ i, (G i j : ℕ) = M := by
  have nonempty : 0 < L.length := by
    cases L with
    | nil => simp [Nat.ne_of_gt hn, Nat.ne_of_gt hpos] at total
    | cons => simp
  obtain ⟨G, row, col⟩ := deal (c := c) hn L (fun d hd => by have := (valid d hd).1; omega) 0
  have right (j : Fin n) : ∑ i, (G i j : ℕ) = M := by
    have h := col j
    simpa [total, Nat.add_comm (n * M), Nat.add_mul_div_left _ _ hn,
      Nat.div_eq_of_lt j.isLt] using h
  have left (i : Fin L.length) : ∑ j, (2 - (G i j : ℕ)) = M - L.get i := by
    rw [Finset.sum_tsub_distrib _ (fun j _ => by have := (G i j).isLt; omega), row]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  refine ⟨_, nonempty, G, ?_, right⟩
  ext a
  simp only [scores, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, left, right]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨_, rfl⟩)
    · exact (valid _ (List.get_mem L i)).2
    · exact hM
  · intro ha
    by_cases e : a = M
    · exact Or.inr ⟨⟨0, hn⟩, e.symm⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp (cover a ha e)
      exact Or.inl ⟨i, by rw [hi]; have := maximal a ha; omega⟩

end BipartiteScoreSets
