module

public import conjectures.BipartiteScoreSets.Allocation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring

public section
namespace BipartiteScoreSets
open Finset

private theorem odd_fill {M R : ℕ} {D : Finset ℕ} (sub : D ⊆ range M)
    (zero : 0 ∉ D) (oddSum : (∑ d ∈ D, d) % 2 = 1)
    (room : 2 * ((range M) \ D).card ≤ R) (oddR : R % 2 = 1) :
    ∃ d ∈ D, d % 2 = 1 ∧ d + 2 ≤ R := by
  let O := D.filter (fun d => d % 2 = 1)
  have existsOdd : O.Nonempty := by
    by_contra h
    have he (x) (hx : x ∈ D) : x % 2 = 0 := by
      by_contra hn
      exact h ⟨x, mem_filter.mpr ⟨hx, by omega⟩⟩
    rw [sum_nat_mod, sum_eq_zero (fun x hx => he x hx)] at oddSum
    contradiction
  let d := O.min' existsOdd
  obtain ⟨hd, parity⟩ := mem_filter.mp (O.min'_mem existsOdd)
  have cnt := card_le_card_of_injOn (s := range (d / 2 + 1)) (t := range M \ D)
    (fun i : ℕ => if i = 0 then 0 else 2 * i - 1) (by
      intro i hi
      have hi' := mem_range.mp hi
      have hd' := mem_range.mp (sub hd)
      by_cases iz : i = 0
      · simp [iz, zero, show 0 < M by omega]
      · simp only [ite_eq_right iz, SetLike.mem_coe, mem_sdiff, mem_range]
        refine ⟨by omega, fun hh => ?_⟩
        have sm := O.min'_le _ (mem_filter.mpr ⟨hh, by omega⟩)
        change d ≤ _ at sm
        omega) (by
      intro a _ b _ hab
      dsimp only at hab
      split_ifs at hab <;> omega)
  rw [card_range] at cnt
  exact ⟨d, hd, parity, by omega⟩

/-- The right part has at most one more than half the maximum score. Every vertex
in that part has the maximum score. -/
theorem uniform_realization (S : Finset ℕ) (ne : S.Nonempty) (pos : ∀ a ∈ S, 0 < a) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ n ≤ S.max' ne / 2 + 1 ∧
      ∃ G : Orientation m n, scores G = S ∧ ∀ j, ∑ i, (G i j : ℕ) = S.max' ne := by
  let M := S.max' ne
  have hM : M ∈ S := S.max'_mem ne
  have maximal (a) (ha : a ∈ S) : a ≤ M := S.le_max' a ha
  have hp := pos M hM
  let D := (range M).filter (fun d => 0 < d ∧ M - d ∈ S)
  have memD {d : ℕ} : d ∈ D ↔ d < M ∧ 0 < d ∧ M - d ∈ S := by simp [D]
  have sub : D ⊆ range M := filter_subset _ _
  let E := range M \ D
  let T := ∑ d ∈ E, d
  let U := ∑ d ∈ D, d
  have parts : T + U = ∑ d ∈ range M, d := sum_sdiff sub
  have sizes : E.card + D.card = M := by
    simpa [E] using card_sdiff_add_card_eq_card sub
  have go (n c : ℕ) (hn : 0 < n) (w : M + c = 2 * n) (short : n ≤ M / 2 + 1) (extra : List ℕ)
      (allowed : ∀ d ∈ extra, d = 0 ∨ d ∈ D)
      (total : (∑ d ∈ D, (d + c)) + (extra.map (· + c)).sum = n * M) :
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ n ≤ M / 2 + 1 ∧
        ∃ G : Orientation m n, scores G = S ∧ ∀ j, ∑ i, (G i j : ℕ) = M := by
    obtain ⟨m, hm, G, eq, uniform⟩ := realize hM hp maximal hn w (D.toList ++ extra) (by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨lt, _, hs⟩ := memD.mp (mem_toList.mp hd)
        exact ⟨lt.le, hs⟩
      · rcases allowed d hd with rfl | hd
        · simpa using And.intro (Nat.zero_le M) hM
        · obtain ⟨lt, _, hs⟩ := memD.mp hd
          exact ⟨lt.le, hs⟩) (by
      intro a ha hne
      have := pos a ha
      have := maximal a ha
      exact List.mem_append_left _ (mem_toList.mpr (memD.mpr ⟨by omega, by omega, by
        convert ha using 1; omega⟩))) (by simpa [sum_map_toList] using total)
    exact ⟨m, n, hm, hn, short, G, eq, uniform⟩
  let h := M / 2
  rcases (show M = 2 * h + 1 ∨ M = 2 * h by dsimp [h]; omega) with odd | even
  · let A := ∑ d ∈ D, (d + 1)
    have bound : A ≤ (h + 1) * M := by
      calc
        A ≤ ∑ d ∈ range M, (d + 1) := sum_le_sum_of_subset sub
        _ = (h + 1) * M := by
          rw [sum_add_distrib]
          simp only [sum_const, card_range, smul_eq_mul, mul_one]
          have ar := sum_range_id_mul_two M
          rw [show M - 1 = 2 * h by omega] at ar
          rw [show M * (2 * h) = 2 * (h * M) by ring] at ar
          rw [Nat.add_mul, Nat.one_mul]
          omega
    apply go (h + 1) 1 (by omega) (by omega) (by rfl) (List.replicate ((h + 1) * M - A) 0)
    · intro x hx
      exact Or.inl (List.mem_replicate.mp hx).2
    · simp [List.sum_replicate, A, Nat.add_sub_of_le bound]
  · have hh : 0 < h := by omega
    have arithmetic : T + U + h = h * M := by
      have ar := sum_range_id_mul_two M
      have step : M - 1 + 1 = M := by omega
      have ar' : (∑ i ∈ range M, i) * 2 + M = M * M := by
        rw [ar, ← Nat.mul_succ, Nat.succ_eq_add_one, step]
      have mprod : M * M = 2 * (h * M) := by
        calc M * M = (2 * h) * M := congrArg (· * M) even
             _ = _ := by ring
      omega
    by_cases sparse : T < h
    · have hd : h + T ∈ D := by
        by_contra hnot
        have inE : h + T ∈ E := mem_sdiff.mpr ⟨mem_range.mpr (by omega), hnot⟩
        have le : h + T ≤ T := single_le_sum (fun (d : ℕ) _ => Nat.zero_le d) inE
        omega
      apply go h 0 hh (by omega) (Nat.le_succ _) [h + T]
      · simpa using Or.inr (a := h + T = 0) hd
      · simp only [Nat.add_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        change U + _ = _
        omega
    · let R := T + 2 * E.card - h
      have rm : 2 * E.card ≤ R := by dsimp [R]; omega
      have budget : (∑ d ∈ D, (d + 2)) + R = (h + 1) * M := by
        rw [sum_add_distrib, Nat.add_mul, Nat.one_mul]
        simp only [sum_const, smul_eq_mul]
        change U + _ + R = _
        dsimp [R]
        omega
      by_cases parity : R % 2 = 0
      · apply go (h + 1) 2 (by omega) (by omega) (by rfl) (List.replicate (R / 2) 0)
        · intro x hx
          exact Or.inl (List.mem_replicate.mp hx).2
        · simpa [List.sum_replicate, smul_eq_mul, show R / 2 * 2 = R by omega] using budget
      · have oddU : U % 2 = 1 := by
          rw [sum_add_distrib, even] at budget
          simp only [sum_const, smul_eq_mul] at budget
          change U + _ + R = _ at budget
          rw [show (h + 1) * (2 * h) = 2 * ((h + 1) * h) by ring] at budget
          omega
        obtain ⟨d, hd, od, le⟩ := odd_fill sub (by simp [D]) oddU rm (by omega)
        apply go (h + 1) 2 (by omega) (by omega) (by rfl) (d :: List.replicate ((R - (d + 2)) / 2) 0)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inr hd
          · exact Or.inl (List.mem_replicate.mp hx).2
        · simp only [List.map_cons, List.map_replicate, List.sum_cons, List.sum_replicate,
            Nat.zero_add, smul_eq_mul]
          omega

theorem resolution : Conjecture := by
  intro S ne pos
  obtain ⟨m, n, hm, hn, _, G, eq, _⟩ := uniform_realization S ne pos
  exact ⟨m, n, hm, hn, G, eq⟩

/-- A singleton score set attains the worst possible size of the smaller right part. -/
theorem singleton_lower {M m n : ℕ} (hp : 0 < M) (hn : 0 < n) (G : Orientation m n)
    (onlyScore : scores G = {M}) : M / 2 + 1 ≤ n := by
  by_contra! tooSmall
  have zeroEntry (i : Fin m) (j : Fin n) : (G i j : ℕ) = 0 := by
    have row : ∑ l, (2 - (G i l : ℕ)) ∈ scores G :=
      mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
    rw [onlyScore, mem_singleton, sum_tsub_distrib _ (fun l _ => by have := (G i l).isLt; omega)] at row
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at row
    have le := single_le_sum (f := fun l => (G i l : ℕ)) (fun _ _ => Nat.zero_le _) (mem_univ j)
    omega
  let j : Fin n := ⟨0, hn⟩
  have col : ∑ i, (G i j : ℕ) ∈ scores G :=
    mem_union_right _ (mem_image.mpr ⟨j, mem_univ _, rfl⟩)
  simp [onlyScore, zeroEntry] at col
  omega

/-- info: 'BipartiteScoreSets.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end BipartiteScoreSets
