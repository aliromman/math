module

public import conjectures.ErdosSuranyi708.Terms

@[expose] public section
namespace ErdosSuranyi708
open Finset

/-- Every nonzero coefficient comes from a different subset of the tail primes. -/
theorem arithmeticCoeff_support (L : ℕ) (s : ℝ) (S : Finset ℕ) :
    ((Icc 1 L).filter (fun e ↦ arithmeticCoeff L s S e ≠ 0)).card ≤ 2^S.card := by
  let U := (Icc 1 L).filter (fun e ↦ arithmeticCoeff L s S e ≠ 0)
  have hs {e : ℕ} (he : e ∈ U) : e.primeFactors ⊆ S ∧ (∏ p ∈ e.primeFactors, p) = e := by
    by_contra hn
    exact (mem_filter.mp he).2 (by simp [arithmeticCoeff,hn])
  rw [← card_powerset]
  apply card_le_card_of_injOn Nat.primeFactors (fun e he ↦ mem_powerset.mpr (hs he).1)
  intro e he f hf eq
  rw [← (hs he).2, ← (hs hf).2, eq]

private theorem siftSum_small (x M d : ℕ) (hd : 0 < d) (D S : Finset ℕ)
    (hcop : (D : Set ℕ).Pairwise Nat.Coprime) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |siftSum 0 M d D (arithmeticCoeff (M/d) s S) -
      siftSum x M d D (arithmeticCoeff (M/d) s S)| ≤ (2:ℝ)^(D.card+S.card) := by
  let L := M/d
  let c := arithmeticCoeff L s S
  let U := (Icc 1 L).filter (fun e ↦ c e ≠ 0)
  have sub : U ⊆ Icc 1 L := filter_subset ..
  have hc := arithmeticCoeff_support L s S
  change U.card ≤ 2^S.card at hc
  have hreal : (U.card:ℝ) ≤ (2:ℝ)^S.card := by exact_mod_cast hc
  rw [abs_sub_comm, siftSum, siftSum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ Icc 1 L, if e ∈ U then (2:ℝ)^D.card else 0 :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e he ↦ by
        by_cases h : e ∈ U
        · rw [ite_eq_left h, ← mul_sub, abs_mul]
          have hh := (arithmeticCoeff_bound L hs S e).trans (pow_le_one₀ hs hs1)
          simpa only [one_mul] using mul_le_mul hh
            (siftCount_full x M (d*e) (Nat.mul_pos hd (mem_Icc.mp he).1) D hcop)
            (abs_nonneg _) zero_le_one
        · have hz : c e = 0 := by
            by_contra hn
            exact h (mem_filter.mpr ⟨he,hn⟩)
          change |c e * _ - c e * _| ≤ _
          simp [hz,h])
    _ = U.card * (2:ℝ)^D.card := by
      rw [← sum_filter]
      have eq : (Icc 1 L).filter (·∈U) = U := by
        ext e
        exact ⟨fun h ↦ (mem_filter.mp h).2,fun h ↦ mem_filter.mpr ⟨sub h,h⟩⟩
      simp [eq]
    _ ≤ _ := by rw [pow_add,mul_comm]; gcongr

namespace SeedIndex

/-- Each seed with second prime at most Y has a translation error bounded only by Y. -/
theorem small_difference {Y K M x : ℕ} {s : ℝ} {P : Finset ℕ} {w : ℕ → ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hp : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, 0 ≤ w p)
    (i : SeedIndex P (grid Y K M w)) (hsmall : i.second ≤ Y) :
    |(∑ b ∈ window 0 M, i.term Y M s w b) - ∑ b ∈ window x M, i.term Y M s w b| ≤
      (2:ℝ)^(Y+2) := by
  classical
  by_cases hn : i.coefficient Y M s w = 0
  · simp [term,hn]
  have pq := hp i.second (mem_filter.mp i.2.1.property).1
  have hlevel := i.second_le_level hp (i.retained_of_nonzero hn)
  have hL : 1 ≤ i.level M := pq.pos.trans_le hlevel
  have hA (p) (h : p ∈ i.required) := hp p (i.req_sub h)
  have hj (p) (h : p ∈ i.required) := And.intro (grid_positive (i.exponent_mem h)) (i.exponent_mem h)
  have hS (p) (h : p ∈ i.tail) := And.intro (hp p (i.tail_sub h)) ((i.tail_lt h).le.trans hlevel)
  let D := forbiddenPowers (grid Y K M w) i.required i.exponent
  have hD : D.card+i.tail.card ≤ Y+2 := by
    have h₁ := forbiddenPowers_card (grid Y K M w) i.required i.exponent
    change D.card ≤ i.required.card at h₁
    rw [i.required_card] at h₁
    have h₂ : i.tail.card+i.red.card = (earlier P i.second).card := card_sdiff_add_card_eq_card i.red_sub
    have h₃ : (earlier P i.second).card ≤ i.second := by
      calc
        _ ≤ (range i.second).card := card_le_card fun p h ↦ mem_range.mpr (mem_filter.mp h).2
        _ = _ := card_range _
    omega
  have hb := siftSum_small x M i.divisor (i.divisor_pos hp) D i.tail
    (forbiddenPowers_pairwise hA) hs hs1
  have ha := i.coefficient_bounds Y M hs hs1 hw
  simp only [term, ← mul_sum, ← mul_sub, abs_mul, abs_of_nonneg ha.1]
  simp only [level,divisor]
  rw [seedPolynomial_sum 0 M hL hA hj hS i.tail_disjoint,
    seedPolynomial_sum x M hL hA hj hS i.tail_disjoint]
  exact (mul_le_mul ha.2 hb (abs_nonneg _) zero_le_one).trans
    (by simpa only [one_mul] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hD))

/-- Above a fixed second-prime cutoff, the translation error is at most an
arbitrary fraction of the initial contribution, uniformly over all seeds. -/
theorem large_difference {s η : ℝ} (hs : 0 < s) (hs' : s < 1/2) (hη : 0 < η) :
    ∃ Y₀ : ℕ, ∀ {Y K M x : ℕ}, Y₀ ≤ Y → ∀ {P : Finset ℕ} {w : ℕ → ℝ},
    (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 0 ≤ w p) → ∀ i : SeedIndex P (grid Y K M w),
    Y < i.second →
    |(∑ b ∈ window 0 M, i.term Y M s w b) - ∑ b ∈ window x M, i.term Y M s w b| ≤
      η*∑ b ∈ window 0 M, i.term Y M s w b := by
  classical
  let k := 1-(s/(1-s))^2
  have hu : 0 < 1-s := by linarith
  have hu1 : 1-s ≤ 1 := by linarith
  have hk : 0 < k := by
    have hh : s/(1-s) < 1 := (div_lt_one hu).mpr (by linarith)
    exact sub_pos.mpr (pow_lt_one₀ (div_nonneg hs.le hu.le) hh (by decide))
  obtain ⟨N,hN⟩ := siftSum_relative hs hs' (mul_pos hη hk)
  refine ⟨N,?_⟩
  intro Y K M x hY P w hp hw i hq
  by_cases hn : i.coefficient Y M s w = 0
  · simp [term,hn]
  have hr := i.retained_of_nonzero hn
  have hlevel := i.second_le_level hp hr
  have pq := hp i.second (mem_filter.mp i.2.1.property).1
  have hL : 1 ≤ i.level M := pq.pos.trans_le hlevel
  have hA (p) (h : p ∈ i.required) := hp p (i.req_sub h)
  have hj (p) (h : p ∈ i.required) := And.intro (grid_positive (i.exponent_mem h)) (i.exponent_mem h)
  have hS (p) (h : p ∈ i.tail) := And.intro (hp p (i.tail_sub h)) ((i.tail_lt h).le.trans hlevel)
  let D := forbiddenPowers (grid Y K M w) i.required i.exponent
  let G := seedMean (1-s) D i.tail
  have hF : (i.required.card:ℝ) ≤ (Real.log (i.level M))^2+2 := by
    rw [i.required_card]; push_cast
    linarith only [hr.2.resolve_left hq.not_ge]
  have hD : (D.card:ℝ) ≤ (Real.log (i.level M))^2+2 :=
    (Nat.cast_le.mpr (forbiddenPowers_card (grid Y K M w) i.required i.exponent)).trans hF
  have hmean : MeanWeight G := seedMean_isMeanWeight hu.le hu1
    (fun _ h ↦ forbiddenPowers_primePow hA h) (fun _ h ↦ (hS _ h).1)
  have diff := hN x M i.divisor D (arithmeticCoeff (i.level M) s i.tail) G i.required
    (i.divisor_pos hp) (hY.trans (hq.le.trans hlevel)) (forbiddenPowers_pairwise hA)
    (fun _ h ↦ Nat.zero_lt_of_lt (forbiddenPowers_two hA h)) hD hF hmean
    (fun _ hp' hn' ↦ seedMean_prime_lower hu1 hA (fun _ h ↦ (hS _ h).1)
      (Nat.mem_primesLE.mp hp').2 hn') (fun e _ ↦ arithmeticCoeff_bound (i.level M) hs.le i.tail e)
  let f := seedPolynomial (i.level M) s (grid Y K M w) i.required i.exponent i.tail
  have hh : |(∑ b ∈ window 0 M, f b)-(∑ b ∈ window x M, f b)| ≤ η*∑ b ∈ window 0 M, f b := by
    rw [abs_sub_comm]
    calc
      _ = _ := by dsimp only [f,level,divisor]; rw [seedPolynomial_sum x M hL hA hj hS i.tail_disjoint,
        seedPolynomial_sum 0 M hL hA hj hS i.tail_disjoint]
      _ ≤ (η*k)*meanSum G (i.level M) := diff
      _ = η*(k*meanSum G (i.level M)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (seedPolynomial_mass_lo M hs hs' hA hj
        (fun _ h ↦ (hS _ h).1) i.tail_disjoint) hη.le
  have ha := (i.coefficient_bounds Y M hs.le (by linarith) hw).1
  simp only [term, ← mul_sum, ← mul_sub, abs_mul, abs_of_nonneg ha]
  exact (mul_le_mul_of_nonneg_left hh ha).trans_eq (by ring)

end SeedIndex
end ErdosSuranyi708
