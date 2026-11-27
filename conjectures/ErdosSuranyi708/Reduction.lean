module

public import conjectures.ErdosSuranyi708.Statement
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-! Wang's raw finite envelope uses one large prime and one cofactor per
removed input. Chen's formal proof of the cubic bound groups equal carriers
and counts multiples in an interval. We use these arguments below. -/

@[expose] public section
namespace ErdosSuranyi708
open Finset

/-- Keep the inputs whose prime divisors are at most the cutoff. -/
def smoothPart (A : Finset ℕ) (K : ℕ) : Finset ℕ :=
  A.filter fun a ↦ ∀ p ∈ a.primeFactors, p ≤ K

theorem window_multiples_lower (x M d : ℕ) :
    M / d ≤ ((window x M).filter (d ∣ ·)).card := by
  have eq : (window x M).filter (d ∣ ·) =
      ((Ioc 0 (x + M)).filter (d ∣ ·)) \ ((Ioc 0 x).filter (d ∣ ·)) := by
    ext n
    simp only [window, mem_filter, mem_Ioc, mem_sdiff]
    omega
  rw [eq, card_sdiff_of_subset, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div]
  · have := Nat.div_add_div_le_add_div (x := x) (y := M) (z := d)
    omega
  · intro n hn
    simp only [mem_filter, mem_Ioc] at hn ⊢
    omega

/-- Give every small factor a fresh multiple in the window. The factors are
indexed by their occurrences, so equal factors can occur more than once. -/
private theorem fill {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    {x M K : ℕ} {U : Finset ℕ} (hU : U ⊆ window x M)
    (hbudget : U.card + s.card ≤ K)
    (hq : ∀ i ∈ s, 0 < q i ∧ K * q i ≤ M) :
    ∃ B ⊆ window x M, B.card ≤ U.card + s.card ∧
      (∏ i ∈ s, q i) * (∏ u ∈ U, u) ∣ ∏ b ∈ B, b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨U, hU, by simp, by simp⟩
  | @insert i s hi ih =>
    have hs := card_insert_of_notMem hi
    obtain ⟨B, hB, hcard, hdvd⟩ := ih (by omega) (fun j hj ↦ hq j (mem_insert_of_mem hj))
    obtain ⟨hpos, hmul⟩ := hq i (mem_insert_self ..)
    have hmany := ((Nat.le_div_iff_mul_le hpos).mpr hmul).trans (window_multiples_lower x M (q i))
    obtain ⟨b, hb, hnew⟩ := exists_mem_notMem_of_card_lt_card
      (show B.card < ((window x M).filter (q i ∣ ·)).card by omega)
    obtain ⟨hwin, hdiv⟩ := mem_filter.mp hb
    refine ⟨insert b B, insert_subset hwin hB, ?_, ?_⟩
    · rw [card_insert_of_notMem hnew, hs]
      omega
    · rw [prod_insert hi, prod_insert hnew, mul_assoc]
      exact Nat.mul_dvd_mul hdiv hdvd

private theorem store_primes (s : Finset ℕ) (p : ℕ → ℕ) (x : ℕ)
    (hp : ∀ a ∈ s, (p a).Prime ∧ p a ∣ a) :
    (∏ a ∈ s, p a) ∣ ∏ b ∈ s.image (fun a ↦ a + x / p a * p a), b := by
  classical
  let f (a : ℕ) := a + x / p a * p a
  change (∏ a ∈ s, p a) ∣ ∏ b ∈ s.image f, b
  rw [← prod_fiberwise_of_maps_to (fun a ha ↦ mem_image_of_mem f ha) p]
  apply prod_dvd_prod_of_dvd
  intro b _
  let fiber := s.filter fun a ↦ f a = b
  change (∏ a ∈ fiber, p a) ∣ b
  have inj : Set.InjOn p ↑fiber := by
    intro a ha c hc heq
    have hfa := (mem_filter.mp ha).2
    have hfc := (mem_filter.mp hc).2
    change a + x / p a * p a = b at hfa
    change c + x / p c * p c = b at hfc
    rw [heq] at hfa
    omega
  change (∏ a ∈ fiber, id (p a)) ∣ b
  rw [← prod_image inj (f := id)]
  apply prod_primes_dvd
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hr
    exact Nat.prime_iff.mp (hp a (mem_filter.mp ha).1).1
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hr
    obtain ⟨hs, hfa⟩ := mem_filter.mp ha
    rw [← hfa]
    exact dvd_add (hp a hs).2 (dvd_mul_left _ _)

/-- Add the remaining inputs at a cost of at most two sites per input.
Distinct large primes can use the same site. Each cofactor gets a fresh site. -/
theorem peel {A B : Finset ℕ} {x M K : ℕ}
    (ha : ∀ a ∈ A, 0 < a ∧ a ≤ M) (hB : B ⊆ window x M)
    (hC : Covers (smoothPart A K) B)
    (hK : B.card + 2 * (A.card - (smoothPart A K).card) ≤ K) :
    ∃ T ⊆ window x M, Covers A T ∧ T.card ≤ B.card + 2 * (A.card - (smoothPart A K).card) := by
  classical
  let S := smoothPart A K
  let R := A \ S
  have hS : S ⊆ A := filter_subset ..
  have hR : R.card = A.card - S.card := card_sdiff_of_subset hS
  have large (a : ℕ) (har : a ∈ R) : ∃ p ∈ a.primeFactors, K < p := by
    obtain ⟨haa, hns⟩ := mem_sdiff.mp har
    change a ∉ A.filter _ at hns
    simp only [mem_filter, haa, true_and, not_forall, not_le] at hns
    obtain ⟨p, hp, hk⟩ := hns
    exact ⟨p, hp, hk⟩
  let prime (a : ℕ) := if h : a ∈ R then Classical.choose (large a h) else 1
  have hprime {a : ℕ} (h : a ∈ R) : prime a ∈ a.primeFactors ∧ K < prime a := by
    simpa [prime, h] using Classical.choose_spec (large a h)
  let f (a : ℕ) := a + x / prime a * prime a
  let U := B ∪ R.image f
  have hU : U ⊆ window x M := by
    refine union_subset hB ?_
    intro b hb
    obtain ⟨a, har, rfl⟩ := mem_image.mp hb
    obtain ⟨hpos, ham⟩ := ha a (mem_sdiff.mp har).1
    have hpa := Nat.dvd_of_mem_primeFactors (hprime har).1
    have hple := Nat.le_of_dvd hpos hpa
    have hrem := Nat.mod_lt x (Nat.prime_of_mem_primeFactors (hprime har).1).pos
    have hsum := Nat.mod_add_div x (prime a)
    have hlo := Nat.div_mul_le_self x (prime a)
    apply mem_Ioc.mpr
    dsimp [f]
    rw [mul_comm (prime a)] at hsum
    omega
  have huc : U.card ≤ B.card + R.card :=
    (card_union_le ..).trans (Nat.add_le_add_left card_image_le _)
  have hP : (∏ a ∈ R, prime a) ∣ ∏ b ∈ U, b := by
    apply (store_primes R prime x fun a h ↦
      ⟨Nat.prime_of_mem_primeFactors (hprime h).1, Nat.dvd_of_mem_primeFactors (hprime h).1⟩).trans
    exact prod_dvd_prod_of_subset _ _ id subset_union_right
  have hc : (∏ a ∈ R, prime a).Coprime (∏ a ∈ S, a) := by
    apply Nat.Coprime.prod_left
    intro a har
    apply Nat.Coprime.prod_right
    intro b hbs
    apply (Nat.prime_of_mem_primeFactors (hprime har).1).coprime_iff_not_dvd.mpr
    intro hd
    have hpos := (ha b (hS hbs)).1
    have hsmall := (mem_filter.mp hbs).2 (prime a)
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors (hprime har).1, hd, hpos.ne'⟩)
    exact (hprime har).2.not_ge hsmall
  have hbase := hc.mul_dvd_of_dvd_of_dvd hP (hC.trans (prod_dvd_prod_of_subset _ U id subset_union_left))
  let co (a : ℕ) := a / prime a
  have prod_co {a : ℕ} (har : a ∈ R) : co a * prime a = a :=
    Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors (hprime har).1)
  have hbudget : U.card + R.card ≤ K := by
    change B.card + 2 * (A.card - S.card) ≤ K at hK
    omega
  obtain ⟨T, ht, htc, htd⟩ := fill R co hU hbudget (by
    intro a har
    obtain ⟨hpos, ham⟩ := ha a (mem_sdiff.mp har).1
    have hmul := prod_co har
    have hlt := (hprime har).2
    exact ⟨by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hmul; omega,
      by calc K * co a ≤ co a * prime a := by nlinarith
              _ = a := hmul
              _ ≤ M := ham⟩)
  refine ⟨T, ht, ?_, ?_⟩
  · change (∏ a ∈ A, a) ∣ ∏ b ∈ T, b
    have mul_eq : (∏ a ∈ R, co a) * (∏ a ∈ R, prime a) = ∏ a ∈ R, a := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl (fun a ha ↦ prod_co ha)
    have full : (∏ a ∈ R, a) * (∏ a ∈ S, a) = ∏ a ∈ A, a := prod_sdiff hS
    rw [← full, ← mul_eq, mul_assoc]
    exact (Nat.mul_dvd_mul_left _ hbase).trans htd
  · change T.card ≤ B.card + 2 * (A.card - S.card)
    omega

private theorem crossing (l : List ℕ) {K : ℕ} (hK : 1 ≤ K)
    (h : ∀ p ∈ l, p ≤ K) (hk : K ≤ l.prod) :
    ∃ d, d ∣ l.prod ∧ K ≤ d ∧ d ≤ K ^ 2 := by
  induction l with
  | nil => exact ⟨1, one_dvd _, hk, by nlinarith⟩
  | cons p l ih =>
    by_cases hl : K ≤ l.prod
    · obtain ⟨d, hd, hlow, hhigh⟩ := ih (fun r hr ↦ h r (List.mem_cons_of_mem _ hr)) hl
      exact ⟨d, hd.trans (by simp), hlow, hhigh⟩
    · refine ⟨(p :: l).prod, dvd_rfl, hk, ?_⟩
      simpa [sq] using Nat.mul_le_mul (h p (by simp)) (le_of_lt (lt_of_not_ge hl))

private theorem split_smooth {a K M : ℕ} (ha : 0 < a) (ham : a ≤ M)
    (hK : 1 ≤ K) (hc : K ^ 3 ≤ M) (h : ∀ p ∈ a.primeFactors, p ≤ K) :
    ∃ d e : ℕ, d * e = a ∧ 0 < d ∧ 0 < e ∧ K * d ≤ M ∧ K * e ≤ M := by
  by_cases hsmall : K * a ≤ M
  · exact ⟨1, a, by simp, by decide, ha, by simp; nlinarith, hsmall⟩
  have hlarge : K ≤ a := by
    by_contra! hlt
    have hk2 : K * a ≤ K ^ 2 := by simpa [sq] using Nat.mul_le_mul_left K hlt.le
    have hk3 : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right hK (by decide)
    omega
  have heq := Nat.prod_primeFactorsList ha.ne'
  obtain ⟨d, hd, hlo, hhi⟩ := crossing a.primeFactorsList hK
    (fun p hp ↦ h p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp)) (by rwa [heq])
  rw [heq] at hd
  obtain ⟨e, hde⟩ := hd
  have hdM : K * d ≤ M :=
    (Nat.mul_le_mul_left K hhi).trans (by nlinarith)
  have heM := (Nat.mul_le_mul_right e hlo).trans (hde ▸ ham)
  exact ⟨d, e, hde.symm, by omega, by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hde; omega,
    hdM, heM⟩

/-- In the cubic range each input needs at most two sites.
This is the large-height estimate of Chen, with the interval length allowed
to exceed the largest input. -/
theorem large_height {A : Finset ℕ} {x M : ℕ}
    (ha : ∀ a ∈ A, 0 < a ∧ a ≤ M) (hm : (2 * A.card) ^ 3 ≤ M) :
    ∃ B ⊆ window x M, Covers A B ∧ B.card ≤ 2 * A.card := by
  classical
  obtain hA | hA := A.eq_empty_or_nonempty
  · subst A
    exact ⟨∅, empty_subset _, by simp [Covers], by simp⟩
  let K := 2 * A.card
  let S := smoothPart A K
  have hS : S ⊆ A := filter_subset ..
  have hSc := card_le_card hS
  have hK : 1 ≤ K := by dsimp [K]; have := card_pos.mpr hA; omega
  have split (a : S) := split_smooth (ha a (hS a.property)).1
    (ha a (hS a.property)).2 hK hm (mem_filter.mp a.property).2
  choose d e hde hd he hdm hem using split
  obtain ⟨D, hD, hdc, hdvd⟩ := fill (univ : Finset S) d
    (empty_subset (window x M)) (K := K) (by simp; dsimp [K]; omega)
    (fun a _ ↦ ⟨hd a, hdm a⟩)
  simp only [card_empty, zero_add, card_univ, Fintype.card_coe, prod_empty, mul_one] at hdc hdvd
  obtain ⟨B, hB, hbc, hbdiv⟩ := fill (univ : Finset S) e hD
    (K := K) (by simp; dsimp [K]; omega) (fun a _ ↦ ⟨he a, hem a⟩)
  simp only [card_univ, Fintype.card_coe] at hbc
  have hbCover : Covers S B := by
    change (∏ a ∈ S, id a) ∣ ∏ b ∈ B, b
    rw [← prod_coe_sort S id]
    change (∏ a : S, (a : ℕ)) ∣ _
    rw [← prod_congr rfl (fun a _ ↦ hde a), prod_mul_distrib, mul_comm]
    exact (Nat.mul_dvd_mul_left _ hdvd).trans hbdiv
  have hbudget : B.card + 2 * (A.card - S.card) ≤ 2 * A.card := by omega
  obtain ⟨T, ht, hcov, htc⟩ := peel ha hB hbCover hbudget
  exact ⟨T, ht, hcov, htc.trans hbudget⟩

end ErdosSuranyi708
