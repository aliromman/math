module

public import conjectures.ErdosSuranyi708.Buckets
public import conjectures.ErdosSuranyi708.Sieve
public import conjectures.ErdosSuranyi708.Discrepancy

@[expose] public section
namespace ErdosSuranyi708
open Finset

/-- The exponent bucket of each required prime agrees with the specified lower endpoint. -/
def bucketMatch (C : ℕ → Finset ℕ) (A : Finset ℕ) (j : ℕ → ℕ) (b : ℕ) : Prop :=
  ∀ r ∈ A, r ∣ b ∧ lastCut (C r) (b.factorization r) = j r

/-- The product of the lower prime powers in a seed. -/
def bucketDivisor (A : Finset ℕ) (j : ℕ → ℕ) : ℕ := ∏ r ∈ A, r^(j r)

/-- An upper bucket endpoint excludes the indicated power on the quotient. -/
def forbiddenPowers (C : ℕ → Finset ℕ) (A : Finset ℕ) (j : ℕ → ℕ) : Finset ℕ :=
  (A.filter fun r => nextCut (C r) (j r) ≠ 0).image fun r => r^(nextCut (C r) (j r)-j r)

/-- The lower sieve contribution from one fixed choice of exponent buckets. -/
noncomputable def seedPolynomial (L : ℕ) (s : ℝ) (C : ℕ → Finset ℕ) (A : Finset ℕ)
    (j : ℕ → ℕ) (S : Finset ℕ) (b : ℕ) : ℝ := by
  classical
  exact if bucketMatch C A j b then lowerSieve L s (S.filter (· ∣ b)) else 0

/-- Extend squarefree sieve coefficients by zero to all natural moduli. -/
noncomputable def arithmeticCoeff (L : ℕ) (s : ℝ) (S : Finset ℕ) (e : ℕ) : ℝ :=
  if e.primeFactors ⊆ S ∧ (∏ p ∈ e.primeFactors, p)=e then sieveCoeff L s e.primeFactors else 0

/-- The original exponential on quotients that satisfy all upper bucket bounds. -/
noncomputable def seedMean (u : ℝ) (D S : Finset ℕ) (m : ℕ) : ℝ :=
  if ∀ v ∈ D, ¬v ∣ m then u^(S.filter (· ∣ m)).card else 0

lemma bucketDivisor_pos {A : Finset ℕ} (j : ℕ → ℕ) (hA : ∀ p ∈ A, p.Prime) :
    0 < bucketDivisor A j := prod_pos fun i hi => pow_pos (hA i hi).pos _

lemma forbiddenPowers_card (C : ℕ → Finset ℕ) (A : Finset ℕ) (j : ℕ → ℕ) :
    (forbiddenPowers C A j).card ≤ A.card := card_image_le.trans (card_filter_le ..)

private lemma cut_lt {C : Finset ℕ} {a : ℕ} (h : nextCut C a ≠ 0) : a < nextCut C a :=
  ((nextCut_spec (t := a)).mpr fun _ _ hg => hg).resolve_left h

lemma forbiddenPowers_two {C : ℕ → Finset ℕ} {A : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) {v : ℕ} (hv : v ∈ forbiddenPowers C A j) : 2 ≤ v := by
  obtain ⟨r,hr,rfl⟩ := mem_image.mp hv
  obtain ⟨hr,hn⟩ := mem_filter.mp hr
  have h := cut_lt hn
  exact Nat.succ_le_of_lt (Nat.one_lt_pow (by omega) (hA r hr).one_lt)

lemma forbiddenPowers_pairwise {C : ℕ → Finset ℕ} {A : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) : ((forbiddenPowers C A j : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
  intro v hv t ht hvt
  obtain ⟨r,hr,rfl⟩ := mem_image.mp hv
  obtain ⟨q,hq,rfl⟩ := mem_image.mp ht
  have hne : r ≠ q := by rintro rfl; exact hvt rfl
  exact (((Nat.coprime_primes (hA r (mem_filter.mp hr).1) (hA q (mem_filter.mp hq).1)).mpr hne).pow_left _).pow_right _

lemma bucketDivisor_factorization {A : Finset ℕ} (j : ℕ → ℕ) (hA : ∀ p ∈ A, p.Prime) (p : ℕ) :
    (bucketDivisor A j).factorization p = if p ∈ A then j p else 0 := by
  unfold bucketDivisor
  rw [Nat.factorization_prod_apply (fun r hr => pow_ne_zero _ (hA r hr).ne_zero)]
  calc
    _ = ∑ r ∈ A, if r=p then j r else 0 := by
      apply sum_congr rfl
      intro r hr
      rw [(hA r hr).factorization_pow]
      by_cases h : r=p <;> simp [h]
    _ = _ := by simp

lemma bucketDivisor_dvd_of_match {C : ℕ → Finset ℕ} {A : Finset ℕ} {j : ℕ → ℕ}
    {b : ℕ} (hA : ∀ p ∈ A, p.Prime) (hb : 0 < b) (hm : bucketMatch C A j b) :
    bucketDivisor A j ∣ b := by
  apply (Nat.factorization_le_iff_dvd (bucketDivisor_pos j hA).ne' hb.ne').mp
  intro p
  rw [bucketDivisor_factorization j hA]
  by_cases h : p ∈ A
  · simp only [h,ite_true]
    exact (hm p h).2 ▸ lastCut_le (C p) (b.factorization p)
  · simp [h]

lemma bucketMatch_mul {C : ℕ → Finset ℕ} {A : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hj : ∀ p ∈ A, 0 < j p ∧ j p ∈ C p) {m : ℕ} (hm : 0 < m) :
    bucketMatch C A j (bucketDivisor A j*m) ↔ ∀ v ∈ forbiddenPowers C A j, ¬v ∣ m := by
  have hd := bucketDivisor_pos j hA
  have factor (p) (hp : p ∈ A) :
      (bucketDivisor A j*m).factorization p = j p+m.factorization p := by
    rw [Nat.factorization_mul hd.ne' hm.ne', Finsupp.add_apply, bucketDivisor_factorization j hA]
    simp [hp]
  constructor
  · intro h v hv
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
    obtain ⟨hp,hn⟩ := mem_filter.mp hp
    have hh := ((lastCut_eq_iff (hj p hp).2).mp (h p hp).2).2.resolve_left hn
    rw [factor p hp] at hh
    rw [(hA p hp).pow_dvd_iff_le_factorization hm.ne']
    omega
  · intro h p hp
    have hpdiv : p ∣ bucketDivisor A j*m := by
      apply (hA p hp).dvd_iff_one_le_factorization (Nat.mul_ne_zero hd.ne' hm.ne') |>.mpr
      rw [factor p hp]
      have := (hj p hp).1
      omega
    refine ⟨hpdiv,(lastCut_eq_iff (hj p hp).2).mpr ?_⟩
    rw [factor p hp]
    refine ⟨by omega,?_⟩
    by_cases hn : nextCut (C p) (j p)=0
    · exact Or.inl hn
    · have hdv := h _ (mem_image.mpr ⟨p,mem_filter.mpr ⟨hp,hn⟩,rfl⟩)
      rw [(hA p hp).pow_dvd_iff_le_factorization hm.ne'] at hdv
      have ht := cut_lt hn
      exact Or.inr (by omega)

lemma arithmeticCoeff_bound (L : ℕ) {s : ℝ} (hs : 0 ≤ s) (S : Finset ℕ) (e : ℕ) :
    |arithmeticCoeff L s S e| ≤ s^e.primeFactors.card := by
  unfold arithmeticCoeff
  split
  · rcases sieveCoeff_values L s e.primeFactors with h | h <;> simp [h,abs_of_nonneg hs,pow_nonneg hs]
  · simp [pow_nonneg hs]

private lemma prime_prod_dvd {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (b : ℕ) :
    (∏ p ∈ E, p) ∣ b ↔ ∀ p ∈ E, p ∣ b := by
  refine ⟨fun h p hp => (dvd_prod_of_mem id hp).trans h, ?_⟩
  exact prod_dvd_of_isRelPrime (s := id) fun p hp q hq hne =>
    Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hE p hp) (hE q hq)).mpr hne)

lemma lowerSieve_divisors {L : ℕ} (hL : 1 ≤ L) (s : ℝ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ L) (b : ℕ) :
    lowerSieve L s (S.filter (· ∣ b)) =
      ∑ e ∈ Icc 1 L, if e ∣ b then arithmeticCoeff L s S e else 0 := by
  classical
  let T := (S.filter (· ∣ b)).powerset
  have sub {E : Finset ℕ} (h : E ∈ T) : E ⊆ S.filter (· ∣ b) := mem_powerset.mp h
  have primes {E : Finset ℕ} (h : E ∈ T) (p) (hp : p ∈ E) : p.Prime :=
    (hS p (mem_filter.mp (sub h hp)).1).1
  apply sum_bij_ne_zero (fun E _ _ => ∏ p ∈ E, p)
  · intro E h hn
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (primes h p hp).pos,
      sieveCoeff_supported hL (fun p hp => ⟨(primes h p hp).pos,
        (hS p (mem_filter.mp (sub h hp)).1).2⟩) hn⟩
  · intro E he _ F hf _ heq
    simpa [Nat.primeFactors_prod (primes he), Nat.primeFactors_prod (primes hf)] using
      congrArg Nat.primeFactors heq
  · intro e _ hn
    split at hn
    next hd =>
      unfold arithmeticCoeff at hn
      split at hn
      next hc =>
        refine ⟨e.primeFactors, mem_powerset.mpr ?_, hn,hc.2⟩
        intro p hp
        exact mem_filter.mpr ⟨hc.1 hp,(Nat.dvd_of_mem_primeFactors hp).trans hd⟩
      next => exact (hn rfl).elim
    next => exact (hn rfl).elim
  · intro E he _
    have hd := (prime_prod_dvd (primes he) b).mpr fun p hp => (mem_filter.mp (sub he hp)).2
    have hsub : E ⊆ S := (sub he).trans (filter_subset ..)
    simp [hd,arithmeticCoeff,Nat.primeFactors_prod (primes he),hsub]

private lemma base_coprime {A S : Finset ℕ} (j : ℕ → ℕ) (hA : ∀ p ∈ A, p.Prime)
    (hS : ∀ p ∈ S, p.Prime) (hAS : Disjoint A S) {p : ℕ} (hp : p ∈ S) :
    p.Coprime (bucketDivisor A j) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro r hr
  exact ((Nat.coprime_primes (hS p hp) (hA r hr)).mpr fun he =>
    disjoint_left.mp hAS hr (he ▸ hp)).pow_right _

private lemma valid_coefficient {L : ℕ} {s : ℝ} {S : Finset ℕ} {e : ℕ}
    (h : arithmeticCoeff L s S e ≠ 0) :
    e.primeFactors ⊆ S ∧ (∏ p ∈ e.primeFactors, p) = e := by
  by_contra hn
  simp [arithmeticCoeff, hn] at h

private lemma seed_condition {A S : Finset ℕ} {j : ℕ → ℕ} {C : ℕ → Finset ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hj : ∀ p ∈ A, 0 < j p ∧ j p ∈ C p)
    (hS : ∀ p ∈ S, p.Prime) (hAS : Disjoint A S) {b e : ℕ} (hb : 0 < b)
    (he : e.primeFactors ⊆ S ∧ (∏ p ∈ e.primeFactors, p) = e) :
    (bucketMatch C A j b ∧ e ∣ b) ↔
      (bucketDivisor A j*e ∣ b ∧ ∀ v ∈ forbiddenPowers C A j, ¬(bucketDivisor A j*e)*v ∣ b) := by
  let d := bucketDivisor A j
  have hd : 0 < d := bucketDivisor_pos j hA
  have hep : 0 < e := he.2 ▸ prod_pos fun p hp => (hS p (he.1 hp)).pos
  have hde : d.Coprime e := by
    conv_rhs => rw [← he.2]
    exact Nat.coprime_prod_right_iff.mpr fun p hp => (base_coprime j hA hS hAS (he.1 hp)).symm
  have hev {v} (hv : v ∈ forbiddenPowers C A j) : v.Coprime e := by
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hv
    have hrA := (mem_filter.mp hr).1
    conv_rhs => rw [← he.2]
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    exact ((Nat.coprime_primes (hA r hrA) (hS p (he.1 hp))).mpr fun eq =>
      disjoint_left.mp hAS hrA (eq ▸ he.1 hp)).pow_left _
  by_cases H : d*e ∣ b
  · obtain ⟨t,rfl⟩ := H
    have ht : 0 < t := Nat.pos_of_mul_pos_left hb
    have hcond : bucketMatch C A j (d*e*t) ↔ ∀ v ∈ forbiddenPowers C A j, ¬v ∣ t := by
      rw [Nat.mul_assoc,bucketMatch_mul hA hj (Nat.mul_pos hep ht)]
      apply forall₂_congr
      intro v hv
      exact not_congr ⟨(hev hv).dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h _⟩
    have hediv : e ∣ d*e*t := (dvd_mul_left e d).trans (dvd_mul_right _ _)
    change (_ ∧ e ∣ d*e*t) ↔ d*e ∣ d*e*t ∧ ∀ v ∈ _, ¬d*e*v ∣ d*e*t
    simp only [hediv, and_true, dvd_mul_right, true_and, Nat.mul_dvd_mul_iff_left (Nat.mul_pos hd hep)]
    exact hcond
  · have H' : ¬(bucketMatch C A j b ∧ e ∣ b) :=
      fun h => H (hde.mul_dvd_of_dvd_of_dvd (bucketDivisor_dvd_of_match hA hb h.1) h.2)
    exact iff_of_false H' fun h => H h.1

/-- The sum over the actual sites is the arithmetic sieve on the interval. -/
theorem seedPolynomial_sum (x M : ℕ) {s : ℝ} {C : ℕ → Finset ℕ} {A S : Finset ℕ} {j : ℕ → ℕ}
    (hL : 1 ≤ M / bucketDivisor A j) (hA : ∀ p ∈ A, p.Prime)
    (hj : ∀ p ∈ A, 0 < j p ∧ j p ∈ C p)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ M / bucketDivisor A j) (hAS : Disjoint A S) :
    ∑ b ∈ window x M, seedPolynomial (M / bucketDivisor A j) s C A j S b =
      siftSum x M (bucketDivisor A j) (forbiddenPowers C A j)
        (arithmeticCoeff (M / bucketDivisor A j) s S) := by
  classical
  unfold siftSum siftCount
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  have hbp : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hb).1
  unfold seedPolynomial
  rw [lowerSieve_divisors hL s hS]
  split
  next hm =>
    apply sum_congr rfl
    intro e _
    by_cases hc : arithmeticCoeff (M / bucketDivisor A j) s S e = 0
    · simp [hc]
    · have he := seed_condition hA hj (fun p hp => (hS p hp).1) hAS hbp (valid_coefficient hc)
      simp only [hm,true_and] at he
      by_cases h : e ∣ b
      · simp only [ite_eq_left h,ite_eq_left (he.mp h),mul_one]
      · simp only [ite_eq_right h,ite_eq_right (he.not.mp h),mul_zero]
  next hm =>
    symm
    apply sum_eq_zero
    intro e _
    by_cases hc : arithmeticCoeff (M / bucketDivisor A j) s S e = 0
    · simp [hc]
    · have he := seed_condition hA hj (fun p hp => (hS p hp).1) hAS hbp (valid_coefficient hc)
      simp [show ¬_ from fun h => hm (he.mpr h).1]

lemma seedPolynomial_mul {L : ℕ} (s : ℝ) {C : ℕ → Finset ℕ} {A S : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hj : ∀ p ∈ A, 0 < j p ∧ j p ∈ C p)
    (hS : ∀ p ∈ S, p.Prime) (hAS : Disjoint A S) {m : ℕ} (hm : 0 < m) :
    seedPolynomial L s C A j S (bucketDivisor A j*m) =
      if ∀ v ∈ forbiddenPowers C A j, ¬v ∣ m then lowerSieve L s (S.filter (· ∣ m)) else 0 := by
  classical
  unfold seedPolynomial
  rw [bucketMatch_mul hA hj hm]
  congr 2
  ext p
  simp only [mem_filter]
  exact and_congr_right fun hp => (base_coprime j hA hS hAS hp).dvd_mul_left

/-- On the initial interval the sieve lies between two fixed multiples of its mean weight. -/
theorem seedPolynomial_mul_bounds {L : ℕ} {s : ℝ} (hs : 0 < s) (hh : s < 1/2)
    {C : ℕ → Finset ℕ} {A S : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hj : ∀ p ∈ A, 0 < j p ∧ j p ∈ C p)
    (hS : ∀ p ∈ S, p.Prime) (hAS : Disjoint A S) {m : ℕ} (hm : 0 < m) (hml : m ≤ L) :
    (1-(s/(1-s))^2)*seedMean (1-s) (forbiddenPowers C A j) S m ≤
        seedPolynomial L s C A j S (bucketDivisor A j*m) ∧
      seedPolynomial L s C A j S (bucketDivisor A j*m) ≤
        seedMean (1-s) (forbiddenPowers C A j) S m := by
  rw [seedPolynomial_mul s hA hj hS hAS hm]
  unfold seedMean
  split
  · have hd := (prime_prod_dvd (E := S.filter (· ∣ m))
        (fun p hp => hS p (mem_filter.mp hp).1) m).mpr fun _ hp => (mem_filter.mp hp).2
    exact ⟨lowerSieve_lower L hs hh _ (fun p hp => (hS p (mem_filter.mp hp).1).pos)
      ((Nat.le_of_dvd hm hd).trans hml), lowerSieve_le L (by linarith) _⟩
  · simp

theorem bucket_initial_sum {A : Finset ℕ} {j : ℕ → ℕ} (hA : ∀ p ∈ A, p.Prime)
    (M : ℕ) (f : ℕ → ℝ) (hf : ∀ b ∈ window 0 M, ¬bucketDivisor A j ∣ b → f b=0) :
    ∑ b ∈ window 0 M, f b = ∑ m ∈ Icc 1 (M / bucketDivisor A j), f (bucketDivisor A j*m) := by
  let d := bucketDivisor A j
  have hd : 0 < d := bucketDivisor_pos j hA
  symm
  apply sum_bij_ne_zero (fun m _ _ => d*m)
  · intro m hm _
    obtain ⟨hm1,hm2⟩ := mem_Icc.mp hm
    apply mem_Ioc.mpr
    rw [Nat.zero_add]
    exact ⟨Nat.mul_pos hd hm1,by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hm2⟩
  · intro _ _ _ _ _ _ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro b hb hn
    have hdv : d ∣ b := by_contra fun h => hn (hf b hb h)
    obtain ⟨m,rfl⟩ := hdv
    have hmm := mem_Ioc.mp hb
    have hm1 : 0 < m := Nat.pos_of_mul_pos_left hmm.1
    have hm2 := (Nat.le_div_iff_mul_le hd).mpr (by simpa [d,Nat.mul_comm] using hmm.2)
    exact ⟨m,mem_Icc.mpr ⟨hm1,hm2⟩,hn,rfl⟩
  · intros; rfl

theorem seedPolynomial_initial (M : ℕ) {s : ℝ} {C : ℕ → Finset ℕ} {A S : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) :
    ∑ b ∈ window 0 M, seedPolynomial (M / bucketDivisor A j) s C A j S b =
      ∑ m ∈ Icc 1 (M / bucketDivisor A j),
        seedPolynomial (M / bucketDivisor A j) s C A j S (bucketDivisor A j*m) := by
  apply bucket_initial_sum hA
  intro b hb hn
  have hm : ¬bucketMatch C A j b := fun h =>
    hn (bucketDivisor_dvd_of_match hA (mem_Ioc.mp hb).1 h)
  simp [seedPolynomial,hm]

theorem seedPolynomial_mass_lo (M : ℕ) {s : ℝ} (hs : 0 < s) (hh : s < 1/2)
    {C : ℕ → Finset ℕ} {A S : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hj : ∀ p ∈ A, 0 < j p ∧ j p ∈ C p)
    (hS : ∀ p ∈ S, p.Prime) (hAS : Disjoint A S) :
    (1-(s/(1-s))^2)*meanSum (seedMean (1-s) (forbiddenPowers C A j) S) (M / bucketDivisor A j) ≤
      ∑ b ∈ window 0 M, seedPolynomial (M / bucketDivisor A j) s C A j S b := by
  rw [seedPolynomial_initial M hA, meanSum, mul_sum]
  exact sum_le_sum fun _ hm => (seedPolynomial_mul_bounds hs hh hA hj hS hAS
    (mem_Icc.mp hm).1 (mem_Icc.mp hm).2).1

theorem seedPolynomial_mass_hi (M : ℕ) {s : ℝ} (hs : 0 < s) (hh : s < 1/2)
    {C : ℕ → Finset ℕ} {A S : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hj : ∀ p ∈ A, 0 < j p ∧ j p ∈ C p)
    (hS : ∀ p ∈ S, p.Prime) (hAS : Disjoint A S) :
    ∑ b ∈ window 0 M, seedPolynomial (M / bucketDivisor A j) s C A j S b ≤
      meanSum (seedMean (1-s) (forbiddenPowers C A j) S) (M / bucketDivisor A j) := by
  rw [seedPolynomial_initial M hA]
  exact sum_le_sum fun _ hm => (seedPolynomial_mul_bounds hs hh hA hj hS hAS
    (mem_Icc.mp hm).1 (mem_Icc.mp hm).2).2

lemma forbiddenPowers_primePow {C : ℕ → Finset ℕ} {A : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) {v : ℕ} (hv : v ∈ forbiddenPowers C A j) : IsPrimePow v := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
  obtain ⟨hp,hn⟩ := mem_filter.mp hp
  exact (isPrimePow_nat_iff _).mpr ⟨p,_,hA p hp,Nat.sub_pos_of_lt (cut_lt hn),rfl⟩

theorem seedMean_isMeanWeight {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    {D S : Finset ℕ} (hD : ∀ v ∈ D, IsPrimePow v) (hS : ∀ p ∈ S, p.Prime) :
    MeanWeight (seedMean u D S) where
  one := by
    have ha : ∀ v ∈ D, ¬v ∣ 1 := fun v hv h => (hD v hv).ne_one (Nat.dvd_one.mp h)
    have he : S.filter (· ∣ 1) = ∅ := by
      apply filter_eq_empty_iff.mpr
      exact fun p hp hd => (hS p hp).ne_one (Nat.dvd_one.mp hd)
    simp only [seedMean,ite_eq_left ha,he,card_empty,pow_zero]
  nonneg _ := by unfold seedMean; split <;> positivity
  mul_le {a b} _ _ := by
    unfold seedMean
    by_cases ha : ∀ v ∈ D, ¬v ∣ a
    · rw [ite_eq_left ha]
      split
      · apply pow_le_pow_of_le_one hu hu1
        exact card_le_card fun p hp => mem_filter.mpr
          ⟨(mem_filter.mp hp).1,dvd_mul_of_dvd_left (mem_filter.mp hp).2 _⟩
      · exact pow_nonneg hu _
    · have hab : ¬∀ v ∈ D, ¬v ∣ a*b :=
        fun h => ha fun v hv hd => h v hv (dvd_mul_of_dvd_left hd _)
      simp [ha,hab]
  coprime {a b} hab := by
    have hcond : (∀ v ∈ D, ¬v ∣ a*b) ↔ (∀ v ∈ D, ¬v ∣ a) ∧ (∀ v ∈ D, ¬v ∣ b) := by
      constructor
      · intro h
        exact ⟨fun v hv h₁ => h v hv ((hab.isPrimePow_dvd_mul (hD v hv)).mpr (Or.inl h₁)),
          fun v hv h₂ => h v hv ((hab.isPrimePow_dvd_mul (hD v hv)).mpr (Or.inr h₂))⟩
      · intro h v hv ht
        exact ((hab.isPrimePow_dvd_mul (hD v hv)).mp ht).elim (h.1 v hv) (h.2 v hv)
    have hfilter : S.filter (· ∣ a*b) = S.filter (· ∣ a) ∪ S.filter (· ∣ b) := by
      ext p
      simp only [mem_filter,mem_union]
      by_cases hp : p ∈ S
      · simp [hp,(hS p hp).dvd_mul]
      · simp [hp]
    have hd : Disjoint (S.filter (· ∣ a)) (S.filter (· ∣ b)) := by
      apply disjoint_left.mpr
      intro p hp hq
      exact (hS p (mem_filter.mp hp).1).not_dvd_one
        (hab ▸ Nat.dvd_gcd (mem_filter.mp hp).2 (mem_filter.mp hq).2)
    unfold seedMean
    by_cases ha : ∀ v ∈ D, ¬v ∣ a
    · by_cases hb : ∀ v ∈ D, ¬v ∣ b
      · simp only [ite_eq_left (hcond.mpr ⟨ha,hb⟩),ite_eq_left ha,ite_eq_left hb,
           hfilter,card_union_of_disjoint hd,pow_add]
      · simp only [ite_eq_right (fun h => hb (hcond.mp h).2),ite_eq_right hb,mul_zero]
    · simp only [ite_eq_right (fun h => ha (hcond.mp h).1),ite_eq_right ha,zero_mul]

theorem seedMean_prime_lower {u : ℝ} (hu : u ≤ 1) {C : ℕ → Finset ℕ} {A S : Finset ℕ}
    {j : ℕ → ℕ} (hA : ∀ p ∈ A, p.Prime) (hS : ∀ p ∈ S, p.Prime)
    {p : ℕ} (hp : p.Prime) (hpa : p ∉ A) : u ≤ seedMean u (forbiddenPowers C A j) S p := by
  have ha : ∀ v ∈ forbiddenPowers C A j, ¬v ∣ p := by
    intro v hv hd
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hv
    obtain ⟨hr,hn⟩ := mem_filter.mp hr
    have ht := cut_lt hn
    have hdv : r ∣ r^(nextCut (C r) (j r)-j r) := dvd_pow_self _ (by omega)
    exact hpa ((Nat.prime_dvd_prime_iff_eq (hA r hr) hp).mp (hdv.trans hd) ▸ hr)
  rw [seedMean,ite_eq_left ha]
  by_cases h : p ∈ S
  · have hf : S.filter (· ∣ p) = {p} := by
      ext r
      simp only [mem_filter,mem_singleton]
      exact ⟨fun hr => (Nat.prime_dvd_prime_iff_eq (hS r hr.1) hp).mp hr.2,
        by rintro rfl; exact ⟨h,dvd_refl _⟩⟩
    simp [hf]
  · have hf : S.filter (· ∣ p) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro r hr hd
      exact h ((Nat.prime_dvd_prime_iff_eq (hS r hr) hp).mp hd ▸ hr)
    simpa [hf] using hu

theorem seedPolynomial_nonneg {M b : ℕ} {s : ℝ} (hs : 0 < s) (hh : s < 1/2)
    {C : ℕ → Finset ℕ} {A S : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hj : ∀ p ∈ A, 0 < j p ∧ j p ∈ C p)
    (hS : ∀ p ∈ S, p.Prime) (hAS : Disjoint A S) (hb : 0 < b) (hbM : b ≤ M) :
    0 ≤ seedPolynomial (M / bucketDivisor A j) s C A j S b := by
  classical
  by_cases hm : bucketMatch C A j b
  · obtain ⟨m,rfl⟩ := bucketDivisor_dvd_of_match hA hb hm
    have hd := bucketDivisor_pos j hA
    have hm1 := Nat.pos_of_mul_pos_left hb
    have hm2 := (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hbM)
    have h₁ : 0 ≤ s/(1-s) := div_nonneg hs.le (by linarith)
    have h₂ : s/(1-s) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hmean := seedMean_isMeanWeight (u := 1-s) (by linarith) (by linarith)
      (D := forbiddenPowers C A j) (fun _ hv => forbiddenPowers_primePow hA hv) hS
    exact (mul_nonneg (by nlinarith [mul_nonneg h₁ (sub_nonneg.mpr h₂)]) (hmean.nonneg m)).trans
      (seedPolynomial_mul_bounds hs hh hA hj hS hAS hm1 hm2).1
  · simp [seedPolynomial,hm]

theorem seedPolynomial_mass_le_level (M : ℕ) {s : ℝ} (hs : 0 < s) (hh : s < 1/2)
    {C : ℕ → Finset ℕ} {A S : Finset ℕ} {j : ℕ → ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hj : ∀ p ∈ A, 0 < j p ∧ j p ∈ C p)
    (hS : ∀ p ∈ S, p.Prime) (hAS : Disjoint A S) :
    ∑ b ∈ window 0 M, seedPolynomial (M / bucketDivisor A j) s C A j S b ≤
      ((M / bucketDivisor A j : ℕ) : ℝ) := by
  apply (seedPolynomial_mass_hi M hs hh hA hj hS hAS).trans
  have hmean := seedMean_isMeanWeight (u := 1-s) (by linarith) (by linarith)
    (D := forbiddenPowers C A j) (fun _ hv => forbiddenPowers_primePow hA hv) hS
  unfold meanSum
  calc
    _ ≤ ∑ _ ∈ Icc 1 (M / bucketDivisor A j), (1:ℝ) :=
      sum_le_sum fun _ hm => hmean.le_one (mem_Icc.mp hm).1
    _ = _ := by simp

end ErdosSuranyi708
