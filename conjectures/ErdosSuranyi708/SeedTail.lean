module

public import conjectures.ErdosSuranyi708.WeightedTail
public import conjectures.ErdosSuranyi708.SeedArithmetic
public import conjectures.ErdosSuranyi708.Site

@[expose] public section
namespace ErdosSuranyi708

open Finset Nat Real

/-- A prime outside the seed has the same valuation on the original integer and on its quotient. -/
theorem seed_siteScore_le {Y K M m : ℕ} {A P : Finset ℕ} {j : ℕ → ℕ} {w : ℕ → ℝ}
    (hm : 0 < m) (hAP : A ⊆ P) (hp : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, 0 ≤ w p) :
    siteSum Y K M P w (bucketDivisor A j*m) ≤
      (∑ p ∈ A, siteWeight Y K M w (bucketDivisor A j*m) p) + cappedScore P w m := by
  have hA p (ha : p ∈ A) := hp p (hAP ha)
  calc
    _ ≤ ∑ p ∈ P, siteWeight Y K M w (bucketDivisor A j*m) p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun p hh _ => siteWeight_nonneg (hw p hh))
    _ = (∑ p ∈ A, siteWeight Y K M w (bucketDivisor A j*m) p) +
        ∑ p ∈ P\A, siteWeight Y K M w (bucketDivisor A j*m) p := by rw [add_comm,sum_sdiff hAP]
    _ ≤ _ := by
      apply add_le_add_right
      rw [cappedScore]
      apply le_trans _ (sum_le_sum_of_subset_of_nonneg (s:=P\A) (t:=P) (sdiff_subset ..) (fun p hh _ =>
        le_min zero_le_one (mul_nonneg (hw p hh) (cast_nonneg _))))
      apply sum_le_sum; intro p hh
      obtain ⟨hP,hnot⟩ := mem_sdiff.mp hh
      have he : (bucketDivisor A j*m).factorization p = m.factorization p := by
        rw [Nat.factorization_mul (bucketDivisor_pos _ hA).ne' hm.ne', Finsupp.add_apply, bucketDivisor_factorization _ hA]
        simp [hnot]
      simpa [he] using siteWeight_le (Y:=Y) (K:=K) (M:=M) (a:=bucketDivisor A j*m) (hw p hP)

private theorem seed_tail_moment {Y K M : ℕ} {A P S : Finset ℕ} {j : ℕ → ℕ} {w : ℕ → ℝ}
    {C : ℕ → Finset ℕ} {s T : ℝ} (hs : 0<s) (hh : s<1/2) (hAP : A ⊆ P)
    (hp : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, 0 ≤ w p) (hS : ∀ p ∈ S, p.Prime)
    (hj : ∀ p ∈ A, 0<j p ∧ j p ∈ C p) (hAS : Disjoint A S)
    (hbase : ∀ b ∈ window 0 M, bucketMatch C A j b → (∑ p ∈ A, siteWeight Y K M w b p) ≤ 3)
    (hG : MeanWeight (seedMean (1-s) (forbiddenPowers C A j) S))
    (limit : ℝ) (hscore : (∑ m ∈ Icc 1 (M / bucketDivisor A j),
      seedMean (1-s) (forbiddenPowers C A j) S m * cappedScore P w m) ≤
        limit * meanSum (seedMean (1-s) (forbiddenPowers C A j) S) (M / bucketDivisor A j)) :
    T*(∑ b ∈ window 0 M, if T<siteSum Y K M P w b then
      seedPolynomial (M / bucketDivisor A j) s C A j S b else 0) ≤
        (3+limit)*meanSum (seedMean (1-s) (forbiddenPowers C A j) S) (M / bucketDivisor A j) := by
  classical
  let d := bucketDivisor A j
  let L := M/d
  let G := seedMean (1-s) (forbiddenPowers C A j) S
  let f := seedPolynomial L s C A j S
  have hA p (ha : p ∈ A) := hp p (hAP ha)
  have hd : 0 < d := bucketDivisor_pos _ hA
  have hu : 0<1-s := by linarith
  have hr : s/(1-s)<1 := (div_lt_one hu).mpr (by linarith)
  have hc : 0 < 1-(s/(1-s))^2 := by nlinarith [mul_pos (sub_pos.mpr hr) (show 0<1+s/(1-s) by positivity)]
  change T*(∑ b ∈ window 0 M, if T<siteSum Y K M P w b then f b else 0) ≤ (3+limit)*meanSum G L
  rw [bucket_initial_sum hA M _ (by
    intro b hb hn
    have hn' : ¬bucketMatch C A j b := fun ht => hn (bucketDivisor_dvd_of_match hA (mem_Ioc.mp hb).1 ht)
    simp [f,seedPolynomial,hn']), mul_sum]
  calc
    _ ≤ ∑ m ∈ Icc 1 L, G m * (3+cappedScore P w m) := by
      apply sum_le_sum; intro m hm
      obtain ⟨hm0,hmL⟩ := mem_Icc.mp hm
      have hnn : 0 ≤ cappedScore P w m := sum_nonneg fun p hh => le_min zero_le_one (mul_nonneg (hw p hh) (cast_nonneg _))
      have hg : 0≤G m := hG.nonneg _
      by_cases hmch : bucketMatch C A j (d*m)
      · have hbm : d*m ∈ window 0 M := mem_Ioc.mpr ⟨Nat.mul_pos hd hm0,
          by simpa [d,Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmL⟩
        have hz := (seed_siteScore_le (Y:=Y) (K:=K) (M:=M) (j:=j) hm0 hAP hp hw).trans
          (add_le_add (hbase _ hbm hmch) (le_refl _))
        obtain ⟨hlo,hhi⟩ := seedPolynomial_mul_bounds (L:=L) hs hh hA hj hS hAS hm0 hmL
        change (1-(s/(1-s))^2)*G m ≤ f (d*m) at hlo
        change f (d*m) ≤ G m at hhi
        split
        next ht =>
          have hb := mul_le_mul (ht.le.trans hz) hhi ((mul_nonneg hc.le hg).trans hlo) (by linarith : 0 ≤ 3+cappedScore P w m)
          simpa [mul_comm] using hb
        next => simp; positivity
      · simp [f,seedPolynomial,show ¬bucketMatch C A j (bucketDivisor A j*m) from hmch]; positivity
    _ ≤ _ := by
      change (∑ m ∈ Icc 1 L, G m*cappedScore P w m) ≤ limit*meanSum G L at hscore
      simp only [mul_add,sum_add_distrib,← sum_mul]
      unfold meanSum at hscore ⊢
      linarith only [hscore]

/-- The proportion of a seed's initial mass above score `T` is at most a constant divided by `T`. -/
theorem seed_high_score {s : ℝ} (hs : 0<s) (hh : s<1/2) : ∃ K₁ : ℝ, 0<K₁ ∧ ∃ L₀ : ℕ,
    ∀ {Y K M : ℕ} {A P S : Finset ℕ} {j : ℕ → ℕ} {w : ℕ → ℝ} {C : ℕ → Finset ℕ} {T : ℝ},
    0<T → L₀ ≤ M / bucketDivisor A j → A ⊆ P → (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 0 ≤ w p) →
    (∀ p ∈ S, p.Prime) → (∀ p ∈ A, 0<j p ∧ j p ∈ C p) → Disjoint A S →
    (A.card : ℝ) ≤ (Real.log (M / bucketDivisor A j : ℕ))^2 + 2 → primeMean P w ≤ 20 →
    (∀ b ∈ window 0 M, bucketMatch C A j b → (∑ p ∈ A, siteWeight Y K M w b p) ≤ 3) →
    (∑ b ∈ window 0 M, if T<siteSum Y K M P w b then
      seedPolynomial (M / bucketDivisor A j) s C A j S b else 0) ≤
    (K₁ / T)*(∑ b ∈ window 0 M, seedPolynomial (M / bucketDivisor A j) s C A j S b) := by
  have hu : 0<1-s := by linarith
  have hu1 : 1-s ≤1 := by linarith
  let c := 1-(s/(1-s))^2
  have hr : s/(1-s)<1 := (div_lt_one hu).mpr (by linarith)
  have hc : 0<c := by dsimp [c]; nlinarith [mul_pos (sub_pos.mpr hr) (show 0<1+s/(1-s) by positivity)]
  obtain ⟨D,hD,L₀,hbound⟩ := weighted_capped_score hu
  refine ⟨(3+D)/c,by positivity,L₀,?_⟩
  intro Y K M A P S j w C T hT hL hAP hp hw hS hj hAS hcard hmean hbase
  have hA p (ha : p ∈ A) := hp p (hAP ha)
  let G := seedMean (1-s) (forbiddenPowers C A j) S
  let L := M / bucketDivisor A j
  have hG : MeanWeight G := seedMean_isMeanWeight hu.le hu1 (fun _ hv => forbiddenPowers_primePow hA hv) hS
  have hfree (p) (hp' : p ∈ primesLE L) (hpa : p ∉ A) : 1-s ≤ G p :=
    seedMean_prime_lower hu1 hA hS (mem_primesLE.mp hp').2 hpa
  have hscore := hbound L hL A P G w hG hcard hfree hp hw hmean
  have htail := seed_tail_moment (T:=T) hs hh hAP hp hw hS hj hAS hbase hG D hscore
  have hmass := seedPolynomial_mass_lo M hs hh hA hj hS hAS
  have hmain := mul_le_mul_of_nonneg_left hmass (show 0 ≤ (3+D)/c by positivity)
  have hid : (3+D)/c*(c*meanSum G L) = (3+D)*meanSum G L := by field_simp
  change (3+D)/c*(c*meanSum G L) ≤ _ at hmain
  rw [hid] at hmain
  have hh' := htail.trans hmain
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hT).mpr
  simpa [mul_comm] using hh'

end ErdosSuranyi708
