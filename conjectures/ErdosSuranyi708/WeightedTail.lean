module

public import conjectures.ErdosSuranyi708.Mean
public import conjectures.ErdosSuranyi708.Dense

@[expose] public section
namespace ErdosSuranyi708

open Finset Nat Real

private theorem multiple_mean {G : ℕ → ℝ} (h : MeanWeight G) (L : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ n ∈ Icc 1 L, if d ∣ n then G n else 0) ≤ meanSum G (L/d) := by
  rw [← sum_filter]
  calc
    _ = ∑ a ∈ Icc 1 (L/d), G (a*d) := by
      refine sum_bij' (fun n _ => n/d) (fun a _ => a*d) ?_ ?_ ?_ ?_ ?_
      · intro n hn; obtain ⟨hn, hv⟩ := mem_filter.mp hn
        have hpos := (mem_Icc.mp hn).1
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hpos hv) hd, Nat.div_le_div_right (mem_Icc.mp hn).2⟩
      · intro a ha; obtain ⟨ha,hq⟩ := mem_Icc.mp ha
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos ha hd,(Nat.le_div_iff_mul_le hd).mp hq⟩, Nat.dvd_mul_left ..⟩
      · intro n hn; exact Nat.div_mul_cancel (mem_filter.mp hn).2
      · intro a _; exact Nat.mul_div_cancel _ hd
      · intro n hn; rw [Nat.div_mul_cancel (mem_filter.mp hn).2]
    _ ≤ meanSum G (L/d) := sum_le_sum fun a ha => h.mul_le (mem_Icc.mp ha).1 hd

/-- The weight on multiples has the usual reciprocal bound below the square root of the cutoff. -/
theorem weighted_multiple {u : ℝ} (hu : 0 < u) : ∃ D : ℝ, 0 < D ∧ ∃ L₀ : ℕ,
    ∀ L ≥ L₀, ∀ (F : Finset ℕ) (G : ℕ → ℝ), MeanWeight G →
    (F.card : ℝ) ≤ (Real.log L)^2+2 → (∀ p ∈ primesLE L, p ∉ F → u ≤ G p) →
    ∀ d : ℕ, 0<d → d^2 ≤ L → (∑ n ∈ Icc 1 L, if d ∣ n then G n else 0) ≤
      (D / d)*meanSum G L := by
  obtain ⟨C,hC,hup⟩ := mean_upper
  obtain ⟨c,hc,L₀,hlow⟩ := mean_lower hu
  refine ⟨3*C/c, by positivity, max 4 L₀, ?_⟩
  intro L hL F G h hF hfree d hd hd2
  have hL4 : 4 ≤ L := (le_max_left ..).trans hL
  let q := L/d
  have hdq : d≤q := (Nat.le_div_iff_mul_le hd).mpr (by simpa [pow_two] using hd2)
  have hq : 2≤q := by
    by_cases he : d=1
    · simpa [q,he] using (show 2≤L by omega)
    · omega
  have hqL : q ≤ L := Nat.div_le_self ..
  have hqpos : 0 < Real.log q := log_pos (by exact_mod_cast (by omega : 1<q))
  have hLpos : 0 < Real.log L := log_pos (by exact_mod_cast (by omega : 1<L))
  have hLq : L ≤ q^3 := calc
    _ ≤ d*(q+1) := (Nat.lt_mul_div_succ L hd).le
    _ ≤ q*(q^2) := Nat.mul_le_mul hdq (by nlinarith only [Nat.mul_le_mul_left q hq,hq])
    _ = _ := by ring
  have hlog : Real.log L ≤ 3*Real.log q := by
    simpa using Real.log_le_log (by exact_mod_cast (by omega : 0<L)) (show (L:ℝ)≤(q:ℝ)^3 by exact_mod_cast hLq)
  have hqdiv : (q:ℝ) ≤ (L:ℝ)/d := (le_div_iff₀ (by exact_mod_cast hd)).mpr (by exact_mod_cast Nat.div_mul_le_self L d)
  have hh := hlow L ((le_max_right ..).trans hL) F G h hF hfree
  have hp : 0 ≤ meanProduct G L := zero_le_one.trans (meanProduct_one_le h _)
  calc
    _ ≤ meanSum G q := multiple_mean h L hd
    _ ≤ C*q*meanProduct G q / Real.log q := hup G h q hq
    _ ≤ C*((L:ℝ)/d)*meanProduct G L / Real.log q := by
      gcongr <;> first | exact meanProduct_mono h hqL | exact zero_le_one.trans (meanProduct_one_le h q)
    _ ≤ ((3*C/c)/d)*(c*L*meanProduct G L / Real.log L) := by
      have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
      field_simp
      nlinarith only [mul_le_mul_of_nonneg_left hlog hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

private def shortPowers (L p : ℕ) : Finset ℕ := (Icc 1 L).filter fun j => (p^j)^2 ≤ L

private theorem prime_power_series {p : ℕ} (hp : p.Prime) (L : ℕ) :
    (∑ j ∈ shortPowers L p, ((p^j : ℕ) : ℝ)⁻¹) ≤ 2/p := by
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ (p:ℝ)⁻¹ := by positivity
  have hr : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hn : 0 ∉ shortPowers L p := by simp [shortPowers]
  have hh := (summable_geometric_of_lt_one hr0 hr).sum_le_tsum (insert 0 (shortPowers L p))
    (fun n _ => pow_nonneg hr0 n)
  rw [sum_insert hn, pow_zero, tsum_geometric_of_lt_one hr0 hr] at hh
  have hgeo : (1-(p:ℝ)⁻¹)⁻¹ = 1+1/((p:ℝ)-1) := by field_simp; ring
  rw [hgeo] at hh
  simp only [Nat.cast_pow, ← inv_pow]
  apply (show (∑ j ∈ shortPowers L p, ((p:ℝ)⁻¹)^j) ≤ 1/((p:ℝ)-1) by linarith only [hh]).trans
  apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
  have hx : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  linarith

private theorem large_power_unique {n L : ℕ} (hn : n ∈ Icc 1 L) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : L < (p^n.factorization p)^2) (h2 : L < (q^n.factorization q)^2) : p=q := by
  by_contra hpq
  let U := p^n.factorization p
  let V := q^n.factorization q
  have hUV : U*V ∣ n := ((Nat.coprime_primes hp hq).mpr hpq |>.pow _ _).mul_dvd_of_dvd_of_dvd
    (Nat.ordProj_dvd n p) (Nat.ordProj_dvd n q)
  have hl := (Nat.le_of_dvd (mem_Icc.mp hn).1 hUV).trans (mem_Icc.mp hn).2
  change L < U^2 at h1; change L < V^2 at h2
  rcases le_total U V with h | h
  · nlinarith only [h1,hl,Nat.mul_le_mul_left U h]
  · nlinarith only [h2,hl,Nat.mul_le_mul_right V h]

private theorem split_score (P : Finset ℕ) (w : ℕ → ℝ) {L n : ℕ} (hn : n ∈ Icc 1 L)
    (hp : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, 0 ≤ w p) :
    cappedScore P w n ≤ 1+∑ p ∈ P, ∑ j ∈ shortPowers L p, if p^j ∣ n then w p else 0 := by
  classical
  let big := fun p => L < (p^n.factorization p)^2
  have honce : (∑ p ∈ P, if big p then (1:ℝ) else 0) ≤ 1 := by
    rw [sum_ite_zero P big (fun p hp' q hq' => large_power_unique hn (hp p hp') (hp q hq'))]
    split <;> norm_num
  apply le_trans _ (add_le_add honce (le_refl _))
  rw [cappedScore, ← sum_add_distrib]
  apply sum_le_sum; intro p hP
  have hpr := hp p hP
  have hnon (j : ℕ) : 0 ≤ if p^j ∣ n then w p else 0 := by split <;> simp [hw p hP]
  by_cases hb : big p
  · simpa [hb] using (min_le_left (1:ℝ) (w p*(n.factorization p:ℝ))).trans
      (le_add_of_nonneg_right (sum_nonneg (fun j _ => hnon j)))
  · simp only [hb, ↓reduceIte, zero_add]
    apply (min_le_right ..).trans
    have hdiv := Nat.le_of_dvd (mem_Icc.mp hn).1 (Nat.ordProj_dvd n p)
    have hv : n.factorization p ≤ L := (Nat.lt_pow_self hpr.one_lt).le.trans (hdiv.trans (mem_Icc.mp hn).2)
    have hsmall : (p^n.factorization p)^2 ≤ L := le_of_not_gt hb
    have hi : Icc 1 (n.factorization p) ⊆ shortPowers L p := by
      intro j hj; obtain ⟨hj1,hjv⟩ := mem_Icc.mp hj
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hj1,hjv.trans hv⟩,
        (Nat.pow_le_pow_left (Nat.pow_le_pow_right hpr.pos hjv) _).trans hsmall⟩
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg hi (fun j _ _ => hnon j))
    have hconst : ∀ j ∈ Icc 1 (n.factorization p), (if p^j ∣ n then w p else 0) = w p := by
      intro j hj
      simp [(hpr.pow_dvd_iff_le_factorization (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)).mpr (mem_Icc.mp hj).2]
    rw [sum_eq_card_nsmul hconst]; simp [mul_comm]

/-- The conditional expected capped score is bounded at every sufficiently large scale.
The bound holds uniformly over the prime weights, their support and the exceptional set. -/
theorem weighted_capped_score {u : ℝ} (hu : 0 < u) : ∃ C : ℝ, 0<C ∧ ∃ L₀ : ℕ,
    ∀ L ≥ L₀, ∀ (F P : Finset ℕ) (G w : ℕ → ℝ), MeanWeight G →
    (F.card : ℝ)≤ (Real.log L)^2+2 → (∀ p ∈ primesLE L, p ∉ F → u ≤ G p) →
    (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 0 ≤ w p) → primeMean P w ≤ 20 →
    (∑ n ∈ Icc 1 L, G n*cappedScore P w n) ≤ C*meanSum G L := by
  classical
  obtain ⟨D,hD,L₀,hdiv⟩ := weighted_multiple hu
  refine ⟨1+40*D, by positivity, L₀, ?_⟩
  intro L hL F P G w h hF hfree hP hw hM
  let S := meanSum G L
  have hS : 0 ≤ S := sum_nonneg fun n _ => h.nonneg n
  have hinner (p : ℕ) (hp : p∈P) (j : ℕ) (hj : j∈shortPowers L p) :
      (∑ n ∈ Icc 1 L, G n*(if p^j∣n then w p else 0)) ≤ ((D*S)*w p) * ((p^j : ℕ) : ℝ)⁻¹ := by
    have he : ∀ n : ℕ, G n*(if p^j∣n then w p else 0) = w p*(if p^j∣n then G n else 0) := by
      intro n; by_cases ht : p^j∣n <;> simp [ht,mul_comm]
    simp only [he, ← mul_sum]
    have hh := hdiv L hL F G h hF hfree (p^j) (pow_pos (hP p hp).pos _) (mem_filter.mp hj).2
    convert mul_le_mul_of_nonneg_left hh (hw p hp) using 1; ring
  have hout (p : ℕ) (hp : p∈P) :
      (∑ j ∈ shortPowers L p, ∑ n ∈ Icc 1 L, G n*(if p^j∣n then w p else 0)) ≤
      (2*D*S)*(w p/p) := by
    apply (sum_le_sum (hinner p hp)).trans
    rw [← mul_sum]
    have hb := mul_le_mul_of_nonneg_left (prime_power_series (hP p hp) L)
      (mul_nonneg (mul_nonneg hD.le hS) (hw p hp))
    convert hb using 1; ring
  calc
    _ ≤ ∑ n ∈ Icc 1 L, (G n + ∑ p ∈ P, ∑ j ∈ shortPowers L p, G n*(if p^j∣n then w p else 0)) := by
      apply sum_le_sum; intro n hn
      simpa [mul_add,mul_sum] using mul_le_mul_of_nonneg_left (split_score P w hn hP hw) (h.nonneg _)
    _ = S + ∑ p ∈ P, ∑ j ∈ shortPowers L p, ∑ n ∈ Icc 1 L, G n*(if p^j∣n then w p else 0) := by
      rw [sum_add_distrib]; congr 1
      rw [sum_comm]; exact sum_congr rfl fun _ _ => sum_comm
    _ ≤ S+(2*D*S)*primeMean P w := by
      apply add_le_add_right; simpa [primeMean,mul_sum] using sum_le_sum hout
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hM (show 0≤2*D*S by positivity)]

end ErdosSuranyi708
