module

public import conjectures.ErdosSuranyi708.SeedTail
public import conjectures.ErdosSuranyi708.Terms

@[expose] public section
namespace ErdosSuranyi708

open Finset Nat Real Filter

/-- One fixed score threshold controls every large-prime term. Terms with a fixed
small second prime have a bounded additional contribution, uniformly in the window length. -/
theorem term_tail_uniform {s : ℝ} (hs : 0<s) (hh : s<1/2) :
    ∃ H : ℝ, 0<H ∧ ∃ Y₀ : ℕ, ∀ Y≥Y₀, ∃ B : ℝ, 0≤B ∧
    ∀ {K M : ℕ} {P : Finset ℕ} {w : ℕ → ℝ} (i : SeedIndex P (grid Y K M w)),
    (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 0≤w p) → primeMean P w≤20 →
    (∑ a ∈ window 0 M, if H<siteSum Y K M P w a then i.term Y M s w a else 0) ≤
      (1/4)*(∑ a ∈ window 0 M, i.term Y M s w a) + if i.second≤Y then B else 0 := by
  classical
  obtain ⟨K₁,hK,L₀,htail⟩ := seed_high_score hs hh
  let H := 4*K₁
  have hH : 0<H := by dsimp [H]; positivity
  refine ⟨H,hH,L₀,?_⟩
  intro Y hY
  have hev : ∀ᶠ n : ℕ in atTop, (Y:ℝ)+1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  let B := max N L₀
  refine ⟨B,cast_nonneg _,?_⟩
  intro K M P w i hp hw hM
  let L := i.level M
  let α := i.coefficient Y M s w
  let f := seedPolynomial L s (grid Y K M w) i.required i.exponent i.tail
  have hα := i.coefficient_bounds Y M hs.le (by linarith) hw
  have hA r (hr : r ∈ i.required) := hp r (i.req_sub hr)
  have hS r (hr : r ∈ i.tail) := hp r (i.tail_sub hr)
  have hj r (hr : r ∈ i.required) : 0 < i.exponent r ∧ i.exponent r ∈ grid Y K M w r :=
    ⟨grid_positive (i.exponent_mem hr),i.exponent_mem hr⟩
  have hf b (hb : b ∈ window 0 M) : 0≤f b :=
    seedPolynomial_nonneg hs hh hA hj hS i.tail_disjoint (mem_Ioc.mp hb).1 (by simpa using (mem_Ioc.mp hb).2)
  have hfM : 0 ≤ ∑ a ∈ window 0 M, f a := sum_nonneg hf
  let V := ∑ a ∈ window 0 M, f a
  let U := ∑ a ∈ window 0 M, if H<siteSum Y K M P w a then f a else 0
  have he : (∑ a ∈ window 0 M, if H<siteSum Y K M P w a then i.term Y M s w a else 0) = α*U := by
    rw [show α*U = ∑ a ∈ window 0 M, α*(if H<siteSum Y K M P w a then f a else 0) by rw [← mul_sum]]
    apply sum_congr rfl; intro a _; split <;> simp [SeedIndex.term,α,f,L]
  have he' : (∑ a ∈ window 0 M, i.term Y M s w a) = α*V := by change (∑ _a ∈ _, α*f _a) = _; rw [← mul_sum]
  rw [he,he']
  by_cases hzero : α=0
  · simp [hzero]; split <;> positivity
  have hret := i.retained_of_nonzero hzero
  have hred : i.red.card ≤ i.second := by
    have hsub : i.red ⊆ range i.second := fun r hr => mem_range.mpr (mem_filter.mp (i.red_sub hr)).2
    simpa using card_le_card hsub
  by_cases hgood : L₀≤L ∧ (i.red.card:ℝ)≤(Real.log L)^2
  · have hcard : (i.required.card:ℝ)≤(Real.log L)^2+2 := by rw [i.required_card]; push_cast; linarith [hgood.2]
    have hbase b (_hb : b ∈ window 0 M) (hmatch : bucketMatch (grid Y K M w) i.required i.exponent b) :
        (∑ r ∈ i.required, siteWeight Y K M w b r) ≤ 3 := by
      apply le_trans _ (i.required_weight_le hw hzero)
      apply sum_le_sum; intro r hr
      simp only [siteWeight,siteExponent,SeedIndex.weights,(hmatch r hr).2,le_refl]
    have ht : U ≤ (K₁/H)*V := htail hH hgood.1 i.req_sub hp hw hS hj i.tail_disjoint hcard hM hbase
    have hratio : K₁/H=1/4 := by dsimp [H]; field_simp
    rw [hratio] at ht
    have hfin : α*U ≤ (1/4)*(α*V) := by simpa [mul_left_comm] using mul_le_mul_of_nonneg_left ht hα.1
    apply hfin.trans; apply le_add_of_nonneg_right; split <;> positivity
  · have hsmall : i.second≤Y := by
      by_contra hn
      have hlevel := i.second_le_level hp hret
      exact hgood ⟨le_trans hY ((le_of_lt (lt_of_not_ge hn)).trans hlevel), hret.2.resolve_left hn⟩
    have hLB : L≤B := by
      by_contra hn
      have hBL := lt_of_not_ge hn
      have hL₀ : L₀≤L := (le_max_right ..).trans hBL.le
      have hl := hN L ((le_max_left ..).trans hBL.le)
      have hY0 : (0:ℝ)≤Y := cast_nonneg _
      have hred' : (i.red.card:ℝ)≤Y := by exact_mod_cast hred.trans hsmall
      have hll : 0≤Real.log L - 1 := by linarith only [hl,hY0]
      have hquad := mul_nonneg hll (log_natCast_nonneg L)
      exact hgood ⟨hL₀, by nlinarith only [hl,hred',hquad]⟩
    have hUV : U≤V := by
      apply sum_le_sum; intro a ha; split <;> first | exact le_rfl | exact hf a ha
    have hVL : V ≤ (L:ℝ) := seedPolynomial_mass_le_level M hs hh hA hj hS i.tail_disjoint
    have hV0 : 0≤V := hfM
    have hz : 0≤α*V := mul_nonneg hα.1 hV0
    have hub : α*U ≤ B := (mul_le_mul_of_nonneg_left hUV hα.1).trans
      ((mul_le_of_le_one_left hV0 hα.2).trans (hVL.trans (by exact_mod_cast hLB)))
    simp only [hsmall,↓reduceIte]; linarith only [hub,hz]

end ErdosSuranyi708
