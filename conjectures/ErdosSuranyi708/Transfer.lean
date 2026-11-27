module

public import conjectures.ErdosSuranyi708.Balance
public import conjectures.ErdosSuranyi708.SeedCount
public import conjectures.ErdosSuranyi708.TermComparison
public import conjectures.ErdosSuranyi708.TermTail
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708
open Finset Filter

private theorem sparse_transfer (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ M ≤ (2*n)^3, ∀ (x : ℕ) (A P : Finset ℕ) (w : ℕ → ℝ),
      A ⊆ window 0 M → A.card ≤ n → (∀ p ∈ P, p.Prime ∧ p ≤ 5*n ∧ p ≤ M) →
      (∀ p ∈ P, 0 ≤ w p) → primeMean P w ≤ 20 →
      (∑ a ∈ A, cappedScore P w a) - ∑ b ∈ window x M, max (cappedScore P w b - 1) 0 ≤
        2*A.card + ε*n := by
  classical
  let θ := ε/8
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let s := (2+θ)⁻¹
  have hs : 0 < s := inv_pos.mpr (by linarith)
  have hh : s < 1/2 := by
    simpa only [s,one_div] using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ)<2) (by linarith : 2<2+θ))
  have hs1 : s ≤ 1 := by linarith
  have hsval : 1/s = 2+θ := by simp [s]
  obtain ⟨H,hH,Y₁,hY₁⟩ := term_tail_uniform hs hh
  let δ := min (1/4) (θ/(2*H))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ' : δ ≤ 1/4 := min_le_left ..
  have hHδ : 2*H*δ ≤ θ := by
    have h := (le_div_iff₀ (by positivity : 0<2*H)).mp (min_le_right (1/4) (θ/(2*H)))
    linarith
  obtain ⟨Y₂,hY₂⟩ := transferSum_source hs hh hθ
  obtain ⟨Y₃,hY₃⟩ := SeedIndex.large_difference hs hh hδ
  let Y := max Y₁ (max Y₂ Y₃)
  have h1 : Y₁ ≤ Y := le_max_left ..
  have h2 : Y₂ ≤ Y := le_trans (le_max_left ..) (le_max_right ..)
  have h3 : Y₃ ≤ Y := le_trans (le_max_right ..) (le_max_right ..)
  obtain ⟨B,hB,hTail⟩ := hY₁ Y h1
  obtain ⟨K,hK⟩ := exists_nat_gt ((Y+1 : ℕ) / θ)
  have hKpos : 0 < K := Nat.cast_pos.mp (lt_of_le_of_lt (by positivity) hK)
  have hround : ((Y+1 : ℕ) : ℝ) * (K : ℝ)⁻¹ ≤ θ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (Nat.cast_pos.mpr hKpos)]
    linarith [(div_lt_iff₀ hθ).mp hK]
  let D : ℝ := max (max B (2^(Y+2))) 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right ..)
  have hdb : B ≤ D := le_trans (le_max_left ..) (le_max_left ..)
  have hdp : (2:ℝ)^(Y+2) ≤ D := le_trans (le_max_right ..) (le_max_left ..)
  filter_upwards [few_small_seeds Y K (θ/D) (div_pos hθ hD)] with n hcount
  intro M hM x A P w hA hn hp hw hμ
  let J := SeedIndex P (grid Y K M w)
  let small := (univ : Finset J).filter (fun i ↦ i.second ≤ Y)
  let F := transferSum Y K M s P w
  let f (i : J) := i.term Y M s w
  let mass (y : ℕ) (i : J) := ∑ b ∈ window y M, f i b
  let z := siteSum Y K M P w
  have hp' (p : ℕ) (h : p ∈ P) := (hp p h).1
  have sum_f {a : ℕ} (ha : 0 < a) : (∑ i : J, f i a) = F a := sum_terms w s hp' ha
  have hmass (y : ℕ) : (∑ i : J, mass y i) = ∑ b ∈ window y M, F b := by
    unfold mass
    rw [sum_comm]
    exact sum_congr rfl fun b h ↦ sum_f (by have := (mem_Ioc.mp h).1; omega)
  have hfn (i : J) (b : ℕ) (hb : b ∈ window 0 M) : 0 ≤ f i b := by
    apply mul_nonneg (i.coefficient_bounds Y M hs.le hs1 hw).1
    exact seedPolynomial_nonneg hs hh (fun r hr ↦ hp' r (i.req_sub hr))
      (fun r hr ↦ ⟨grid_positive (i.exponent_mem hr),i.exponent_mem hr⟩)
      (fun r hr ↦ hp' r (i.tail_sub hr)) i.tail_disjoint (mem_Ioc.mp hb).1
      (by simpa using (mem_Ioc.mp hb).2)
  have hmn (i : J) : 0 ≤ mass 0 i := sum_nonneg (hfn i)
  have hF (b : ℕ) (hb : b ∈ window 0 M) : 0 ≤ F b := by
    rw [← sum_f (mem_Ioc.mp hb).1]
    exact sum_nonneg fun i _ ↦ hfn i b hb
  have hsm : (small.card : ℝ) ≤ θ/D*n := hcount M hM P w hp hw
  have herr : D * small.card ≤ θ*n := calc
    _ ≤ D * (θ/D * n) := mul_le_mul_of_nonneg_left hsm hD.le
    _ = _ := by field_simp
  have hscomp := sum_comparison small (mass 0) (mass x) hmn hδ.le
    (c := D) (fun i hi ↦ ((le_abs_self _).trans
      (SeedIndex.small_difference hs.le hs1 hp' hw i (mem_filter.mp hi).2)).trans hdp)
    (fun i hi ↦ (le_abs_self _).trans (hY₃ (x := x) h3 hp' hw i
      (lt_of_not_ge fun h ↦ hi (mem_filter.mpr ⟨mem_univ _,h⟩))))
  rw [hmass,hmass] at hscomp
  have hcmp : (1-δ) * (∑ a ∈ window 0 M, F a) - θ*n ≤ ∑ b ∈ window x M, F b := by linarith
  have tail_i (i : J) : (∑ a ∈ window 0 M, if H < z a then f i a else 0) ≤
      (1/4)*mass 0 i + if i ∈ small then B else 0 := by
    simpa only [small,mem_filter,mem_univ,true_and] using hTail i hp' hw hμ
  have hallTail := sum_le_sum (s := univ) fun i _ ↦ tail_i i
  rw [sum_comm] at hallTail
  have haux (b : ℕ) (hb : b ∈ window 0 M) :
      (∑ i : J, if H < z b then f i b else 0) = if H < z b then F b else 0 := by
    by_cases h : H < z b
    · simpa only [h,ite_true] using sum_f (mem_Ioc.mp hb).1
    · simp [h]
  rw [sum_congr rfl haux] at hallTail
  have hend : (∑ i : J, if i ∈ small then B else 0) = small.card * B := by
    classical
    simp [Finset.sum_ite_mem]
  simp only [sum_add_distrib,← mul_sum,hend,hmass] at hallTail
  have hbErr : (small.card : ℝ)*B ≤ θ*n := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hdb (Nat.cast_nonneg _)).trans herr
  have hAz (a : ℕ) (_ : a ∈ A) : F a ≤ z a := by
    have ht := truncatedCrossing_le hs hs1 (activeLabels P a) (siteCost Y K M w a)
      (siteWeight Y K M w a) Y M (fun r h ↦ ⟨siteWeight_nonneg (hw r (mem_filter.mp h).1), min_le_left ..⟩)
    have hz : 0 ≤ z a := sum_nonneg fun p h ↦ siteWeight_nonneg (hw p (mem_filter.mp h).1)
    exact ht.trans (max_le (by change z a-1 ≤ z a; linarith) hz)
  have htail : ∑ a ∈ A, F a ≤ H*A.card + (1/4)*(∑ a ∈ window 0 M, F a) + θ*n := by
    linarith [sum_source_tail hA F z H hF hAz hH.le]
  have hsite (a : ℕ) (ha : a ∈ A) : cappedScore P w a ≤ F a + (2+θ) + (2*θ) := by
    obtain ⟨ha1,ha2⟩ := mem_Ioc.mp (hA ha)
    have h := hY₂ Y h2 hKpos hw hp' ha1 (by simpa using ha2)
    rw [hsval] at h
    linarith
  have hfinal := balance_transfer hA hn hH.le hδ.le hδ' (mul_nonneg hθ.le (Nat.cast_nonneg n)) hF hsite
    (fun b _ ↦ transferSum_upper hs hs1 hw b) hcmp htail
  have hcard' := Nat.cast_le (α := ℝ) |>.mpr hn
  have heq : ε = 8*θ := by dsimp [θ]; ring
  nlinarith [mul_le_mul_of_nonneg_right hHδ (Nat.cast_nonneg n),
    mul_le_mul_of_nonneg_left hcard' hθ.le]

/-- The interval-transfer inequality for all boxed prime weights. -/
theorem transfer : TransferBound := by
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (sparse_transfer ε hε)
  refine ⟨N, ?_⟩
  intro n hn M _ hM x A P w hA hAn hp hw
  apply (cap_transfer hA (fun p h ↦ (hp p h).1) w (fun p h ↦ (hw p h).1)).trans
  by_cases hd : 20 ≤ primeMean P w
  · exact (dense_transfer hA (fun p h ↦ ⟨(hp p h).1,(hp p h).2.2⟩) hw hd).trans
      (le_add_of_nonneg_right (mul_nonneg hε.le (Nat.cast_nonneg _)))
  · exact hN n hn M hM x A P w hA hAn hp (fun p h ↦ (hw p h).1) (le_of_not_ge hd)

end ErdosSuranyi708
