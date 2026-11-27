module

public import conjectures.ErdosSuranyi708.Scores
public import conjectures.ErdosSuranyi708.Selection
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708
open Finset Filter

/-- The number of available prime labels is negligible compared with the input size. -/
theorem few_labels (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (((5 * n).primesLE.card : ℕ) : ℝ) ≤ ε * n := by
  have htop : Tendsto (fun n : ℕ ↦ ((5 * n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop.mpr fun b ↦ by
      filter_upwards [eventually_ge_atTop b] with n hn
      omega)
  have hlog := (Real.tendsto_log_atTop.comp htop).eventually_ge_atTop
      (5 * (Real.log 4 + 1) / ε)
  filter_upwards [htop.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1)),
      hlog, eventually_ge_atTop 1] with n hn hl hn1
  simp only [Function.comp_apply, Nat.floor_natCast] at hn hl
  rw [Nat.primesLE_card_eq_primeCounting]
  refine hn.trans ((div_le_iff₀ (Real.log_pos (by exact_mod_cast (show 1 < 5*n by omega)))).mpr ?_)
  have := (div_le_iff₀ hε).mp hl
  push_cast at this ⊢
  nlinarith [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg n)]

private theorem select_smooth {A P : Finset ℕ} {x M : ℕ} {C : ℝ}
    (ha : A ⊆ window 0 M) (hp : ∀ p ∈ P, p.Prime)
    (hs : ∀ a ∈ A, a.primeFactors ⊆ P)
    (hd : ∀ w : ℕ → ℝ, (∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) →
      (∑ a ∈ A, valuationScore P w a) -
        ∑ b ∈ window x M, max (valuationScore P w b - 1) 0 ≤ C) :
    ∃ B ⊆ window x M, Covers A B ∧ (B.card : ℝ) ≤ C + P.card := by
  classical
  let W := window x M
  let v (p : P) (b : W) : ℕ := b.val.factorization p.val
  let d (p : P) : ℝ := ∑ a ∈ A, (a.factorization p.val : ℝ)
  have hc (p : P) : d p ≤ ∑ b : W, (v p b : ℝ) := by
    simpa only [d, v, W, sum_coe_sort (window x M) (fun b : ℕ ↦ (b.factorization p.val : ℝ))] using
      valuation_transport (x := x) ha (hp p p.property) (fun k ↦ (k : ℝ))
        (fun i j hij ↦ Nat.cast_le.mpr hij) (fun k ↦ Nat.cast_nonneg k)
  obtain ⟨S, hcard, hrow⟩ := select_of_dual v d C hc (by
    intro u hu
    let w (p : ℕ) : ℝ := if h : p ∈ P then u ⟨p, h⟩ else 0
    have h1 := hd w (fun p h ↦ by simpa only [w, dite_eq_left h] using hu ⟨p,h⟩)
    have heq (a : ℕ) : (∑ p : P, u p * (a.factorization p.val : ℝ)) = valuationScore P w a := by
      rw [valuationScore, ← sum_coe_sort P (fun p : ℕ ↦ w p * (a.factorization p : ℝ))]
      exact sum_congr rfl fun p _ ↦ by simp [w, p.property]
    simp only [d, mul_sum]
    rw [sum_comm]
    simp only [heq, v]
    rwa [← sum_coe_sort W (fun b : ℕ ↦ max (valuationScore P w b - 1) 0)] at h1)
  let B := S.map (Function.Embedding.subtype fun b ↦ b ∈ W)
  have hB : B ⊆ W := by
    intro b hb
    obtain ⟨j, _, rfl⟩ := mem_map.mp hb
    exact j.property
  have hA0 (a : ℕ) (h : a ∈ A) : a ≠ 0 := (mem_Ioc.mp (ha h)).1.ne'
  have hB0 (b : ℕ) (h : b ∈ B) : b ≠ 0 := by have := (mem_Ioc.mp (hB h)).1; omega
  refine ⟨B, hB, ?_, by simpa [B] using hcard⟩
  apply (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr hA0) (prod_ne_zero_iff.mpr hB0)).mp
  intro p
  rw [Nat.factorization_prod_apply hA0, Nat.factorization_prod_apply hB0]
  by_cases hh : p ∈ P
  · simp only [B, sum_map, Function.Embedding.subtype_apply]
    have hrows := hrow ⟨p, hh⟩
    simp only [d, v] at hrows
    exact_mod_cast hrows
  · have hz (a : ℕ) (ha' : a ∈ A) : a.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp fun h ↦ hh (hs a ha' h)
    rw [sum_eq_zero hz]
    exact Nat.zero_le _

/-- A uniform dual estimate gives the required selection on every positive window. -/
theorem positive_of_transfer (h : TransferBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (A : Finset ℕ) {M : ℕ}, N ≤ A.card → A ⊆ window 0 M → ∀ x : ℕ,
      ∃ B ⊆ window x M, Covers A B ∧ (B.card : ℝ) ≤ (2 + ε) * A.card := by
  let δ := min (ε / 3) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨N, hN⟩ := h δ hδ
  obtain ⟨N', hN'⟩ := eventually_atTop.mp (few_labels δ hδ)
  refine ⟨max N N', ?_⟩
  intro A M hn ha x
  have ha' (a : ℕ) (hh : a ∈ A) : 0 < a ∧ a ≤ M := by simpa [window] using ha hh
  by_cases hbig : (2 * A.card)^3 ≤ M
  · obtain ⟨B, hB, hc, hcost⟩ := large_height (x := x) ha' hbig
    exact ⟨B,hB,hc,(by exact_mod_cast hcost : (B.card : ℝ) ≤ 2 * A.card) |>.trans
      (by nlinarith [mul_nonneg hε.le (Nat.cast_nonneg A.card)])⟩
  let K := 5 * A.card
  let S := smoothPart A K
  let P := (min K M).primesLE
  have hS : S ⊆ A := filter_subset ..
  have hsc := card_le_card hS
  have hP (p : ℕ) (hh : p ∈ P) := Nat.mem_primesLE.mp hh
  have hlabels : (P.card : ℝ) ≤ δ * A.card :=
    (by exact_mod_cast card_le_card (Nat.primesLE_mono (min_le_left K M)) :
      (P.card : ℝ) ≤ K.primesLE.card).trans (hN' _ (le_trans (le_max_right ..) hn))
  have hAM : A.card ≤ M := by simpa [window] using card_le_card ha
  obtain ⟨B, hB, hc, hcost⟩ := select_smooth (P := P) (x := x) (hS.trans ha)
    (fun p hh ↦ (hP p hh).2) (by
      intro a hh p hpa
      exact Nat.mem_primesLE.mpr ⟨le_min ((mem_filter.mp hh).2 p hpa)
        ((Nat.le_of_dvd (ha' a (hS hh)).1 (Nat.dvd_of_mem_primeFactors hpa)).trans (ha' a (hS hh)).2),
        Nat.prime_of_mem_primeFactors hpa⟩)
    (fun w hw ↦ hN A.card (le_trans (le_max_left ..) hn) M hAM (le_of_not_ge hbig) x S P w
      (hS.trans ha) hsc (fun p hh ↦ ⟨(hP p hh).2, (le_min_iff.mp (hP p hh).1).1,
        (le_min_iff.mp (hP p hh).1).2⟩) hw)
  have hδ1 := min_le_right (ε / 3) (1/2 : ℝ)
  have hδε := min_le_left (ε / 3) (1/2 : ℝ)
  change δ ≤ 1/2 at hδ1
  change δ ≤ ε/3 at hδε
  have hr : ((A.card - S.card : ℕ) : ℝ) = A.card - S.card := Nat.cast_sub hsc
  have hcount : B.card + 2 * (A.card-S.card) ≤ K := by
    change _ ≤ 5 * A.card
    exact_mod_cast (show (B.card : ℝ) + 2 * ((A.card-S.card : ℕ) : ℝ) ≤ 5 * A.card by
      rw [hr]
      nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg A.card)])
  obtain ⟨T, ht, hcov, htc⟩ := peel ha' hB hc hcount
  refine ⟨T,ht,hcov, (Nat.cast_le.mpr htc : (T.card : ℝ) ≤ _) |>.trans ?_⟩
  push_cast [hr]
  nlinarith [mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg A.card)]

end ErdosSuranyi708
