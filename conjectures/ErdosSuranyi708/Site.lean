module

public import conjectures.ErdosSuranyi708.Buckets
public import conjectures.ErdosSuranyi708.CrossingTrim
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708
open Finset

def activeLabels (P : Finset ℕ) (a : ℕ) : Finset ℕ := P.filter (· ∣ a)

noncomputable def siteCost (Y K M : ℕ) (w : ℕ → ℝ) (a p : ℕ) : ℕ :=
  p ^ siteExponent Y K M w p a

noncomputable def siteSum (Y K M : ℕ) (P : Finset ℕ) (w : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ p ∈ activeLabels P a, siteWeight Y K M w a p

noncomputable def transferSum (Y K M : ℕ) (s : ℝ) (P : Finset ℕ) (w : ℕ → ℝ) (a : ℕ) : ℝ :=
  truncatedCrossing Y M s (activeLabels P a) (siteCost Y K M w a) (siteWeight Y K M w a)

private theorem cap_on_active (P : Finset ℕ) (w : ℕ → ℝ) (a : ℕ) :
    cappedScore P w a = ∑ p ∈ activeLabels P a, min 1 (w p * (a.factorization p : ℝ)) := by
  rw [cappedScore,activeLabels,sum_filter]
  apply sum_congr rfl
  intro p _
  split
  · rfl
  next h => simp [Nat.factorization_eq_zero_of_not_dvd h]

theorem siteSum_le (Y K M : ℕ) {P : Finset ℕ} {w : ℕ → ℝ} (hw : ∀ p ∈ P, 0 ≤ w p) (a : ℕ) :
    siteSum Y K M P w a ≤ cappedScore P w a := by
  rw [cap_on_active]
  exact sum_le_sum fun p h ↦ siteWeight_le (hw p (mem_filter.mp h).1)

theorem siteSum_close {Y K M : ℕ} {P : Finset ℕ} {w : ℕ → ℝ} (hK : 0 < K)
    (hp : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, 0 ≤ w p) {a : ℕ} (ha : 0 < a) (ham : a ≤ M) :
    cappedScore P w a ≤ siteSum Y K M P w a + (Y + 1 : ℕ) * (K : ℝ)⁻¹ := by
  rw [cap_on_active]
  let S := activeLabels P a
  have ht := sum_le_sum (s := S) (fun p h ↦ sourceWeight_le (Y := Y) hK
    (hw p (mem_filter.mp h).1) (hp p (mem_filter.mp h).1) ha ham (mem_filter.mp h).2)
  rw [sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul] at ht
  have hc : (S.filter (· ≤ Y)).card ≤ Y+1 := by
    rw [← card_range (Y+1)]
    exact card_le_card fun _ h ↦ mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp h).2)
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc)
    (inv_nonneg.mpr (Nat.cast_nonneg _))))

theorem siteCost_fit {Y K M a : ℕ} (P : Finset ℕ) (w : ℕ → ℝ) (hp : ∀ p ∈ P, p.Prime)
    (ha : 0 < a) : ∏ p ∈ activeLabels P a, siteCost Y K M w a p ≤ a := by
  let T := activeLabels P a
  have hT : T ⊆ a.primeFactors := fun p h ↦ Nat.mem_primeFactors.mpr
    ⟨hp p (mem_filter.mp h).1,(mem_filter.mp h).2,ha.ne'⟩
  apply Nat.le_of_dvd ha
  calc
    ∏ p ∈ T, siteCost Y K M w a p ∣ ∏ p ∈ T, p ^ a.factorization p :=
      prod_dvd_prod_of_dvd _ _ fun p _ ↦ pow_dvd_pow _ (lastCut_le ..)
    _ ∣ ∏ p ∈ a.primeFactors, p ^ a.factorization p := prod_dvd_prod_of_subset _ _ _ hT
    _ = a := Nat.prod_factorization_pow_eq_self ha.ne'

theorem siteCost_ge {Y K M a p : ℕ} {P : Finset ℕ} {w : ℕ → ℝ} (ha : 0 < a)
    (hp : ∀ p ∈ P, p.Prime) (h : p ∈ activeLabels P a) : 2 ≤ p ∧ p ≤ siteCost Y K M w a p := by
  have hp' := hp p (mem_filter.mp h).1
  have hv := hp'.factorization_pos_of_dvd ha.ne' (mem_filter.mp h).2
  exact ⟨hp'.two_le, Nat.le_self_pow (Nat.ne_of_gt (le_lastCut (grid_one ..) hv)) _⟩

theorem transferSum_upper {Y K M : ℕ} {s : ℝ} {P : Finset ℕ} {w : ℕ → ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hw : ∀ p ∈ P, 0 ≤ w p) (a : ℕ) :
    transferSum Y K M s P w a ≤ max (cappedScore P w a - 1) 0 := by
  apply (truncatedCrossing_le hs hs1 _ _ _ _ _ (fun p h ↦
    ⟨siteWeight_nonneg (hw p (mem_filter.mp h).1),min_le_left ..⟩)).trans
  exact max_le_max (sub_le_sub_right (siteSum_le Y K M hw a) _) le_rfl

theorem transferSum_nonneg {Y K M : ℕ} {s : ℝ} {P : Finset ℕ} {w : ℕ → ℝ}
    (hs : 0 < s) (hh : s < 1/2) (hw : ∀ p ∈ P, 0 ≤ w p) (hp : ∀ p ∈ P, p.Prime)
    {a : ℕ} (ha : 0 < a) (ham : a ≤ M) : 0 ≤ transferSum Y K M s P w a :=
  truncatedCrossing_nonneg hs hh (fun p h ↦
    ⟨(siteCost_ge (Y := Y) (K := K) (M := M) (w := w) ha hp h).1.trans' (by decide),
      (siteCost_ge ha hp h).2⟩) ((siteCost_fit P w hp ha).trans ham)
    (fun p h ↦ siteWeight_nonneg (hw p (mem_filter.mp h).1))

theorem transferSum_source {s ε : ℝ} (hs : 0 < s) (hh : s < 1/2) (hε : 0 < ε) :
    ∃ Y₀ : ℕ, ∀ Y ≥ Y₀, ∀ {K M : ℕ} {P : Finset ℕ} {w : ℕ → ℝ}, 0 < K →
      (∀ p ∈ P, 0 ≤ w p) → (∀ p ∈ P, p.Prime) → ∀ {a : ℕ}, 0 < a → a ≤ M →
      cappedScore P w a ≤ transferSum Y K M s P w a + 1/s + ε + (Y+1 : ℕ) * (K : ℝ)⁻¹ := by
  obtain ⟨Y₀, hY₀⟩ := truncatedCrossing_lower_uniform hs hh hε
  refine ⟨Y₀, ?_⟩
  intro Y hY K M P w hK hw hp a ha ham
  have h := hY₀ _ hY M (activeLabels P a) (siteCost Y K M w a) (siteWeight Y K M w a)
    (fun p h ↦ siteCost_ge ha hp h) (fun p h ↦ ⟨siteWeight_nonneg (hw p (mem_filter.mp h).1),
      min_le_left ..⟩) ((siteCost_fit P w hp ha).trans ham)
  have hlow : siteSum Y K M P w a - 1/s ≤ transferSum Y K M s P w a + ε := (le_max_left ..).trans h
  linarith [siteSum_close (Y := Y) hK hp hw ha ham]

end ErdosSuranyi708
