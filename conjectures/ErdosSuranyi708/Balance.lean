module

public import conjectures.ErdosSuranyi708.Site
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708
open Finset

/-- Combine a relative error for long terms and an absolute error for a small
family of terms. -/
theorem sum_comparison {ι : Type*} [Fintype ι] (small : Finset ι)
    (S I : ι → ℝ) {δ c : ℝ} (hS : ∀ i, 0 ≤ S i) (hδ : 0 ≤ δ)
    (hsmall : ∀ i ∈ small, S i - I i ≤ c)
    (hlarge : ∀ i ∉ small, S i - I i ≤ δ*S i) :
    (1-δ) * (∑ i, S i) - c * small.card ≤ ∑ i, I i := by
  classical
  have hi (i : ι) : S i - I i ≤ δ*S i + if i ∈ small then c else 0 := by
    by_cases h : i ∈ small
    · rw [ite_eq_left h]
      exact (hsmall i h).trans (le_add_of_nonneg_left (mul_nonneg hδ (hS i)))
    · simpa [h] using hlarge i h
  have h := sum_le_sum (s := univ) (fun i _ ↦ hi i)
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,← sum_filter,filter_mem_eq_inter,
    univ_inter,sum_const,nsmul_eq_mul] at h
  linarith

/-- Bound the contribution of a small input set using a level cutoff. -/
theorem sum_source_tail {A W : Finset ℕ} (hA : A ⊆ W) (F z : ℕ → ℝ) (H : ℝ)
    (hn : ∀ a ∈ W, 0 ≤ F a) (hl : ∀ a ∈ A, F a ≤ z a) (hH : 0 ≤ H) :
    ∑ a ∈ A, F a ≤ H * A.card + ∑ a ∈ W, if H < z a then F a else 0 := by
  classical
  have hi (a : ℕ) (h : a ∈ A) : F a ≤ H + (if H < z a then F a else 0) := by
    split
    · linarith
    next hz => linarith [(hl a h)]
  have h := sum_le_sum hi
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_comm (A.card : ℝ)] at h
  apply h.trans (add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg hA ?_))
  intro a hw _
  split
  · exact hn a hw
  · rfl

/-- When the source mass is large, its high-score tail controls the input.
When it is small, the relative interval error is already an absolute bound. -/
theorem balance_transfer {A W I : Finset ℕ} {F z : ℕ → ℝ} {n : ℕ} (hA : A ⊆ W)
    (hm : A.card ≤ n) {t η H δ e : ℝ} (hH : 0 ≤ H) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/4)
    (he : 0 ≤ e) (hF : ∀ a ∈ W, 0 ≤ F a)
    (hsite : ∀ a ∈ A, z a ≤ F a + t + η)
    (hwin : ∀ b ∈ I, F b ≤ max (z b-1) 0)
    (hcmp : (1-δ) * (∑ a ∈ W, F a) - e ≤ ∑ b ∈ I, F b)
    (htail : ∑ a ∈ A, F a ≤ H*A.card + (1/4)*(∑ a ∈ W, F a) + e) :
    (∑ a ∈ A, z a) - ∑ b ∈ I, max (z b-1) 0 ≤ (t+η)*A.card + 2*H*δ*n + 2*e := by
  have hsrc := sum_le_sum hsite
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at hsrc
  have htarget := sum_le_sum hwin
  have hall := sum_le_sum_of_subset_of_nonneg (f := F) hA fun a h _ ↦ hF a h
  have hM := Nat.cast_le (α := ℝ) |>.mpr hm
  let T := ∑ a ∈ W, F a
  change _ ≤ H * A.card + (1/4)*T + e at htail
  change (1-δ)*T-e ≤ _ at hcmp
  change _ ≤ T at hall
  by_cases hsmall : T ≤ 2*H*n
  · nlinarith [mul_le_mul_of_nonneg_left hsmall hδ]
  · have hT : 0 ≤ T := sum_nonneg hF
    nlinarith [mul_le_mul_of_nonneg_left hM hH,
      mul_le_mul_of_nonneg_right hδ' hT, mul_nonneg (mul_nonneg hH hδ) (Nat.cast_nonneg n)]

end ErdosSuranyi708
