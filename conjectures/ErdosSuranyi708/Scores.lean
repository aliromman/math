module

public import conjectures.ErdosSuranyi708.Reduction
public import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708
open Finset

def valuationScore (P : Finset ℕ) (w : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ p ∈ P, w p * (a.factorization p : ℝ)

def cappedScore (P : Finset ℕ) (w : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ p ∈ P, min 1 (w p * (a.factorization p : ℝ))

/-- The cost estimate on intervals below the cubic cutoff. -/
def TransferBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ M : ℕ, n ≤ M → M ≤ (2 * n) ^ 3 →
    ∀ (x : ℕ) (A P : Finset ℕ) (w : ℕ → ℝ), A ⊆ window 0 M → A.card ≤ n →
      (∀ p ∈ P, p.Prime ∧ p ≤ 5 * n ∧ p ≤ M) → (∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) →
      (∑ a ∈ A, valuationScore P w a) -
        ∑ b ∈ window x M, max (valuationScore P w b - 1) 0 ≤ 2 * A.card + ε * n

/-- For one prime, match every source to a distinct site of at least the same
valuation. This is the nested-family case of Hall's theorem, as used by Chen. -/
theorem valuation_transport {A : Finset ℕ} {x M p : ℕ}
    (hA : A ⊆ window 0 M) (hp : p.Prime) (g : ℕ → ℝ)
    (hg : Monotone g) (h0 : ∀ j, 0 ≤ g j) :
    ∑ a ∈ A, g (a.factorization p) ≤ ∑ b ∈ window x M, g (b.factorization p) := by
  classical
  let t (a : A) := (window x M).filter (p ^ (a.val.factorization p) ∣ ·)
  obtain ⟨f, hf, hmem⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp (by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmin⟩ := s.exists_min_image (fun a : A ↦ a.val.factorization p) hs
      let q := p ^ (a.val.factorization p)
      have hi : s.image Subtype.val ⊆ (window 0 M).filter (q ∣ ·) := by
        intro b hb
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
        have hn := (mem_Ioc.mp (hA j.property)).1
        exact mem_filter.mpr ⟨hA j.property,
          (hp.pow_dvd_iff_le_factorization hn.ne').mpr (hmin j hj)⟩
      calc
        s.card = (s.image Subtype.val).card := (card_image_of_injective s Subtype.val_injective).symm
        _ ≤ ((window 0 M).filter (q ∣ ·)).card := card_le_card hi
        _ = M / q := by simp [window, Nat.Ioc_filter_dvd_card_eq_div]
        _ ≤ ((window x M).filter (q ∣ ·)).card := window_multiples_lower x M q
        _ ≤ (s.biUnion t).card := card_le_card fun b hb ↦ mem_biUnion.mpr ⟨a, ha, hb⟩
    · simp [not_nonempty_iff_eq_empty.mp hs])
  have hpair (a : A) := mem_filter.mp (hmem a)
  rw [← sum_coe_sort A (fun a : ℕ ↦ g (a.factorization p))]
  calc
    _ ≤ ∑ a : A, g ((f a).factorization p) := sum_le_sum fun a _ ↦ hg
      ((hp.pow_dvd_iff_le_factorization (by have := (mem_Ioc.mp (hpair a).1).1; omega)).mp (hpair a).2)
    _ = ∑ b ∈ univ.image f, g (b.factorization p) := by rw [sum_image hf.injOn]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (by intro b hb; obtain ⟨a, _, rfl⟩ := mem_image.mp hb; exact (hpair a).1) (fun b _ _ ↦ h0 _)

private lemma cap_hinge (P : Finset ℕ) (v : ℕ → ℝ) (hn : ∀ p ∈ P, 0 ≤ v p) :
    max ((∑ p ∈ P, v p) - 1) 0 =
    (∑ p ∈ P, max (v p - 1) 0) + max ((∑ p ∈ P, min 1 (v p)) - 1) 0 := by
  have hsplit : ∑ p ∈ P, v p = (∑ p ∈ P, max (v p - 1) 0) + ∑ p ∈ P, min 1 (v p) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun p _ ↦ by rcases le_total 1 (v p) with h|h <;> simp [h]
  by_cases hbig : ∃ p ∈ P, 1 ≤ v p
  · obtain ⟨p, hp, hv⟩ := hbig
    have h1 : 1 ≤ ∑ p ∈ P, min 1 (v p) :=
      by simpa only [min_eq_left hv] using
        (single_le_sum (fun j hj ↦ le_min zero_le_one (hn j hj)) hp)
    have h2 : 0 ≤ ∑ p ∈ P, max (v p - 1) 0 := sum_nonneg fun _ _ ↦ le_max_right _ _
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · have hzero : (∑ p ∈ P, max (v p - 1) 0) = 0 :=
      sum_eq_zero fun p hp ↦ max_eq_right (by have := not_exists.mp hbig p; grind)
    rw [hzero, zero_add] at hsplit ⊢
    rw [hsplit]

/-- Cap each prime's score at one. All excess is transported prime by prime. -/
theorem cap_transfer {A P : Finset ℕ} {x M : ℕ} (hA : A ⊆ window 0 M)
    (hp : ∀ p ∈ P, p.Prime) (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) :
    (∑ a ∈ A, valuationScore P w a) - ∑ b ∈ window x M, max (valuationScore P w b - 1) 0 ≤
    (∑ a ∈ A, cappedScore P w a) - ∑ b ∈ window x M, max (cappedScore P w b - 1) 0 := by
  let excess (p a : ℕ) := max (w p * (a.factorization p : ℝ) - 1) 0
  have cancel : (∑ a ∈ A, ∑ p ∈ P, excess p a) ≤ ∑ b ∈ window x M, ∑ p ∈ P, excess p b := by
    rw [sum_comm, sum_comm (s := window x M)]
    apply sum_le_sum
    intro p h
    exact valuation_transport hA (hp p h) (fun j ↦ max (w p * j - 1) 0)
      (fun i j hij ↦ max_le_max (sub_le_sub_right (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr hij) (hw p h)) _) le_rfl) (fun _ ↦ le_max_right _ _)
  have hsource (a : ℕ) : valuationScore P w a = cappedScore P w a + ∑ p ∈ P, excess p a := by
    unfold valuationScore cappedScore excess
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    grind
  have htarget (b : ℕ) : max (valuationScore P w b - 1) 0 =
      (∑ p ∈ P, excess p b) + max (cappedScore P w b - 1) 0 :=
    cap_hinge P _ fun p h ↦ mul_nonneg (hw p h) (Nat.cast_nonneg _)
  simp_rw [htarget, hsource, sum_add_distrib]
  linarith

end ErdosSuranyi708
