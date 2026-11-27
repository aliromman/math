module

public import conjectures.ErdosSuranyi708.Scores
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace ErdosSuranyi708
open Finset

noncomputable def primeMean (P : Finset ℕ) (w : ℕ → ℝ) : ℝ := ∑ p ∈ P, w p / p

private def firstScore (P : Finset ℕ) (w : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ p ∈ P, if p ∣ a then w p else 0

private lemma initial_count (M d : ℕ) (c : ℝ) :
    (∑ a ∈ window 0 M, if d ∣ a then c else 0) = (M / d : ℕ) * c := by
  rw [← sum_filter]
  simp [window, Nat.Ioc_filter_dvd_card_eq_div]

private lemma floor_le {M d : ℕ} (hd : 0 < d) : ((M / d : ℕ) : ℝ) ≤ M / (d : ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hd)).mpr
  exact_mod_cast Nat.div_mul_le_self M d

private lemma le_floor_add {M d : ℕ} (hd : 0 < d) : (M : ℝ) / d ≤ (M / d : ℕ) + (1 : ℝ) := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr
  have := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (M / d))
  exact_mod_cast this.le

private lemma first_moment {P : Finset ℕ} (w : ℕ → ℝ) {M : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ M) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) :
    M * (primeMean P w - 1) ≤ ∑ a ∈ window 0 M, firstScore P w a := by
  have hcard : P.card ≤ M := by
    have hs : P ⊆ window 0 M := by
      intro p hp
      simpa [window] using And.intro (hP p hp).1.pos (hP p hp).2
    simpa [window] using card_le_card hs
  have ht : (∑ p ∈ P, (M : ℝ) * (w p / p)) ≤ ∑ p ∈ P, (((M/p : ℕ) : ℝ) * w p + 1) := by
    apply sum_le_sum
    intro p hp
    have := mul_le_mul_of_nonneg_right (le_floor_add (M := M) (hP p hp).1.pos) (hw p hp).1
    calc
      _ = ((M : ℝ) / p) * w p := by ring
      _ ≤ _ := by linarith [(hw p hp).2]
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, ← mul_sum] at ht
  unfold primeMean
  simp only [firstScore]
  rw [sum_comm]
  simp only [initial_count]
  have hcard' : (P.card : ℝ) ≤ M := Nat.cast_le.mpr hcard
  linarith

private lemma pair_count {M p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) (hv1 : v ≤ 1) :
    (∑ a ∈ window 0 M, (if p ∣ a then v else 0) * (if q ∣ a then w else 0)) ≤
      M * ((v / p) * (w / q)) + (if p = q then M * (w / q) else 0) := by
  by_cases h : p = q
  · subst q
    simp only [ite_true]
    have heq (a : ℕ) : (if p ∣ a then v else 0) * (if p ∣ a then w else 0) =
        if p ∣ a then v*w else 0 := by split_ifs <;> simp
    simp_rw [heq, initial_count]
    have hb := mul_le_mul_of_nonneg_right (floor_le (M := M) hp.pos) (mul_nonneg hv hw)
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv1 hw)
      (div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg p))
    have hn : 0 ≤ (M : ℝ) * ((v / p) * (w / p)) := by positivity
    simp only [div_eq_mul_inv] at hb hc hn ⊢
    nlinarith
  · rw [ite_eq_right h]
    have hc := (Nat.coprime_primes hp hq).mpr h
    have heq (a : ℕ) : (if p ∣ a then v else 0) * (if q ∣ a then w else 0) =
        if p*q ∣ a then v*w else 0 := by
      have he : p*q ∣ a ↔ p ∣ a ∧ q ∣ a := ⟨fun hh ↦ ⟨dvd_of_mul_right_dvd hh,
        dvd_of_mul_left_dvd hh⟩, fun ⟨h1,h2⟩ ↦ hc.mul_dvd_of_dvd_of_dvd h1 h2⟩
      simp only [he]
      split_ifs <;> simp_all
    simp_rw [heq, initial_count]
    have hb := mul_le_mul_of_nonneg_right (floor_le (M := M) (Nat.mul_pos hp.pos hq.pos))
      (mul_nonneg hv hw)
    push_cast at hb
    convert hb using 1; ring

private lemma second_moment {P : Finset ℕ} (w : ℕ → ℝ) {M : ℕ}
    (hp : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) :
    (∑ a ∈ window 0 M, firstScore P w a ^ 2) ≤ M * (primeMean P w ^ 2 + primeMean P w) := by
  simp only [firstScore, sq, sum_mul, mul_sum]
  calc
    _ = ∑ p ∈ P, ∑ q ∈ P, ∑ a ∈ window 0 M,
        (if p ∣ a then w p else 0) * (if q ∣ a then w q else 0) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      rw [sum_comm]
      exact sum_congr rfl fun q _ ↦ sum_congr rfl fun a _ ↦ mul_comm _ _
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, (M * (w p / p * (w q / q)) + if p = q then M * (w q / q) else 0) :=
      sum_le_sum fun p h ↦ sum_le_sum fun q h' ↦
        pair_count (hp p h) (hp q h') (hw p h).1 (hw q h').1 (hw p h).2
    _ = _ := by
      simp only [sum_add_distrib, sum_ite_eq, ← mul_sum, ← sum_mul, primeMean]
      simp only [sum_ite_mem, inter_self, ← mul_sum]
      ring

private theorem dense_mass {P : Finset ℕ} {w : ℕ → ℝ} {M : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ M) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1)
    (hm : 20 ≤ primeMean P w) :
    (M : ℝ) ≤ ∑ a ∈ window 0 M, min 2 (cappedScore P w a) := by
  let μ := primeMean P w
  let Y := firstScore P w
  let Z := cappedScore P w
  have h1 := first_moment w hP hw
  have h2 := second_moment (M := M) w (fun p h ↦ (hP p h).1) hw
  change M * (μ-1) ≤ ∑ a ∈ window 0 M, Y a at h1
  change ∑ a ∈ window 0 M, Y a ^ 2 ≤ M * (μ^2+μ) at h2
  change 20 ≤ μ at hm
  have hle (a : ℕ) (ha : a ∈ window 0 M) : Y a ≤ Z a := by
    apply sum_le_sum
    intro p hp
    by_cases hd : p ∣ a
    · rw [ite_eq_left hd]
      have hj : 1 ≤ a.factorization p :=
        (hP p hp).1.factorization_pos_of_dvd (mem_Ioc.mp ha).1.ne' hd
      exact le_min (hw p hp).2 <| le_mul_of_one_le_right (hw p hp).1 (by exact_mod_cast hj)
    · simp only [ite_eq_right hd, Nat.factorization_eq_zero_of_not_dvd hd, Nat.cast_zero, mul_zero]
      norm_num
  have hz (a : ℕ) : 0 ≤ Z a := sum_nonneg fun p hp ↦ le_min zero_le_one
    (mul_nonneg (hw p hp).1 (Nat.cast_nonneg _))
  have hsite (a : ℕ) (ha : a ∈ window 0 M) :
      6 * μ ≤ 3*μ * min 2 (Z a) + ((Y a)^2 - 2*μ*Y a + μ^2) := by
    rcases le_total 2 (Z a) with hh|hh
    · rw [min_eq_left hh]
      nlinarith [sq_nonneg (Y a - μ)]
    · rw [min_eq_right hh]
      have hy := (hle a ha).trans hh
      have hy' : 0 ≤ (μ-Y a)^2-(μ-2)^2 := sub_nonneg.mpr
        (sq_le_sq' (by linarith) (by linarith))
      nlinarith [mul_nonneg (by linarith : 0 ≤ 3*μ) (hz a),
        mul_nonneg (by linarith : 0 ≤ μ-20) (by linarith : 0 ≤ μ+10)]
  have ht := sum_le_sum hsite
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, window, Nat.card_Ioc,
    zero_add, Nat.sub_zero, nsmul_eq_mul] at ht h1 h2 ⊢
  change (M : ℝ) ≤ ∑ a ∈ Ioc 0 M, min 2 (Z a)
  by_contra! hn
  nlinarith [mul_pos (by linarith : 0 < μ) (sub_pos.mpr hn),
    mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 2*μ)]

/-- If the prime mean is large, the initial interval supplies the entire dual budget. -/
theorem dense_transfer {P A : Finset ℕ} {w : ℕ → ℝ} {M x : ℕ} (hA : A ⊆ window 0 M)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ M) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1)
    (hm : 20 ≤ primeMean P w) :
    (∑ a ∈ A, cappedScore P w a) - ∑ b ∈ window x M, max (cappedScore P w b - 1) 0 ≤ 2 * A.card := by
  let W := window 0 M
  let Z := cappedScore P w
  have hall : (∑ a ∈ W, Z a) ≤ ∑ b ∈ window x M, Z b := by
    simp only [Z, cappedScore]
    rw [sum_comm, sum_comm (s := window x M)]
    apply sum_le_sum
    intro p hp
    exact valuation_transport Subset.rfl (hP p hp).1 (fun j ↦ min 1 (w p * j))
      (fun i j hij ↦ min_le_min le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) (hw p hp).1))
      (fun j ↦ le_min zero_le_one (mul_nonneg (hw p hp).1 (Nat.cast_nonneg j)))
  have hg := dense_mass hP hw hm
  change (M : ℝ) ≤ ∑ a ∈ W, min 2 (Z a) at hg
  rw [← sum_sdiff hA] at hg hall
  have hlow : ∑ a ∈ W \ A, min 2 (Z a) ≤ ∑ a ∈ W \ A, Z a :=
    sum_le_sum fun a _ ↦ min_le_right _ _
  have ha : ∑ a ∈ A, min 2 (Z a) ≤ A.card * (2 : ℝ) :=
    (sum_le_sum (s := A) (fun a _ ↦ min_le_left 2 (Z a))).trans_eq (by simp)
  have hi : ∑ b ∈ window x M, (Z b - 1) ≤ ∑ b ∈ window x M, max (Z b - 1) 0 :=
    sum_le_sum fun _ _ ↦ le_max_left _ _
  simp only [sum_sub_distrib, sum_const, window, Nat.card_Ioc, nsmul_eq_mul, mul_one,
    Nat.add_sub_cancel_left] at hi
  change (∑ a ∈ A, Z a) - ∑ b ∈ window x M, max (Z b - 1) 0 ≤ 2 * A.card
  change (∑ b ∈ window x M, Z b) - M ≤ ∑ b ∈ window x M, max (Z b - 1) 0 at hi
  linarith

end ErdosSuranyi708
