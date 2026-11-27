module

public import conjectures.ErdosSuranyi708.Statement
public import conjectures.ErdosSuranyi708.Mean
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708
open Finset

/-- Count multiples of the base that avoid every forbidden factor on the quotient. -/
noncomputable def siftCount (x M d : ℕ) (D : Finset ℕ) : ℝ :=
  ∑ b ∈ window x M, if d ∣ b ∧ ∀ v ∈ D, ¬ d * v ∣ b then 1 else 0

/-- Sum the counts for the divisors that have a nonzero sieve coefficient. -/
noncomputable def siftSum (x M d : ℕ) (D : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ Icc 1 (M / d), c e * siftCount x M (d * e) D

private noncomputable def rawCount (x M d : ℕ) : ℝ :=
  ((window x M).filter (d ∣ ·)).card

private lemma raw_bounds (x M d : ℕ) : (M / d : ℕ) ≤ rawCount x M d ∧
    rawCount x M d ≤ (M / d : ℕ) + 1 := by
  have hs : (window x M).filter (d ∣ ·) =
      ((Ioc 0 (x+M)).filter (d ∣ ·)) \ ((Ioc 0 x).filter (d ∣ ·)) := by
    ext b
    simp only [window, mem_filter, mem_Ioc, mem_sdiff]
    omega
  have sub : (Ioc 0 x).filter (d ∣ ·) ⊆ (Ioc 0 (x+M)).filter (d ∣ ·) := by
    intro b hb
    simp only [mem_filter, mem_Ioc] at hb ⊢
    omega
  simp only [rawCount, hs, card_sdiff_of_subset sub, Nat.Ioc_filter_dvd_card_eq_div]
  have hlo := Nat.div_add_div_le_add_div (x := x) (y := M) (z := d)
  have hhi := Nat.add_div_le_div_add_div_add_one x M d
  constructor
  · exact_mod_cast (show M/d ≤ (x+M)/d-x/d by omega)
  · have hz : ((x+M)/d-x/d : ℕ) ≤ (M/d+1 : ℕ) := Nat.sub_le_iff_le_add.mpr
      (by simpa only [add_comm, add_left_comm, add_assoc] using hhi)
    exact_mod_cast hz

private lemma raw_discrepancy (x M d : ℕ) : |rawCount x M d - rawCount 0 M d| ≤ 1 := by
  obtain ⟨h₁, h₂⟩ := raw_bounds x M d
  obtain ⟨h₃, h₄⟩ := raw_bounds 0 M d
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private noncomputable def moment (x M d : ℕ) (D : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ E ∈ D.powersetCard r, rawCount x M (d * ∏ v ∈ E, v)

private lemma product_dvd_iff {E : Finset ℕ} (hc : (E : Set ℕ).Pairwise Nat.Coprime) (t : ℕ) :
    (∏ v ∈ E, v) ∣ t ↔ ∀ v ∈ E, v ∣ t := by
  refine ⟨fun hd v hv ↦ (dvd_prod_of_mem id hv).trans hd, ?_⟩
  exact prod_dvd_of_isRelPrime (s := id)
    (fun i hi j hj hij ↦ Nat.coprime_iff_isRelPrime.mp (hc hi hj hij))

private lemma site_moment (d b : ℕ) (hd : 0 < d) (D : Finset ℕ)
    (hc : (D : Set ℕ).Pairwise Nat.Coprime) (r : ℕ) :
    (∑ E ∈ D.powersetCard r, if d * (∏ v ∈ E, v) ∣ b then (1 : ℝ) else 0) =
      if d ∣ b then ((D.filter fun v ↦ d*v ∣ b).card.choose r : ℝ) else 0 := by
  classical
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    simp only [Nat.mul_dvd_mul_iff_left hd, sum_boole]
    congr 1
    rw [← card_powersetCard]
    congr 1
    ext E
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hes, her⟩, hdv⟩
      exact ⟨fun v hv ↦ mem_filter.mpr ⟨hes hv, (dvd_prod_of_mem id hv).trans hdv⟩, her⟩
    · rintro ⟨hes, her⟩
      have hsub : E ⊆ D := fun v hv ↦ (mem_filter.mp (hes hv)).1
      exact ⟨⟨hsub, her⟩, (product_dvd_iff (hc.mono hsub) t).mpr
        (fun v hv ↦ (mem_filter.mp (hes hv)).2)⟩
  · apply sum_eq_zero
    intro E _
    exact ite_eq_right fun hf ↦ h ((dvd_mul_right d _).trans hf)

private lemma moment_as_sum (x M d : ℕ) (hd : 0 < d) (D : Finset ℕ)
    (hc : (D : Set ℕ).Pairwise Nat.Coprime) (r : ℕ) :
    moment x M d D r = ∑ b ∈ window x M,
      if d ∣ b then ((D.filter fun v ↦ d*v ∣ b).card.choose r : ℝ) else 0 := by
  unfold moment rawCount
  simp_rw [← sum_boole]
  rw [sum_comm]
  exact sum_congr rfl fun b _ ↦ site_moment d b hd D hc r

private lemma alternating_error (m r : ℕ) :
    |(if m = 0 then (1 : ℝ) else 0) -
      ∑ j ∈ range r, (-1 : ℝ)^j * (m.choose j : ℝ)| ≤ m.choose r := by
  cases r with
  | zero => simp; split <;> norm_num
  | succ r =>
    cases m with
    | zero => simp [Finset.sum_range_succ']
    | succ m =>
      have eq : ∑ j ∈ range (r+1), (-1 : ℝ)^j * ((m+1).choose j : ℝ) =
          (-1 : ℝ)^r * (m.choose r : ℝ) := by
        exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := m) (m := r))
      simp only [Nat.succ_ne_zero, ite_false, zero_sub, abs_neg, eq, abs_mul, abs_pow,
        abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
      exact_mod_cast (show m.choose r ≤ (m+1).choose (r+1) by rw [Nat.choose_succ_succ]; omega)

private lemma bonferroni (x M d : ℕ) (hd : 0 < d) (D : Finset ℕ)
    (hc : (D : Set ℕ).Pairwise Nat.Coprime) (r : ℕ) :
    |siftCount x M d D - ∑ j ∈ range r, (-1 : ℝ)^j * moment x M d D j| ≤
      moment x M d D r := by
  simp_rw [moment_as_sum x M d hd D hc]
  simp only [mul_sum]
  rw [sum_comm (s := range r), siftCount, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ ↦ ?_)
  by_cases h : d ∣ b
  · simp only [h, true_and, ite_true]
    have eq : (∀ v ∈ D, ¬ d*v ∣ b) ↔ (D.filter fun v ↦ d*v ∣ b).card = 0 := by
      simp [card_eq_zero, filter_eq_empty_iff]
    simpa only [eq] using alternating_error ((D.filter fun v ↦ d*v ∣ b).card) r
  · simp [h]

private lemma moment_discrepancy (x M d : ℕ) (D : Finset ℕ) (r : ℕ) :
    |moment x M d D r - moment 0 M d D r| ≤ D.card.choose r := by
  unfold moment
  rw [← sum_sub_distrib]
  have h := (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun E (_ : E ∈ D.powersetCard r) ↦ raw_discrepancy x M (d*(∏ v ∈ E, v)))
  simpa using h

/-- Full inclusion and exclusion costs at most one floor error per subset. -/
theorem siftCount_full (x M d : ℕ) (hd : 0 < d) (D : Finset ℕ)
    (hc : (D : Set ℕ).Pairwise Nat.Coprime) :
    |siftCount x M d D - siftCount 0 M d D| ≤ (2:ℝ)^D.card := by
  have h (y : ℕ) : siftCount y M d D =
      ∑ j ∈ range (D.card+1), (-1:ℝ)^j * moment y M d D j := by
    have bound := bonferroni y M d hd D hc (D.card+1)
    have hempty : D.powersetCard (D.card+1) = ∅ := powersetCard_eq_empty.mpr (by omega)
    simpa [moment, hempty, sub_eq_zero] using bound
  rw [h x, h 0, ← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ range (D.card+1), (D.card.choose j:ℝ) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ by
        simpa [← mul_sub, abs_mul] using moment_discrepancy x M d D j)
    _ = _ := by exact_mod_cast Nat.sum_range_choose D.card

private lemma reciprocal_product (D : Finset ℕ) (h : ∀ v ∈ D, 0 < v) :
    (∏ v ∈ D, (1 + (v : ℝ)⁻¹)) ≤ D.card + 1 := by
  induction D using Finset.induction_on_max with
  | empty => simp
  | insert v D hv ih =>
    have hn : v ∉ D := fun e ↦ (hv v e).false
    have hsub : D ⊆ Ico 1 v := fun a ha ↦
      mem_Ico.mpr ⟨h a (mem_insert_of_mem ha), hv a ha⟩
    have hvpos := h v (mem_insert_self ..)
    have hvbig : D.card + 1 ≤ v := by
      have hc := card_le_card hsub
      simp only [Nat.card_Ico] at hc
      omega
    rw [prod_insert hn, card_insert_of_notMem hn, Nat.cast_add, Nat.cast_one]
    have hv' : (D.card : ℝ) + 1 ≤ v := by exact_mod_cast hvbig
    have invle : (v : ℝ)⁻¹ * (D.card + 1 : ℝ) ≤ 1 := by
      rw [← div_eq_inv_mul]
      exact (div_le_one (by exact_mod_cast hvpos)).mpr hv'
    have bound := mul_le_mul_of_nonneg_left (ih (fun a ha ↦ h a (mem_insert_of_mem ha)))
      (show 0 ≤ 1 + (v : ℝ)⁻¹ by positivity)
    nlinarith

private lemma reciprocal_moment (D : Finset ℕ) (h : ∀ v ∈ D, 0 < v) (r : ℕ) :
    (∑ E ∈ D.powersetCard r, (∏ v ∈ E, (v : ℝ)⁻¹)) ≤
      ((D.card : ℝ) + 1)^2 / (2:ℝ)^r := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [sum_mul]
  calc
    _ = ∑ E ∈ D.powersetCard r, ∏ v ∈ E, (2 * (v:ℝ)⁻¹) := by
      apply sum_congr rfl
      intro E hE
      simp only [prod_mul_distrib, prod_const, (mem_powersetCard.mp hE).2, mul_comm]
    _ ≤ ∑ E ∈ D.powerset, ∏ v ∈ E, (2 * (v:ℝ)⁻¹) :=
      sum_le_sum_of_subset_of_nonneg
        (fun E hE ↦ mem_powerset.mpr (mem_powersetCard.mp hE).1) (by intros; positivity)
    _ = ∏ v ∈ D, (1 + 2 * (v:ℝ)⁻¹) := (prod_one_add D).symm
    _ ≤ ∏ v ∈ D, (1 + (v:ℝ)⁻¹)^2 := by
      apply prod_le_prod₀ (by intros; positivity)
      intro v _
      nlinarith [sq_nonneg (v:ℝ)⁻¹]
    _ ≤ _ := by
      rw [Finset.prod_pow]
      exact pow_le_pow_left₀ (by positivity) (reciprocal_product D h) _

private lemma moment_bound (x M d : ℕ) (D : Finset ℕ) (h : ∀ v ∈ D, 0 < v) (r : ℕ) :
    moment x M d D r ≤ ((M / d : ℕ) : ℝ) * ((D.card : ℝ) + 1)^2 / (2:ℝ)^r + D.card.choose r := by
  have one (E : Finset ℕ) : rawCount x M (d * ∏ v ∈ E, v) ≤
      ((M/d : ℕ):ℝ) * (∏ v ∈ E, (v:ℝ)⁻¹) + 1 := by
    have hbound := (raw_bounds x M (d * ∏ v ∈ E, v)).2
    rw [← Nat.div_div_eq_div_mul] at hbound
    refine hbound.trans (add_le_add_left ((Nat.cast_div_le (α := ℝ)).trans_eq ?_) 1)
    simp [div_eq_mul_inv]
  have hle := sum_le_sum fun E (_ : E ∈ D.powersetCard r) ↦ one E
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one, card_powersetCard] at hle
  apply hle.trans
  rw [mul_div_assoc]
  exact add_le_add_left (mul_le_mul_of_nonneg_left (reciprocal_moment D h r) (by positivity)) _

/-- Compare two length-`M` windows after excluding pairwise coprime factors.
The truncation order is arbitrary. Each excluded intersection contributes
one floor error, and the reciprocal sum of the omitted intersections
decreases geometrically with the order. -/
theorem siftCount_discrepancy (x M d : ℕ) (hd : 0 < d) (D : Finset ℕ)
    (hc : (D : Set ℕ).Pairwise Nat.Coprime) (hpos : ∀ v ∈ D, 0 < v) (r : ℕ) :
    |siftCount x M d D - siftCount 0 M d D| ≤
      2 * (((M / d : ℕ) : ℝ) * ((D.card:ℝ)+1)^2 / (2:ℝ)^r + D.card.choose r) +
        ∑ j ∈ range r, (D.card.choose j : ℝ) := by
  let P (y : ℕ) := ∑ j ∈ range r, (-1 : ℝ)^j * moment y M d D j
  have err (y) : |siftCount y M d D - P y| ≤
      ((M / d : ℕ) : ℝ) * ((D.card:ℝ)+1)^2 / (2:ℝ)^r + D.card.choose r :=
    (bonferroni y M d hd D hc r).trans (moment_bound y M d D hpos r)
  have changeP : |P x - P 0| ≤ ∑ j ∈ range r, (D.card.choose j : ℝ) := by
    dsimp [P]
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
    simpa [← mul_sub, abs_mul] using moment_discrepancy x M d D j
  calc
    _ ≤ |siftCount x M d D - P x| + |P x - P 0| + |P 0 - siftCount 0 M d D| :=
      (abs_sub_le _ (P 0) _).trans (add_le_add_left (abs_sub_le _ (P x) _) _)
    _ ≤ _ := by rw [abs_sub_comm (P 0)]; linarith [err x, err 0]

private lemma crude_discrepancy (x M d : ℕ) (D : Finset ℕ) :
    |siftCount x M d D - siftCount 0 M d D| ≤ ((M/d : ℕ) : ℝ) + 1 := by
  have h (y) : 0 ≤ siftCount y M d D ∧ siftCount y M d D ≤ ((M/d : ℕ) : ℝ) + 1 := by
    constructor
    · unfold siftCount
      exact sum_nonneg fun _ _ ↦ by split <;> norm_num
    · apply le_trans _ (raw_bounds y M d).2
      unfold siftCount rawCount
      rw [← sum_boole]
      apply sum_le_sum
      intro b _
      split_ifs <;> simp_all
  obtain ⟨h₁, h₂⟩ := h x
  obtain ⟨h₃, h₄⟩ := h 0
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma harmonic_tail (L m : ℕ) (g : ℕ → ℝ) (C : ℝ) (hL : 0 < L)
    (hn : ∀ e, 0 ≤ g e)
    (hb : ∀ j < m, ∑ e ∈ Icc 1 (L/2^j), g e ≤ C * ((L:ℝ)/2^j)) :
    ∑ e ∈ Ioc (L/2^m) L, g e / e ≤ 2 * C * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    let a := L/2^(m+1)
    let b := L/2^m
    have hab : a ≤ b := Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) (by omega))
      (by positivity)
    have hbL : b ≤ L := Nat.div_le_self ..
    rw [← Finset.sum_Ioc_consecutive _ hab hbL]
    have hsum : ∑ e ∈ Ioc a b, g e ≤ ∑ e ∈ Icc 1 b, g e :=
      sum_le_sum_of_subset_of_nonneg (fun e he ↦ by
        obtain ⟨hl, hr⟩ := mem_Ioc.mp he
        exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt hl, hr⟩) (fun e _ _ ↦ hn e)
    have step : ∑ e ∈ Ioc a b, g e/e ≤ 2*C := by
      calc
        _ ≤ ∑ e ∈ Ioc a b, g e * ((2:ℝ)^(m+1)/L) := by
          apply sum_le_sum
          intro e he
          have hgt := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(m+1))).mp (mem_Ioc.mp he).1
          have he' : (0:ℝ) < e := by exact_mod_cast (show 0 < e from (Nat.zero_le _).trans_lt (mem_Ioc.mp he).1)
          rw [div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_left _ (hn e)
          apply (le_div_iff₀ (by exact_mod_cast hL)).mpr
          rw [mul_comm, ← div_eq_mul_inv]
          apply (div_le_iff₀ he').mpr
          exact_mod_cast (show L ≤ 2^(m+1)*e by simpa [Nat.mul_comm] using hgt.le)
        _ = (∑ e ∈ Ioc a b, g e) * ((2:ℝ)^(m+1)/L) := (sum_mul ..).symm
        _ ≤ (C*((L:ℝ)/2^m)) * ((2:ℝ)^(m+1)/L) :=
          mul_le_mul_of_nonneg_right (hsum.trans (hb m (by omega))) (by positivity)
        _ = _ := by rw [pow_succ]; field_simp
    have prev := ih fun j hj ↦ hb j (by omega)
    push_cast
    dsimp [a,b] at step
    linarith

private lemma subset_bound (J r : ℕ) :
    2*(J.choose r : ℝ) + ∑ j ∈ range r, (J.choose j : ℝ) ≤
      (r+2 : ℝ) * ((J+1:ℕ):ℝ)^r := by
  have hj (j : ℕ) (hjr : j ≤ r) : (J.choose j : ℝ) ≤ ((J+1:ℕ):ℝ)^r := by
    exact_mod_cast (Nat.choose_le_pow J j).trans ((Nat.pow_le_pow_left (by omega : J ≤ J+1) j).trans
      (Nat.pow_le_pow_right (by omega : 0 < J+1) hjr))
  have z := sum_le_sum fun j (hj' : j ∈ range r) ↦ hj j (mem_range.mp hj').le
  simp only [sum_const, card_range, nsmul_eq_mul] at z
  linarith [hj r le_rfl]

/-- A finite form of the arithmetic transfer. Use `m` dyadic intervals for
the large secondary divisors and `r` terms of inclusion and exclusion for
the small ones. -/
theorem siftSum_bound (x M d : ℕ) (hd : 0 < d) (D : Finset ℕ)
    (hc : (D : Set ℕ).Pairwise Nat.Coprime) (hpos : ∀ v ∈ D, 0 < v)
    (c g : ℕ → ℝ) (L m r : ℕ) (hl : L = M/d) (hL : 0 < L)
    (hn : ∀ e, 0 ≤ g e) (hcoef : ∀ e ∈ Icc 1 L, |c e| ≤ g e)
    (H C : ℝ) (harm : ∑ e ∈ Icc 1 L, g e / e ≤ H)
    (hb : ∀ j < m, ∑ e ∈ Icc 1 (L/2^j), g e ≤ C*((L:ℝ)/2^j)) :
    |siftSum x M d D c - siftSum 0 M d D c| ≤
      L * ((2*((D.card:ℝ)+1)^2/(2:ℝ)^r +
        (r+2:ℝ)*((D.card:ℝ)+1)^r/(2:ℝ)^m)*H + 4*C*m) := by
  let U : ℝ := 2*((D.card:ℝ)+1)^2/(2:ℝ)^r +
        (r+2:ℝ)*((D.card:ℝ)+1)^r/(2:ℝ)^m
  let Δ (e : ℕ) := siftCount x M (d*e) D - siftCount 0 M (d*e) D
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hdiv (e : ℕ) : M/(d*e) = L/e := by rw [← Nat.div_div_eq_div_mul, hl]
  have lo (e : ℕ) (he : e ∈ Icc 1 (L/2^m)) : |Δ e| ≤ (L:ℝ)/e * U := by
    obtain ⟨hep, hec⟩ := mem_Icc.mp he
    have h := siftCount_discrepancy x M (d*e) (Nat.mul_pos hd hep) D hc hpos r
    rw [hdiv] at h
    have he' : 0 < (e:ℝ) := by exact_mod_cast hep
    have hscale : (2:ℝ)^m ≤ (L:ℝ)/e := by
      apply (le_div_iff₀ he').mpr
      exact_mod_cast (show 2^m*e ≤ L by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by positivity : 0 < 2^m)).mp hec)
    have a := Nat.cast_div_le (α := ℝ) (m := L) (n := e)
    have b := subset_bound D.card r
    push_cast at b
    have small : (r+2:ℝ)*((D.card:ℝ)+1)^r ≤
        (L:ℝ)/e * ((r+2)*((D.card:ℝ)+1)^r/(2:ℝ)^m) := by
      calc
        _ = (2:ℝ)^m * ((r+2)*((D.card:ℝ)+1)^r/(2:ℝ)^m) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)
    have first := mul_le_mul_of_nonneg_right a (show 0 ≤ 2*((D.card:ℝ)+1)^2/(2:ℝ)^r by positivity)
    dsimp [U, Δ]
    linear_combination (norm := ring_nf) h + b + small + first
    exact le_rfl
  have hi (e : ℕ) (he : e ∈ Icc 1 L) : |Δ e| ≤ 2*((L:ℝ)/e) := by
    obtain ⟨hep, heL⟩ := mem_Icc.mp he
    have er : (0:ℝ) < e := by exact_mod_cast hep
    have he' : 1 ≤ (L:ℝ)/e := (one_le_div er).mpr (by exact_mod_cast heL)
    have hc' := crude_discrepancy x M (d*e) D
    rw [hdiv] at hc'
    dsimp [Δ]
    linarith [Nat.cast_div_le (α := ℝ) (m := L) (n := e)]
  have split : Icc 1 L = Icc 1 (L/2^m) ∪ Ioc (L/2^m) L := by
    ext e
    have hz := Nat.div_le_self L (2^m)
    have hzero := Nat.zero_le (L/2^m)
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have disj : Disjoint (Icc 1 (L/2^m)) (Ioc (L/2^m) L) :=
    disjoint_left.mpr fun _ h₁ h₂ ↦ (mem_Ioc.mp h₂).1.not_ge (mem_Icc.mp h₁).2
  have hsub : Icc 1 (L/2^m) ⊆ Icc 1 L := Icc_subset_Icc_right (Nat.div_le_self ..)
  have hsub' : Ioc (L/2^m) L ⊆ Icc 1 L := fun _ he ↦
    mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp he).1, (mem_Ioc.mp he).2⟩
  have lhs : |siftSum x M d D c - siftSum 0 M d D c| ≤ ∑ e ∈ Icc 1 L, g e * |Δ e| := by
    unfold siftSum
    rw [← hl, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro e he
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (hcoef e he) (abs_nonneg _)
  rw [split, sum_union disj] at lhs
  have left : ∑ e ∈ Icc 1 (L/2^m), g e * |Δ e| ≤ (L * U) * H := by
    calc
      _ ≤ ∑ e ∈ Icc 1 (L/2^m), (L*U)*(g e/e) := by
        apply sum_le_sum
        intro e he
        apply (mul_le_mul_of_nonneg_left (lo e he) (hn e)).trans_eq
        ring
      _ = (L*U)*∑ e ∈ Icc 1 (L/2^m), g e/e := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ div_nonneg (hn e) (Nat.cast_nonneg _))).trans harm)
        (by positivity)
  have right : ∑ e ∈ Ioc (L/2^m) L, g e * |Δ e| ≤ (2*L)*(2*C*m) := by
    calc
      _ ≤ ∑ e ∈ Ioc (L/2^m) L, (2*L)*(g e/e) := by
        apply sum_le_sum
        intro e he
        apply (mul_le_mul_of_nonneg_left (hi e (hsub' he)) (hn e)).trans_eq
        ring
      _ = (2*L)*∑ e ∈ Ioc (L/2^m) L, g e/e := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_tail L m g C hL hn hb) (by positivity)
  change _ ≤ L*(U*H+4*C*m)
  linarith only [lhs, left, right]

private lemma truncation_parameters {A : ℝ} {t J : ℕ}
    (ht : 1 ≤ t) (hA : 1 ≤ A) (hp : A ≤ (2:ℝ)^t) (hJ : (J:ℝ) ≤ A^2+2) :
    2*((J:ℝ)+1)^2/(2:ℝ)^(16*t) +
      (16*t+2:ℝ)*((J:ℝ)+1)^(16*t)/(2:ℝ)^(100*t^2) ≤ 2/A^3 := by
  have h2 : (2:ℝ) ≤ 2^t := by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) ht
  have hA3 : A^3 ≤ (2:ℝ)^(3*t) := by
    rw [Nat.mul_comm 3, pow_mul]
    exact pow_le_pow_left₀ (by linarith) hp _
  have hJ' : (J:ℝ)+1 ≤ (2:ℝ)^(3*t) := by
    rw [Nat.mul_comm 3, pow_mul]
    nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ A) hp 2,
      mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg ((2:ℝ)^t))]
  have bound₁ : 2*((J:ℝ)+1)^2*A^3 ≤ (2:ℝ)^(16*t) := by
    calc
      _ ≤ 2*((2:ℝ)^(3*t))^2*2^(3*t) := by gcongr
      _ = (2:ℝ)^(1+3*t*2+3*t) := by conv_rhs => rw [pow_add, pow_add, pow_mul (2:ℝ) (3*t) 2, pow_one]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have small : (16*t+2:ℝ) ≤ (2:ℝ)^(16*t+2) := by
    have hh : 16*t+2 < 2^(16*t+2) := Nat.lt_pow_self (by decide)
    exact_mod_cast hh.le
  have bound₂ : (16*t+2:ℝ)*((J:ℝ)+1)^(16*t)*A^3 ≤ (2:ℝ)^(100*t^2) := by
    calc
      _ ≤ (2:ℝ)^(16*t+2)*(2^(3*t))^(16*t)*2^(3*t) := by gcongr
      _ = (2:ℝ)^(16*t+2+(3*t)*(16*t)+3*t) := by conv_rhs => rw [pow_add, pow_add, pow_mul (2:ℝ) (3*t) (16*t)]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.mul_le_mul_right t ht])
  have hpos : 0 < A^3 := by positivity
  apply (le_div_iff₀ hpos).mpr
  rw [add_mul]
  have first : 2*((J:ℝ)+1)^2/(2:ℝ)^(16*t)*A^3 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    exact bound₁
  have second : (16*t+2:ℝ)*((J:ℝ)+1)^(16*t)/(2:ℝ)^(100*t^2)*A^3 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    exact bound₂
  linarith

open Filter Real Asymptotics

private lemma dyadic_range {L m j : ℕ} (hL : 2 ≤ L) (hj : j < m)
    (hm : (m:ℝ) ≤ Real.log L / 2) :
    2 ≤ L/2^j ∧ Real.log L / 2 ≤ Real.log (L/2^j : ℕ) := by
  have hx : (0:ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have ht : (j+1:ℝ)*Real.log 2 ≤ Real.log L/2 := by
    have le' : (j+1:ℝ) ≤ m := by exact_mod_cast hj
    have hl : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith only [le', hm, mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (j+1:ℝ))]
  have hpow : (2:ℝ)^(j+1) ≤ L := by
    apply (Real.log_le_log_iff (by positivity) hx).mp
    rw [Real.log_pow]; push_cast; linarith [Real.log_nonneg (show (1 : ℝ) ≤ L by exact_mod_cast (by omega : 1 ≤ L))]
  have htwo : 2 ≤ L/2^j := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    exact_mod_cast (show 2*(2:ℝ)^j ≤ L by simpa [pow_succ, mul_comm] using hpow)
  refine ⟨htwo, ?_⟩
  have hlim : (L:ℝ) ≤ (2:ℝ)^(j+1) * (L/2^j : ℕ) := by
    exact_mod_cast (show L ≤ 2^(j+1)*(L/2^j) by
      have hbound := Nat.lt_mul_div_succ L (by positivity : 0 < 2^j)
      rw [pow_succ]
      nlinarith [Nat.mul_le_mul_left (2^j) htwo])
  have logle := Real.log_le_log hx hlim
  rw [Real.log_mul (by positivity) (by exact_mod_cast (by omega : L/2^j ≠ 0)), Real.log_pow] at logle
  push_cast at logle
  linarith

private lemma choose_level {ν : ℝ} (hν : 0 < ν) (hν' : ν ≤ 1/2) :
    ∀ᶠ A : ℝ in atTop, 4 ≤ A ∧ A^ν ≤ A/2 ∧
      (∀ y : ℝ, 0 < y → y ≤ A^2+5 → 1+Real.log y ≤ A^ν) ∧
      ∃ t : ℕ, 1 ≤ t ∧ A ≤ (2:ℝ)^t ∧ (100*t^2:ℝ) ≤ A^ν := by
  have logs := (isLittleO_log_rpow_atTop (half_pos hν)).bound (c := 1/100) (by norm_num)
  filter_upwards [eventually_ge_atTop (10:ℝ), logs] with A hA hlog
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have log2 : 1/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogA : 1 ≤ Real.log A := by
    have he := Real.log_le_log (by norm_num : (0:ℝ)<2^2) (by linarith : (2:ℝ)^2 ≤ A)
    rw [Real.log_pow] at he
    norm_num at he
    linarith
  have hsmall : Real.log A ≤ (1/100)*A^(ν/2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log A),
      abs_of_nonneg (Real.rpow_nonneg hA0.le _)] using hlog
  have sq : (A^(ν/2))^2 = A^ν := by
    rw [← Real.rpow_mul_natCast hA0.le]; congr 1; push_cast; ring
  have halfsq : (A^(1/2:ℝ))^2 = A := by
    rw [← Real.rpow_mul_natCast hA0.le]; norm_num
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · apply (Real.rpow_le_rpow_of_exponent_le hA1 hν').trans
    nlinarith [sq_nonneg (A^(1/2:ℝ)-2)]
  · intro y hy hY
    have hcap : y ≤ A^3 := by
      nlinarith [mul_nonneg (sq_nonneg A) (show 0 ≤ A-2 by linarith)]
    have hl := Real.log_le_log hy hcap
    rw [Real.log_pow] at hl
    have powle := Real.rpow_le_rpow_of_exponent_le hA1 (by linarith : ν/2 ≤ ν)
    push_cast at hl
    linarith
  · let t := ⌈Real.logb 2 A⌉₊
    have hz : 0 ≤ Real.logb 2 A := div_nonneg (by linarith) (by linarith)
    have he : A ≤ (2:ℝ)^t := by
      rw [← Real.rpow_natCast]
      exact (Real.logb_le_iff_le_rpow (by norm_num) hA0).mp (Nat.le_ceil _)
    have htp : 1 ≤ t := by
      by_contra! h
      rw [show t = 0 by omega, pow_zero] at he
      linarith
    have hceil := Nat.ceil_lt_add_one hz
    have ratio : Real.logb 2 A ≤ 2*Real.log A := by
      apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
      nlinarith [mul_le_mul_of_nonneg_right log2.le (by linarith : 0 ≤ Real.log A)]
    have ht : (t:ℝ) ≤ 3*Real.log A := by dsimp [t]; linarith
    refine ⟨t, htp, he, ?_⟩
    nlinarith only [sq, pow_le_pow_left₀ (Nat.cast_nonneg t) (ht.trans
      (mul_le_mul_of_nonneg_left hsmall (by norm_num))) 2, sq_nonneg (A^(ν/2))]

/-- A uniform absolute discrepancy for any coefficients bounded by the
squarefree sieve weights. The loss exponent `ν` can be arbitrarily small. -/
theorem siftSum_absolute {s ν : ℝ} (hs : 0 < s) (hs' : s ≤ 1)
    (hν : 0 < ν) (hν' : ν ≤ 1/2) : ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℕ, ∀ (x M d : ℕ)
    (D : Finset ℕ) (c : ℕ → ℝ), 0 < d → L₀ ≤ M/d → (D : Set ℕ).Pairwise Nat.Coprime →
    (∀ v ∈ D, 0 < v) → (D.card:ℝ) ≤ (Real.log (M/d:ℕ))^2+2 →
    (∀ e ∈ Icc 1 (M/d), |c e| ≤ omegaWeight s e) →
    |siftSum x M d D c - siftSum 0 M d D c| ≤
      C*(M/d:ℕ)*(Real.log (M/d:ℕ))^(s-1+ν) := by
  obtain ⟨C₁,hC₁,harm⟩ := omega_harmonic hs hs'
  obtain ⟨C₂,hC₂,hmean⟩ := omega_count hs hs'
  let B := C₂ / (2:ℝ)^(s-1)
  have hB : 0 < B := by dsimp [B]; positivity
  let C := 2*C₁+4*B
  have hC : 0 < C := by dsimp [C]; positivity
  have hlevels := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (choose_level hν hν')
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlevels
  refine ⟨C,hC,max N 2,?_⟩
  intro x M d D c hd hL hcop hpos hc hcoef
  let L := M/d
  let A := Real.log L
  have hNL : N ≤ L := (le_max_left ..).trans hL
  have h2 : 2 ≤ L := (le_max_right ..).trans hL
  obtain ⟨hA, hp, _, t, ht, hpow, hts⟩ := hN L hNL
  change 4 ≤ A at hA
  change A^ν ≤ A/2 at hp
  change A ≤ (2:ℝ)^t at hpow
  change (100*t^2:ℝ) ≤ A^ν at hts
  have hA0 : 0 < A := by linarith
  let m := 100*t^2
  let r := 16*t
  have hm : (m:ℝ) ≤ A^ν := by exact_mod_cast hts
  have hlog : ∀ j < m, ∑ e ∈ Icc 1 (L/2^j), omegaWeight s e ≤
      (B*A^(s-1))*((L:ℝ)/2^j) := by
    intro j hj
    obtain ⟨hsize,hlo⟩ := dyadic_range h2 hj (hm.trans hp)
    have mu := hmean (L/2^j) hsize
    have hx := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < A/2) hlo (by linarith : s-1 ≤ 0)
    rw [Real.div_rpow hA0.le (by norm_num)] at hx
    have hfloor : ((L/2^j:ℕ):ℝ) ≤ (L:ℝ)/2^j := by exact_mod_cast (Nat.cast_div_le (α := ℝ)
      (m := L) (n := 2^j))
    calc
      _ ≤ _ := mu
      _ ≤ C₂*((L:ℝ)/2^j)*(A^(s-1)/(2:ℝ)^(s-1)) := by gcongr
      _ = _ := by dsimp [B]; ring
  have bound := siftSum_bound x M d hd D hcop hpos c (omegaWeight s) L m r rfl (by omega)
    (fun e ↦ by unfold omegaWeight; positivity) hcoef _ _ (harm L h2) hlog
  have tr : 2*((D.card:ℝ)+1)^2/(2:ℝ)^r +
      (r+2:ℝ)*((D.card:ℝ)+1)^r/(2:ℝ)^m ≤ 2/A^3 := by
    simpa [m,r] using truncation_parameters ht (by linarith : 1 ≤ A) hpow hc
  have t₁ : (2/A^3)*(C₁*A^s) ≤ 2*C₁*A^(s-1+ν) := by
    have hlo := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ A) (by linarith : s-3 ≤ s-1+ν)
    have heq : A^(s-3:ℝ) = A^s/A^3 := by rw [Real.rpow_sub hA0]; norm_num
    rw [heq] at hlo
    calc
      _ = (2*C₁)*(A^s/A^3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  have t₂ : 4*(B*A^(s-1))*m ≤ 4*B*A^(s-1+ν) := by
    rw [Real.rpow_add hA0]
    grw [hm]; ring_nf; exact le_rfl
  apply bound.trans
  change L * (_*(C₁*A^s)+4*(B*A^(s-1))*m) ≤ C*L*A^(s-1+ν)
  have term := (mul_le_mul_of_nonneg_right tr (show 0 ≤ C₁*A^s by positivity)).trans t₁
  have both := mul_le_mul_of_nonneg_left (add_le_add term t₂) (Nat.cast_nonneg L)
  dsimp [C]
  linear_combination (norm := ring_nf) both
  exact le_rfl

/-- A single quotient threshold controls every translated interval, forbidden-factor
set, coefficient sequence, and comparison weight in the stated range. -/
theorem siftSum_relative {s δ : ℝ} (hs : 0 < s) (hs' : s < 1/2) (hδ : 0 < δ) :
    ∃ L₀ : ℕ, ∀ (x M d : ℕ) (D : Finset ℕ) (c G : ℕ → ℝ) (F : Finset ℕ),
    0 < d → L₀ ≤ M/d → (D : Set ℕ).Pairwise Nat.Coprime → (∀ v ∈ D, 0 < v) →
    (D.card : ℝ) ≤ (Real.log (M/d:ℕ))^2+2 → (F.card : ℝ) ≤ (Real.log (M/d:ℕ))^2+2 →
    MeanWeight G → (∀ p ∈ Nat.primesLE (M/d), p ∉ F → 1-s ≤ G p) →
    (∀ e ∈ Icc 1 (M/d), |c e| ≤ omegaWeight s e) →
    |siftSum x M d D c - siftSum 0 M d D c| ≤ δ*meanSum G (M/d) := by
  let ν := (1-2*s)/4
  have hν : 0 < ν := by dsimp [ν]; linarith
  have hν' : ν ≤ 1/2 := by dsimp [ν]; linarith
  have hu : 0 < 1-s := by linarith
  obtain ⟨C,hC,N₁,absolute⟩ := siftSum_absolute hs (by linarith) hν hν'
  obtain ⟨b,hb,N₂,hm⟩ := mean_lower hu
  obtain ⟨a,ha,hp⟩ := product_lower hu (by linarith)
  have hgap : 0 < 1-2*s-2*ν := by dsimp [ν]; linarith
  have small := (tendsto_order.mp (tendsto_rpow_neg_atTop hgap)).2
    (δ*b*a/C) (by positivity)
  have eventual := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    ((choose_level hν hν').and small)
  obtain ⟨N₃,hN⟩ := eventually_atTop.mp eventual
  refine ⟨max N₁ (max N₂ N₃),?_⟩
  intro x M d D c G F hd hL hcop hpos hD hF hG hfree hcoef
  let L := M/d
  let A := Real.log L
  have h₁ : N₁ ≤ L := (le_max_left ..).trans hL
  have h₂ : N₂ ≤ L := (le_max_left ..).trans ((le_max_right ..).trans hL)
  have h₃ : N₃ ≤ L := (le_max_right ..).trans ((le_max_right ..).trans hL)
  obtain ⟨⟨hA, _, hlog, _⟩,hst⟩ := hN L h₃
  change 4 ≤ A at hA
  change A^(-(1-2*s-2*ν)) < δ*b*a/C at hst
  have hA0 : 0 < A := by linarith
  have denom : 0 < 1+Real.log (F.card+3:ℕ) := by
    have h := Real.log_natCast_nonneg (F.card+3)
    linarith
  have denle : 1+Real.log (F.card+3:ℕ) ≤ A^ν := by
    apply hlog _ (by positivity)
    push_cast
    change (F.card:ℝ) ≤ A^2+2 at hF
    change (F.card:ℝ)+3 ≤ A^2+5
    linarith
  have low : b*a*L*A^(-s-ν) ≤ meanSum G L := by
    have he : A^(-s-ν) = A^(1-s)/A^ν/A := by
      rw [show -s-ν = (1-s-ν)-1 by ring, Real.rpow_sub hA0, Real.rpow_one, Real.rpow_sub hA0]
    calc
      _ = b*L*(a*A^(1-s)/A^ν)/A := by rw [he]; ring
      _ ≤ b*L*(a*A^(1-s)/(1+Real.log (F.card+3:ℕ)))/A := by gcongr
      _ ≤ b*L*meanProduct G L/A := by gcongr; exact hp L F G hG hfree
      _ ≤ _ := hm L h₂ F G hG hF hfree
  apply (absolute x M d D c hd h₁ hcop hpos hD hcoef).trans
  have hz : C*A^(-(1-2*s-2*ν)) ≤ δ*b*a := by
    simpa [mul_comm] using (lt_div_iff₀ hC).mp hst |>.le
  have he : A^(s-1+ν) = A^(-(1-2*s-2*ν))*A^(-s-ν) := by
    rw [← Real.rpow_add hA0]; congr 1; ring
  change C*L*A^(s-1+ν) ≤ δ*meanSum G L
  calc
    _ = (C*A^(-(1-2*s-2*ν)))*(L*A^(-s-ν)) := by rw [he]; ring
    _ ≤ (δ*b*a)*(L*A^(-s-ν)) := mul_le_mul_of_nonneg_right hz (by positivity)
    _ = δ*(b*a*L*A^(-s-ν)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left low hδ.le

end ErdosSuranyi708
