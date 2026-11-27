module

public import conjectures.ErdosSuranyi708.SeedIndex
public import conjectures.ErdosSuranyi708.Envelope
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708
open Finset Filter

private theorem log_sum {n M : ℕ} (hM : M ≤ (2*n)^3) {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, Nat.log p M ≤ (Nat.nthRoot 4 n + 1) * (15+12*Nat.nthRoot 4 n) + 15*P.card := by
  let R := Nat.nthRoot 4 n
  have hR : n < (R+1)^4 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hdl : M ≤ 2 ^ (15 + 12*R) := by
    have hd : R+1 ≤ 2^(R+1) := Nat.le_of_lt (Nat.lt_two_pow_self)
    calc
      M ≤ (2 * (R+1)^4)^3 := hM.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hR.le) _)
      _ ≤ (2 * (2^(R+1))^4)^3 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _)) _
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
  have hl (p : ℕ) (h : p ∈ P) : Nat.log p M ≤ 15+12*R :=
    (Nat.log_anti_left (by decide) (hp p h).two_le).trans
      ((Nat.log_mono_right hdl).trans_eq (Nat.log_pow (by decide) _))
  have hr (p : ℕ) (h : p ∈ P) (hlt : R < p) : Nat.log p M ≤ 15 := by
    have hpow : n < p^4 := hR.trans_le (Nat.pow_le_pow_left hlt _)
    have hlarge : 2*n < p^5 := by
      calc
        _ < 2 * p^4 := Nat.mul_lt_mul_of_pos_left hpow (by decide)
        _ ≤ p * p^4 := Nat.mul_le_mul_right _ (hp p h).two_le
        _ = _ := by ring
    have h15 : M < p^15 := by
      calc
        _ ≤ (2*n)^3 := hM
        _ < (p^5)^3 := Nat.pow_lt_pow_left hlarge (by decide)
        _ = _ := by ring
    exact (Nat.log_lt_of_lt_pow' (by decide : 15 ≠ 0) h15).le
  have hadd := sum_filter_add_sum_filter_not P (fun p ↦ p ≤ R) (fun p ↦ Nat.log p M)
  rw [← hadd]
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ _ ∈ P.filter (· ≤ R), (15+12*R) :=
        sum_le_sum fun p h ↦ hl p (mem_filter.mp h).1
      _ = (P.filter (· ≤ R)).card * (15+12*R) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by
        rw [← card_range (R+1)]
        exact card_le_card fun p h ↦ mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp h).2))
  · calc
      _ ≤ ∑ _ ∈ P.filter (fun p ↦ ¬p≤R), 15 := sum_le_sum fun p h ↦
        hr p (mem_filter.mp h).1 (lt_of_not_ge (mem_filter.mp h).2)
      _ = 15 * (P.filter (fun p ↦ ¬p≤R)).card := by simp [mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ (card_filter_le ..)

/-- The total number of possible top-prime exponents is sublinear in the input size. -/
theorem few_top_exponents (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, ∀ M ≤ (2*n)^3,
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p ≤ 5*n) →
    ((∑ p ∈ P, Nat.log p M : ℕ) : ℝ) ≤ ε * n := by
  obtain ⟨Q,hQ⟩ := exists_nat_ge (108 / ε)
  filter_upwards [few_labels (ε / 30) (by positivity), eventually_ge_atTop ((Q+1)^4)] with n hp hn
  intro M hM P hP
  have hs : P ⊆ (5*n).primesLE := fun p h ↦ Nat.mem_primesLE.mpr ⟨(hP p h).2,(hP p h).1⟩
  have hpi := (Nat.cast_le.mpr (card_le_card hs) : (P.card : ℝ) ≤ _).trans hp
  have hb := Nat.cast_le (α := ℝ) |>.mpr (log_sum hM (fun p h ↦ (hP p h).1))
  let R := Nat.nthRoot 4 n
  have hr : Q+1 ≤ R := (Nat.le_nthRoot_iff (by decide : 4≠0)).mpr hn
  have h1 : 1 ≤ R := by omega
  have hre : R^4 ≤ n := Nat.pow_nthRoot_le (.inl (by decide))
  change (108 : ℝ) / ε ≤ Q at hQ
  have hεR : 108 ≤ ε * R := (div_le_iff₀ hε).mp (hQ.trans (Nat.cast_le.mpr (by omega : Q ≤ R))) |>.trans_eq (mul_comm ..)
  have hr' : (R : ℝ)^4 ≤ n := by exact_mod_cast hre
  have h1' : (1 : ℝ) ≤ R := Nat.one_le_cast.mpr h1
  change ((∑ p ∈ P, Nat.log p M : ℕ) : ℝ) ≤ _ at hb
  push_cast at hb
  change ((∑ p ∈ P, Nat.log p M : ℕ) : ℝ) ≤ _
  push_cast
  change (∑ p ∈ P, (Nat.log p M : ℝ)) ≤ ((R : ℝ)+1)*(15+12*R)+15*P.card at hb
  have hsquare : (R : ℝ)^2 ≤ (R : ℝ)^3 := by nlinarith [mul_nonneg (sq_nonneg (R:ℝ)) (sub_nonneg.mpr h1')]
  have hl : 108 * (R:ℝ)^3 ≤ ε * n := calc
    _ ≤ (ε * R) * (R:ℝ)^3 := mul_le_mul_of_nonneg_right hεR (by positivity)
    _ = ε * (R:ℝ)^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr' hε.le
  nlinarith [mul_nonneg (sub_nonneg.mpr h1') (by positivity : 0 ≤ 15*(R:ℝ)+15)]

private lemma earlier_card (P : Finset ℕ) (q : ℕ) : (earlier P q).card ≤ q := by
  calc
    _ ≤ (range q).card := card_le_card fun p hp ↦ mem_range.mpr (mem_filter.mp hp).2
    _ = q := card_range _

private theorem small_assignment_count {P : Finset ℕ} {C : ℕ → Finset ℕ} {Y K : ℕ}
    (hC : ∀ p ∈ P, p ≤ Y → (C p).card ≤ K+1) (p : P) (q : earlier P p.val)
    (hq : q.val ≤ Y) (V : (earlier P q.val).powerset) :
    Fintype.card (Assignment C (requiredLabels p.val q.val V.val)) ≤
      (C p).card * (K+1)^(Y+1) := by
  let U := insert q.val V.val
  have hV := mem_powerset.mp V.property
  have hpq := (mem_filter.mp q.property).2
  have hpU : p.val ∉ U := by
    intro h
    rcases mem_insert.mp h with h|h
    · omega
    · exact ((mem_filter.mp (hV h)).2.trans hpq).false
  have hc : U.card ≤ Y+1 :=
    (card_insert_le ..).trans (Nat.add_le_add_right ((card_le_card hV).trans ((earlier_card ..).trans hq)) _)
  rw [Fintype.card_pi]
  simp only [Fintype.card_coe]
  rw [prod_coe_sort _ (fun r ↦ (C r).card)]
  change (∏ r ∈ insert p.val U, (C r).card) ≤ _
  rw [prod_insert hpU]
  apply Nat.mul_le_mul_left
  calc
    ∏ r ∈ U, (C r).card ≤ ∏ _ ∈ U, (K+1) := Finset.prod_le_prod fun r hr ↦ by
      rcases mem_insert.mp hr with h|h
      · subst r
        exact hC _ (mem_filter.mp q.property).1 hq
      · exact hC _ (mem_filter.mp (hV h)).1 ((mem_filter.mp (hV h)).2.le.trans hq)
    _ ≤ _ := by simp [Nat.pow_le_pow_right (by omega : 1 ≤ K+1) hc]

/-- For a fixed cutoff and score grid, the small-second-prime terms have
sublinear cardinality. -/
theorem few_small_seeds (Y K : ℕ) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
    ∀ M ≤ (2*n)^3, ∀ (P : Finset ℕ) (w : ℕ → ℝ),
    (∀ p ∈ P, p.Prime ∧ p ≤ 5*n ∧ p ≤ M) → (∀ p ∈ P, 0 ≤ w p) →
    (((univ : Finset (SeedIndex P (grid Y K M w))).filter (fun i ↦ i.second ≤ Y)).card : ℝ) ≤ ε*n := by
  classical
  let c := (Y+1) * 2^Y * (K+1)^(Y+1)
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [few_top_exponents (ε / c) (by positivity)] with n hn
  intro M hM P w hp hw
  let C := grid Y K M w
  have hC := fun p (h : p ∈ P) (h' : p ≤ Y) ↦ grid_card_small (M := M) (K := K) w h' (hw p h)
  let bound (p : ℕ) := (C p).card * (2^Y * (K+1)^(Y+1))
  have grouped (p : P) (q : earlier P p.val) :
      (∑ V : (earlier P q.val).powerset, ∑ _ : Assignment C (requiredLabels p.val q.val V.val),
          if q.val ≤ Y then 1 else 0) ≤ (if q.val ≤ Y then bound p else 0) := by
    split_ifs with hq
    · calc
        _ = ∑ V : (earlier P q.val).powerset, Fintype.card (Assignment C (requiredLabels p.val q.val V.val)) := by simp
        _ ≤ ∑ _ : (earlier P q.val).powerset, (C p).card * (K+1)^(Y+1) :=
          sum_le_sum fun V _ ↦ small_assignment_count hC p q hq V
        _ ≤ bound p := by
          simp only [sum_const,card_univ,Fintype.card_coe,card_powerset,nsmul_eq_mul]
          have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) ((earlier_card P q.val).trans hq)
          dsimp [bound]
          nlinarith [Nat.mul_le_mul_right ((C p).card*(K+1)^(Y+1)) h]
    · simp
  have hqcount (p : P) : (∑ q : earlier P p.val, if q.val ≤ Y then bound p.val else 0) ≤ (Y+1)*bound p := by
    rw [sum_coe_sort _ (fun q ↦ if q ≤ Y then bound p else 0), ← sum_filter, sum_const, nsmul_eq_mul]
    apply Nat.mul_le_mul_right
    rw [← card_range (Y+1)]
    exact card_le_card fun j h ↦ mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp h).2)
  have total : ((univ : Finset (SeedIndex P C)).filter fun i ↦ i.second ≤ Y).card ≤
      c * ∑ p ∈ P, Nat.log p M := by
    rw [card_eq_sum_ones,sum_filter]
    simp only [Fintype.sum_sigma,SeedIndex.second]
    rw [mul_sum, ← sum_coe_sort P (fun p ↦ c * Nat.log p M)]
    apply sum_le_sum
    intro p _
    refine ((sum_le_sum (s := (univ : Finset (earlier P p.val))) (fun q _ ↦ grouped p q)).trans (hqcount p)).trans ?_
    have h := grid_card_large (Y := Y) (K := K) (w := w) (hp p p.property).1.one_lt (hp p p.property).2.2
    calc
      _ = c * (C p).card := by dsimp [bound,c]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ h
  have ht := Nat.cast_le (α := ℝ) |>.mpr total
  rw [Nat.cast_mul] at ht
  apply ht.trans
  have hh := hn M hM P (fun p h ↦ ⟨(hp p h).1,(hp p h).2.1⟩)
  calc
    _ ≤ (c : ℝ) * (ε / c * n) := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
    _ = _ := by field_simp

end ErdosSuranyi708
