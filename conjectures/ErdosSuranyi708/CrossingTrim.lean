module

public import conjectures.ErdosSuranyi708.Crossing
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708

/-- Retain all small second primes and the short predecessor sets at larger primes. -/
def goodSeed (Y M : ℕ) (cost : ℕ → ℕ) (p q : ℕ) (V : Finset ℕ) : Prop :=
  q ≤ Y ∨ (V.card : ℝ) ≤ (Real.log (M / seedDivisor cost p q V : ℕ))^2

noncomputable instance (Y M : ℕ) (cost : ℕ → ℕ) (p q : ℕ) (V : Finset ℕ) :
    Decidable (goodSeed Y M cost p q V) := Classical.propDecidable _

/-- The part of the finite crossing sum used for transfer between intervals. -/
noncomputable def truncatedCrossing (Y M : ℕ) (s : ℝ) (T : Finset ℕ) (cost : ℕ → ℕ)
    (w : ℕ → ℝ) : ℝ := by
  classical
  exact ∑ p ∈ T, ∑ q ∈ earlier T p, ∑ V ∈ (earlier T q).powerset,
    if goodSeed Y M cost p q V then seedValue M s w cost (earlier T q) p q V else 0

lemma truncatedCrossing_le {s : ℝ} (hs : 0 < s) (hu : s ≤ 1) (T : Finset ℕ) (cost : ℕ → ℕ)
    (w : ℕ → ℝ) (Y M : ℕ) (hw : ∀ i ∈ T, 0 ≤ w i ∧ w i ≤ 1) :
    truncatedCrossing Y M s T cost w ≤ hinge (∑ i ∈ T, w i) := by
  classical
  refine le_trans ?_ (crossing_pairs_le hs hu T w hw)
  unfold truncatedCrossing
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro V _
  have ha := (hw p hp).1
  have hb := (hw q (Finset.mem_filter.mp hq).1).1
  split
  · exact seedValue_le hs.le hu _ _ _ _ _ _ _ ha hb
  · exact mul_nonneg (mul_nonneg (pow_nonneg hs.le _) (crossingLength_nonneg ha hb))
      (pow_nonneg (sub_nonneg.mpr hu) _)

lemma truncatedCrossing_nonneg {s : ℝ} (hs : 0 < s) (hh : s < 1/2) {Y M : ℕ}
    {T : Finset ℕ} {w : ℕ → ℝ} {cost : ℕ → ℕ} (hc : ∀ i ∈ T, 1 ≤ i ∧ i ≤ cost i)
    (hf : (∏ r ∈ T, cost r) ≤ M) (hw : ∀ i ∈ T, 0 ≤ w i) :
    0 ≤ truncatedCrossing Y M s T cost w := by
  classical
  unfold truncatedCrossing
  exact Finset.sum_nonneg fun p hp => Finset.sum_nonneg fun q hq => Finset.sum_nonneg fun V hV => by
    split
    · exact seedValue_nonneg hs hh hp hq (Finset.mem_powerset.mp hV) hc hf (hw p hp)
        (hw q (Finset.mem_filter.mp hq).1)
    · rfl

private lemma unused_factors {T : Finset ℕ} {p q M : ℕ} {cost : ℕ → ℕ} {V : Finset ℕ}
    (hp : p ∈ T) (hq : q ∈ earlier T p) (hV : V ⊆ earlier T q)
    (hc : ∀ i ∈ T, 2 ≤ i ∧ i ≤ cost i) (hfit : (∏ r ∈ T, cost r) ≤ M) :
    2^(T.card-(V.card+2)) ≤ M / seedDivisor cost p q V := by
  let B := insert p (insert q V)
  have hqT := (Finset.mem_filter.mp hq).1
  have hqp := (Finset.mem_filter.mp hq).2
  have hVT : V ⊆ T := hV.trans (Finset.filter_subset ..)
  have hBT : B ⊆ T := Finset.insert_subset hp (Finset.insert_subset hqT hVT)
  have hqV : q ∉ V := fun h => (Nat.lt_irrefl q) (Finset.mem_filter.mp (hV h)).2
  have hpV : p ∉ insert q V := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · have := (Finset.mem_filter.mp (hV h)).2
      omega
  have hB : B.card = V.card+2 := by simp [B,hpV,hqV,Nat.add_assoc]
  have modulus : (∏ r ∈ B, cost r) = seedDivisor cost p q V := by
    simp [B,hpV,hqV,seedDivisor,Nat.mul_assoc]
  have pos : 0 < seedDivisor cost p q V := by
    rw [← modulus]
    exact Finset.prod_pos fun i hi => by have := hc i (hBT hi); omega
  apply (Nat.le_div_iff_mul_le pos).mpr
  rw [← hB, ← Finset.card_sdiff_of_subset hBT, ← Finset.prod_const, ← modulus]
  calc
    _ ≤ (∏ r ∈ T\B, cost r)*(∏ r ∈ B, cost r) := by
      gcongr with i hi
      have hiT := (Finset.mem_sdiff.mp hi).1
      exact (hc i hiT).1.trans (hc i hiT).2
    _ = _ := Finset.prod_sdiff hBT
    _ ≤ M := hfit

private lemma cutoff_exists (K : ℕ) : ∃ Y : ℕ, ∀ L : ℕ, Y ≤ L →
    16 / Real.log 2 ≤ Real.log L ∧ (K:ℝ)+1 ≤ Real.log L := by
  let B : ℝ := max (16 / Real.log 2) (K+1)
  refine ⟨⌈Real.exp B⌉₊,fun L h => ?_⟩
  have hL : Real.exp B ≤ (L:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
  have b : B ≤ Real.log L := (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hL)).mpr hL
  exact ⟨(le_max_left ..).trans b,(le_max_right ..).trans b⟩

private lemma bad_size {Y M p q K : ℕ} {V T : Finset ℕ} {cost : ℕ → ℕ}
    (hcut : ∀ L : ℕ, Y ≤ L → 16/Real.log 2 ≤ Real.log L ∧ (K:ℝ)+1 ≤ Real.log L)
    (hbad : ¬goodSeed Y M cost p q V) (hkeep : seedDivisor cost p q V*q ≤ M)
    (hp : p ∈ T) (hq : q ∈ earlier T p) (hV : V ⊆ earlier T q)
    (hc : ∀ i ∈ T, 2 ≤ i ∧ i ≤ cost i) (hfit : (∏ r ∈ T, cost r) ≤ M) :
    K ≤ T.card ∧ 4*(T.card/5) ≤ V.card := by
  let d := seedDivisor cost p q V
  let L := M / d
  have hrest := unused_factors hp hq hV hc hfit
  have hd : 0 < d := by
    unfold d seedDivisor
    apply Nat.mul_pos
    · apply Nat.mul_pos <;> have h₁ := hc p hp <;> have h₂ := hc q (Finset.mem_filter.mp hq).1 <;> omega
    · exact Finset.prod_pos fun i hi => by have := hc i (Finset.mem_filter.mp (hV hi)).1; omega
  have hqL : q ≤ L := (Nat.le_div_iff_mul_le hd).mpr ((Nat.mul_comm ..) ▸ hkeep)
  have hyq : Y < q := lt_of_not_ge fun h => hbad (Or.inl h)
  have hJ : (Real.log L)^2 < (V.card:ℝ) := lt_of_not_ge fun h => hbad (Or.inr h)
  obtain ⟨hlarge,hK⟩ := hcut L (hyq.le.trans hqL)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2:ℝ)^(T.card-(V.card+2)) ≤ (L:ℝ) := by exact_mod_cast hrest
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  have hmult := (div_le_iff₀ hlog2).mp hlarge
  have hls : 0 ≤ Real.log L := by linarith [show 0 ≤ (K:ℝ) by positivity]
  have hN := mul_le_mul_of_nonneg_right hlog hls
  have hM := mul_le_mul_of_nonneg_left hmult (Nat.cast_nonneg (T.card-(V.card+2)))
  have hrat : 16*(T.card-(V.card+2)) ≤ V.card := by
    exact_mod_cast (show (16:ℝ)*((T.card-(V.card+2):ℕ):ℝ) ≤ (V.card:ℝ) by nlinarith [hJ])
  have hKV : K ≤ V.card := by
    exact_mod_cast (show (K:ℝ) ≤ (V.card:ℝ) by nlinarith [sq_nonneg (Real.log L-1)])
  have hsmall : V.card ≤ T.card := Finset.card_le_card (hV.trans (Finset.filter_subset ..))
  have enough : 4 ≤ V.card := by
    have hlog₂le : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have h16 : 16 ≤ Real.log L := by nlinarith [mul_le_mul_of_nonneg_left hlog₂le hls]
    exact_mod_cast (show (4:ℝ) ≤ (V.card:ℝ) by nlinarith [sq_nonneg (Real.log L-16)])
  exact ⟨hKV.trans hsmall,by omega⟩

private noncomputable def rate (k : ℕ) : ℝ := (k:ℝ)^2*3^k/4^(4*(k/5))

private lemma rate_small {ε : ℝ} (hε : 0 < ε) : ∃ K, ∀ k ≥ K, rate k ≤ ε := by
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0:ℝ) ≤ 243/256) (by norm_num : (243:ℝ)/256 < 1)).const_mul (81*3^4)
  obtain ⟨t₀,h₀⟩ := Filter.eventually_atTop.mp (ht.eventually_le_const (by simpa using hε))
  refine ⟨5*(t₀+1),fun k hk => ?_⟩
  let t := k/5
  have ht₀ : t₀ ≤ t := by dsimp [t]; omega
  have ht1 : 1 ≤ t := by dsimp [t]; omega
  have hk9 : k ≤ 9*t := by dsimp [t] at *; omega
  have hk5 : k ≤ 5*t+4 := by dsimp [t]; omega
  have hc : (k:ℝ) ≤ 9*(t:ℝ) := by exact_mod_cast hk9
  have hsq : (k:ℝ)^2 ≤ 81*(t:ℝ)^2 := by nlinarith [sq_le_sq₀ (Nat.cast_nonneg k) (show 0≤9*(t:ℝ) by positivity) |>.mpr hc]
  have hpow : (3:ℝ)^k ≤ (243:ℝ)^t*3^4 := by
    calc
      _ ≤ (3:ℝ)^(5*t+4) := pow_le_pow_right₀ (by norm_num) hk5
      _ = _ := by rw [pow_add,pow_mul]; norm_num
  refine le_trans ?_ (h₀ t ht₀)
  change (k:ℝ)^2*3^k/4^(4*t) ≤ 81*3^4*((t:ℝ)^2*(243/256)^t)
  rw [pow_mul,div_pow]
  norm_num
  apply (div_le_iff₀ (show 0 < (256:ℝ)^t by positivity)).mpr
  field_simp
  nlinarith only [mul_le_mul hsq hpow (by positivity) (by positivity)]

private lemma binomial (T : Finset ℕ) : (∑ V ∈ T.powerset, (2:ℝ)^V.card) = 3^T.card := by
  have := Finset.sum_pow_mul_eq_add_pow (2:ℝ) 1 T
  norm_num at this
  exact this

private lemma loss_size {s : ℝ} (hs : 0 < s) (hh : s < 1/2) {Y M K : ℕ} {T : Finset ℕ}
    {w : ℕ → ℝ} {cost : ℕ → ℕ} (hc : ∀ i ∈ T, 2 ≤ i ∧ i ≤ cost i)
    (hf : (∏ r ∈ T, cost r) ≤ M) (hw : ∀ i ∈ T, 0 ≤ w i ∧ w i ≤ 1)
    (hcut : ∀ L : ℕ, Y ≤ L → 16/Real.log 2 ≤ Real.log L ∧ (K:ℝ)+1 ≤ Real.log L)
    {p q : ℕ} {V : Finset ℕ} (hp : p ∈ T) (hq : q ∈ earlier T p) (hV : V ⊆ earlier T q) :
    seedValue M s w cost (earlier T q) p q V ≤
      (if goodSeed Y M cost p q V then seedValue M s w cost (earlier T q) p q V else 0) +
      if K ≤ T.card then (2:ℝ)^V.card / 4^(4*(T.card/5)) else 0 := by
  classical
  have hfrac : 0 ≤ (2:ℝ)^V.card / 4^(4*(T.card/5)) := by positivity
  by_cases hg : goodSeed Y M cost p q V
  · simp only [hg,ite_true]; split_ifs <;> linarith
  rw [ite_eq_right hg,zero_add]
  by_cases hf₀ : seedDivisor cost p q V*q ≤ M
  · obtain ⟨hKt,hJ⟩ := bad_size hcut hg hf₀ hp hq hV hc hf
    rw [ite_eq_left hKt]
    have hu : s ≤ 1 := by linarith
    have hwq := hw q (Finset.mem_filter.mp hq).1
    have term := seedValue_le hs.le hu w cost M p q (earlier T q) V (hw p hp).1 hwq.1
    have positive := crossingLength_nonneg (x := ∑ i ∈ V, w i) (hw p hp).1 hwq.1
    have hlength := (crossingLength_le (x := ∑ i ∈ V, w i) (b := w q) (hw p hp).1).trans (hw p hp).2
    have hbl : (1-s)^(earlier T q\V).card ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hu) (by linarith)
    have hseed : seedWeight s w p q V ≤ s^V.card := by
      unfold seedWeight
      rw [pow_succ]
      nlinarith only [mul_nonneg (mul_nonneg (pow_nonneg hs.le V.card) hs.le) (sub_nonneg.mpr hlength),
        mul_nonneg (pow_nonneg hs.le V.card) (sub_nonneg.mpr hu)]
    have hsmall : seedValue M s w cost (earlier T q) p q V ≤ s^V.card :=
      term.trans ((mul_le_of_le_one_right (mul_nonneg (pow_nonneg hs.le _) positive) hbl).trans hseed)
    refine hsmall.trans ((le_div_iff₀ (show 0<(4:ℝ)^(4*(T.card/5)) by positivity)).mpr ?_)
    calc
      _ ≤ s^V.card*(4:ℝ)^V.card := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hJ) (pow_nonneg hs.le _)
      _ = (s*4)^V.card := (mul_pow ..).symm
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) _
  · simp only [seedValue,hf₀,ite_false]
    split_ifs <;> linarith

/-- The removed predecessor sets cost arbitrarily little at each source site, uniformly in its size. -/
lemma truncatedCrossing_lower_uniform {s ε : ℝ} (hs : 0 < s) (hh : s < 1/2) (hε : 0 < ε) :
    ∃ Y₀ : ℕ, ∀ Y ≥ Y₀, ∀ (M : ℕ) (T : Finset ℕ) (cost : ℕ → ℕ) (w : ℕ → ℝ),
      (∀ i ∈ T, 2 ≤ i ∧ i ≤ cost i) → (∀ i ∈ T, 0 ≤ w i ∧ w i ≤ 1) →
      (∏ i ∈ T, cost i) ≤ M →
      max ((∑ i ∈ T, w i)-1/s) 0 ≤ truncatedCrossing Y M s T cost w + ε := by
  classical
  obtain ⟨K,hK⟩ := rate_small hε
  obtain ⟨Y₀,hY₀⟩ := cutoff_exists K
  refine ⟨Y₀,fun Y hY M T cost w hc hw hf => ?_⟩
  have hcc : ∀ i ∈ T, 1 ≤ i ∧ i ≤ cost i := fun i hi => ⟨by have := (hc i hi).1; omega,(hc i hi).2⟩
  refine (hinge_le_crossing hs hh T cost w M hcc hw hf).trans ?_
  have terms := Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
    Finset.sum_le_sum fun V hV => loss_size hs hh hc hf hw (fun L hl => hY₀ L (hY.trans hl))
      hp hq (Finset.mem_powerset.mp hV)
  simp_rw [Finset.sum_add_distrib] at terms
  change crossing M s T cost w ≤ truncatedCrossing Y M s T cost w + _ at terms
  apply terms.trans
  apply add_le_add le_rfl
  by_cases hKt : K ≤ T.card
  · simp only [hKt,ite_true,← Finset.sum_div,binomial]
    refine le_trans ?_ (hK T.card hKt)
    apply (div_le_div_iff_of_pos_right (show 0 < (4:ℝ)^(4*(T.card/5)) by positivity)).mpr
    have count (p : ℕ) : (earlier T p).card ≤ T.card := Finset.card_le_card (Finset.filter_subset ..)
    calc
      _ ≤ ∑ p ∈ T, ∑ _q ∈ earlier T p, (3:ℝ)^T.card := Finset.sum_le_sum fun p _ =>
        Finset.sum_le_sum fun q _ => pow_le_pow_right₀ (by norm_num) (count q)
      _ ≤ ∑ _p ∈ T, (T.card:ℝ)*3^T.card := Finset.sum_le_sum fun p _ => by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast count p) (by positivity)
      _ = _ := by simp [sq,mul_assoc]
  · simpa [hKt] using hε.le

end ErdosSuranyi708
