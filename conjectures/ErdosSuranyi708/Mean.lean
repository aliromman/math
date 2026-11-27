module

public import conjectures.ErdosSuranyi708.PrimeEstimates
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section
namespace ErdosSuranyi708

open Finset Nat Real Filter

private theorem subset_moment (r v : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i) (hv : ∀ i, 0 ≤ v i)
    (T : Finset ℕ) :
    (∑ S ∈ T.powerset, (∏ p ∈ S, r p)*(∑ p ∈ S, v p)) ≤
      (∏ p ∈ T, (1+r p))*(∑ p ∈ T, r p*v p) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | @insert x T hx ih =>
    let M := ∑ S ∈ T.powerset, (∏ p ∈ S, r p)*(∑ p ∈ S, v p)
    let P := ∏ p ∈ T, (1+r p)
    have h0 : 0 ≤ P := prod_nonneg fun i _ => by linarith [hr i]
    have hnew : (∑ S ∈ T.powerset, (∏ p ∈ insert x S, r p)*(∑ p ∈ insert x S, v p)) =
        r x*v x*P + r x*M := by
      simp only [P, M, prod_one_add, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro S hS
      have hxS := notMem_mono (mem_powerset.mp hS) hx
      rw [prod_insert hxS, sum_insert hxS]; ring_nf
    rw [sum_powerset_insert hx, hnew, prod_insert hx, sum_insert hx]
    change M + (r x*v x*P+r x*M) ≤ (1+r x)*P*(r x*v x+_)
    change M ≤ P*_ at ih
    have hscale := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1+r x by linarith [hr x])
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (r x)) (hv x)) h0]

private theorem prime_set_mass {G : ℕ → ℝ} (h : MeanWeight G) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) : (∏ p ∈ S, G p/(p:ℝ)) = G (∏ p ∈ S, p) / (∏ p ∈ S, p : ℕ) := by
  classical
  rw [prod_div_distrib, Nat.cast_prod]
  congr 1
  induction S using Finset.induction with
  | empty => simp [h.one]
  | @insert p S hp ih =>
    have hpP := hS p (mem_insert_self p S)
    have hsP (q) (hq : q ∈ S) := hS q (mem_insert_of_mem hq)
    rw [prod_insert hp, prod_insert hp, h.coprime, ih hsP]
    exact Nat.Coprime.prod_right fun q hq => (Nat.coprime_primes hpP (hsP q hq)).mpr
      (fun e => hp (e ▸ hq))

/-- At least half the squarefree Euler mass is on products at most the fourth power of the cutoff. -/
theorem euler_le_harmonic {G : ℕ → ℝ} (h : MeanWeight G) {L : ℕ} (hL : 2 ≤ L) :
    meanProduct G L ≤ 2 * harmonicSum G (L^4) := by
  classical
  let T := primesLE L
  let r := fun p : ℕ => G p / (p : ℝ)
  let mass := fun S : Finset ℕ => ∏ p ∈ S, r p
  let rad := fun S : Finset ℕ => ∏ p ∈ S, p
  let P := meanProduct G L
  have hP : P = ∑ S ∈ T.powerset, mass S := Finset.prod_one_add _
  have hP0 : 0 ≤ P := zero_le_one.trans (meanProduct_one_le h L)
  have hr p : 0 ≤ r p := div_nonneg (h.nonneg _) p.cast_nonneg
  have hm S : 0 ≤ mass S := prod_nonneg (fun p _ => hr p)
  have hpS {S : Finset ℕ} (hs : S ∈ T.powerset) (p) (hp : p ∈ S) : p.Prime :=
    (mem_primesLE.mp (mem_powerset.mp hs hp)).2
  have hrad {S : Finset ℕ} (hs : S ∈ T.powerset) : 0 < rad S := prod_pos fun p hp => (hpS hs p hp).pos
  have hlog {S : Finset ℕ} (hs : S ∈ T.powerset) : Real.log (rad S) = ∑ p ∈ S, Real.log p := by
    simp only [rad, Nat.cast_prod]; exact Real.log_prod fun p hp => by exact_mod_cast (hpS hs p hp).ne_zero
  have hmoment : ∑ S ∈ T.powerset, mass S * Real.log (rad S) ≤ P * (2*Real.log L) := by
    calc
      _ = ∑ S ∈ T.powerset, mass S*(∑ p ∈ S, Real.log p) := sum_congr rfl (fun S hS => by rw [hlog hS])
      _ ≤ P * (∑ p ∈ T, r p * Real.log p) := subset_moment r (fun p => Real.log p) hr log_natCast_nonneg T
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hP0
        apply le_trans _ (prime_log_moment (by omega : 0 < L)); apply sum_le_sum
        intro p hp
        have hn := h.le_one (mem_primesLE.mp hp).2.pos
        have hh := mul_le_mul_of_nonneg_right hn (div_nonneg (log_natCast_nonneg p) p.cast_nonneg)
        simpa [r, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  let B := T.powerset.filter fun S => ¬rad S ≤ L^4
  let A := T.powerset.filter fun S => rad S ≤ L^4
  have hadd : (∑ S ∈ A, mass S)+(∑ S ∈ B, mass S) = P := by
    rw [hP]; exact sum_filter_add_sum_filter_not _ _ _
  have hb : (4*Real.log L)*(∑ S ∈ B, mass S) ≤ ∑ S ∈ T.powerset, mass S * Real.log (rad S) := by
    rw [mul_sum]
    apply (sum_le_sum fun S hS => ?_).trans (sum_le_sum_of_subset_of_nonneg (filter_subset ..)
      (fun S _ _ => mul_nonneg (hm S) (log_natCast_nonneg _)))
    have hx : L^4 ≤ rad S := Nat.le_of_lt (lt_of_not_ge (mem_filter.mp hS).2)
    have hle := Real.log_le_log (show 0 < ((L^4:ℕ):ℝ) by positivity) (by exact_mod_cast hx : ((L^4:ℕ):ℝ) ≤ rad S)
    rw [Nat.cast_pow, Real.log_pow] at hle
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hle (hm S)
  have hlogpos : 0 < Real.log L := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hgood : P ≤ 2*(∑ S ∈ A, mass S) := by
    have ht := hb.trans hmoment
    have hz : Real.log L*(2*(∑ S ∈ B, mass S)) ≤ Real.log L * P := by nlinarith only [ht]
    linarith [(mul_le_mul_iff_of_pos_left hlogpos).mp hz]
  refine hgood.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  change (∑ S ∈ A, mass S) ≤ ∑ n ∈ Icc 1 (L^4), G n / n
  apply sum_le_sum_of_injOn rad
  · intro S hs U hu heq
    have hs' := hpS (mem_filter.mp hs).1
    have hu' := hpS (mem_filter.mp hu).1
    exact (Nat.primeFactors_prod hs').symm.trans ((congrArg Nat.primeFactors heq).trans (Nat.primeFactors_prod hu'))
  · intro n hn; obtain ⟨S, hS, rfl⟩ := mem_image.mp hn
    exact mem_Icc.mpr ⟨hrad (mem_filter.mp hS).1,(mem_filter.mp hS).2⟩
  · intro S hS; exact (prime_set_mass h S (hpS (mem_filter.mp hS).1)).le
  · intro n _ _; exact div_nonneg (h.nonneg _) n.cast_nonneg

private theorem cut_product {G : ℕ → ℝ} (h : MeanWeight G) {R L : ℕ}
    (hR : 2 ≤ R) (hRL : R ≤ L) (hL : L ≤ R^32) :
    meanProduct G L ≤ meanProduct G R * exp 64 := by
  let D := primesLE L \ primesLE R
  have hlogR : 0 < Real.log R := log_pos (by exact_mod_cast (by omega : 1<R))
  have hlogL : Real.log L ≤ 32 * Real.log R := by
    simpa using Real.log_le_log (by exact_mod_cast (by omega : 0<L)) (show (L:ℝ) ≤ (R:ℝ)^32 by exact_mod_cast hL)
  have hsum : (∑ p ∈ D, G p/p) ≤ 64 := by
    apply (le_of_mul_le_mul_right (a := Real.log R) _ hlogR)
    rw [sum_mul]
    calc
      _ ≤ ∑ p ∈ D, Real.log p / p := by
        apply sum_le_sum; intro p hp
        obtain ⟨hpL, hpR⟩ := mem_sdiff.mp hp
        obtain ⟨_, hpr⟩ := mem_primesLE.mp hpL
        have hRp : R ≤ p := le_of_lt (lt_of_not_ge fun e => hpR (mem_primesLE.mpr ⟨e,hpr⟩))
        have hlogp := log_le_log (by exact_mod_cast (by omega : 0<R)) (by exact_mod_cast hRp : (R:ℝ)≤p)
        have v := mul_le_mul (h.le_one hpr.pos) hlogp hlogR.le zero_le_one
        convert div_le_div_of_nonneg_right v p.cast_nonneg using 1 <;> ring
      _ ≤ ∑ p ∈ primesLE L, Real.log p / p := sum_le_sum_of_subset_of_nonneg (sdiff_subset ..)
        (fun p _ _ => div_nonneg (log_natCast_nonneg p) p.cast_nonneg)
      _ ≤ 2 * Real.log L := prime_log_moment (by omega)
      _ ≤ _ := by linarith
  have he : ∏ p ∈ D, (1+G p/p) ≤ exp 64 := by
    calc
      _ ≤ ∏ p ∈ D, exp (G p/p) := Finset.prod_le_prod₀
        (fun p _ => by linarith [div_nonneg (h.nonneg p) p.cast_nonneg])
        (fun p _ => by linarith [Real.add_one_le_exp (G p/p)])
      _ = _ := (Real.exp_sum ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsum
  have id := prod_sdiff (f := fun p : ℕ => (1:ℝ)+G p/p) (primesLE_mono hRL)
  calc
    _ = meanProduct G R * (∏ p ∈ D, (1+G p/p)) := by simpa [meanProduct, D, mul_comm] using id.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left he (zero_le_one.trans (meanProduct_one_le h _))

private def largePrimes (L B : ℕ) (F : Finset ℕ) (a : ℕ) : Finset ℕ :=
  primesLE (L/a) \ (Icc 1 B ∪ F)

private theorem mem_largePrimes {L B a p : ℕ} {F : Finset ℕ} :
    p ∈ largePrimes L B F a ↔ p.Prime ∧ p ≤ L/a ∧ B < p ∧ p ∉ F := by
  constructor
  · intro hp
    obtain ⟨hQ,hx⟩ := mem_sdiff.mp hp
    obtain ⟨hq, hpr⟩ := mem_primesLE.mp hQ
    exact ⟨hpr,hq,lt_of_not_ge (fun hh => hx (mem_union_left _ (mem_Icc.mpr ⟨hpr.pos,hh⟩))),
      fun hh => hx (mem_union_right _ hh)⟩
  · rintro ⟨hpr,hq,hB,hF⟩
    exact mem_sdiff.mpr ⟨mem_primesLE.mpr ⟨hq,hpr⟩, fun hh => (mem_union.mp hh).elim
      (fun e => hB.not_ge (mem_Icc.mp e).2) hF⟩

private theorem prime_room {L B a : ℕ} {F : Finset ℕ} (ha : 0<a) (hq : 4 ≤ L/a)
    (room : 8*((B:ℝ)+F.card)*a*Real.log L ≤ L) :
    (L:ℝ)/(8*a*Real.log L) ≤ (largePrimes L B F a).card := by
  let q := L/a
  have hq' : (4:ℕ) ≤ q := hq
  have hqL : q ≤ L := Nat.div_le_self ..
  have hL : 1 < L := by omega
  have hl : 0 < Real.log L := log_pos (by exact_mod_cast hL)
  have hlg : 0 < Real.log q := log_pos (by exact_mod_cast (by omega : 1<q))
  have hcast : (L : ℝ) ≤ 2*(q:ℝ)*a := by
    exact_mod_cast ((Nat.lt_mul_div_succ L ha).le.trans <|
      show a*(L/a+1) ≤ 2*q*a by rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega))
  have hhalf : (1:ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2); norm_num at hh ⊢; linarith
  have hQ := (div_le_iff₀ hlg).mp (Chebyshev.pi_ge_of_four_le hq')
  rw [← Nat.primesLE_card_eq_primeCounting] at hQ
  have hlarge : (L : ℝ) ≤ 4*(primesLE q).card*a*Real.log L := by
    have hlog := Real.log_le_log (by exact_mod_cast (by omega : 0<q)) (by exact_mod_cast hqL : (q:ℝ)≤L)
    have hk := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (primesLE q).card)
    have hh := mul_le_mul_of_nonneg_left hhalf q.cast_nonneg
    have hqq : (q:ℝ) ≤ 2*(primesLE q).card*Real.log L := by linarith [hk,hh]
    nlinarith [mul_le_mul_of_nonneg_right hqq a.cast_nonneg]
  have hcard : (primesLE q).card ≤ (largePrimes L B F a).card + (B+F.card) := by
    apply (card_le_card_sdiff_add_card (s:=primesLE q) (t:=Icc 1 B ∪ F)).trans
    apply Nat.add_le_add_left
    simpa using card_union_le (Icc 1 B) F
  have hca : ((primesLE q).card:ℝ) ≤ (largePrimes L B F a).card + ((B:ℝ)+F.card) := by exact_mod_cast hcard
  apply (div_le_iff₀ (by positivity : 0 < 8*(a:ℝ)*Real.log L)).mpr
  nlinarith only [hlarge,room,mul_le_mul_of_nonneg_right hca (mul_nonneg a.cast_nonneg hl.le)]

private theorem large_prime_lift {G : ℕ → ℝ} (h : MeanWeight G) {L B : ℕ} {F : Finset ℕ} {u : ℝ}
    (hfree : ∀ p ∈ primesLE L, p ∉ F → u ≤ G p) :
    (∑ a ∈ Icc 1 B, ((largePrimes L B F a).card : ℝ)*(G a*u)) ≤ meanSum G L := by
  classical
  have he : (∑ a ∈ Icc 1 B, ((largePrimes L B F a).card : ℝ)*(G a*u)) =
      ∑ z ∈ (Icc 1 B).sigma (largePrimes L B F), G z.1*u := by simp [sum_sigma]
  rw [he]
  apply sum_le_sum_of_injOn (fun z : (_ : ℕ) × ℕ => z.1*z.2)
  · rintro ⟨a,p⟩ hp ⟨b,q⟩ hq heq
    obtain ⟨ha,hp⟩ := mem_sigma.mp hp; obtain ⟨hb,hq⟩ := mem_sigma.mp hq
    obtain ⟨hp,_,hBp,_⟩ := mem_largePrimes.mp hp
    obtain ⟨hq,_,hBq,_⟩ := mem_largePrimes.mp hq
    obtain ⟨_,haB⟩ := mem_Icc.mp ha; obtain ⟨hb0,hbB⟩ := mem_Icc.mp hb
    change a*p=b*q at heq
    have hdiv : p ∣ b*q := heq ▸ Nat.dvd_mul_left ..
    have epq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp ((hp.dvd_mul.mp hdiv).resolve_left
      fun hd => hBp.not_ge ((Nat.le_of_dvd hb0 hd).trans hbB))
    subst q; have := Nat.eq_of_mul_eq_mul_right hp.pos heq; subst b; rfl
  · intro n hn; obtain ⟨⟨a,p⟩,hz,rfl⟩ := mem_image.mp hn
    obtain ⟨ha,hp⟩ := mem_sigma.mp hz
    have ha0 := (mem_Icc.mp ha).1
    obtain ⟨hpr,hq,_,_⟩ := mem_largePrimes.mp hp
    exact mem_Icc.mpr ⟨Nat.mul_pos ha0 hpr.pos, by simpa [mul_comm] using (Nat.le_div_iff_mul_le ha0).mp hq⟩
  · rintro ⟨a,p⟩ hz
    obtain ⟨ha,hp⟩ := mem_sigma.mp hz
    obtain ⟨hpr,hq,hBp,hF⟩ := mem_largePrimes.mp hp
    obtain ⟨ha0,haB⟩ := mem_Icc.mp ha
    change G a*u ≤ G (a*p)
    rw [h.coprime ((hpr.coprime_iff_not_dvd.mpr (fun d => hBp.not_ge ((Nat.le_of_dvd ha0 d).trans haB))).symm)]
    exact mul_le_mul_of_nonneg_left (hfree p (mem_primesLE.mpr ⟨hq.trans (Nat.div_le_self ..),hpr⟩) hF) (h.nonneg _)
  · intro n _ _; exact h.nonneg n

/-- A single threshold works for every weight and every exceptional set of the stated size. -/
theorem mean_lower {u : ℝ} (hu : 0 < u) : ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ,
    ∀ L : ℕ, L₀ ≤ L → ∀ (F : Finset ℕ) (G : ℕ → ℝ), MeanWeight G →
    (F.card : ℝ) ≤ (Real.log L)^2+2 → (∀ p ∈ primesLE L, p ∉ F → u ≤ G p) →
    c * L * meanProduct G L / Real.log L ≤ meanSum G L := by
  refine ⟨u/(16*exp 64), by positivity, 64^16, ?_⟩
  intro L hL F G h hF hfree
  let R := Nat.nthRoot 16 L
  have hR : 64 ≤ R := (Nat.le_nthRoot_iff (by decide : 16≠0)).mpr hL
  have hlo : R^16 ≤ L := Nat.pow_nthRoot_le (.inl (by decide))
  have hR2 : R+1 ≤ R^2 := by nlinarith only [Nat.mul_le_mul_left R (show 2≤R by omega), hR]
  have hhi : L ≤ R^32 := calc
    _ ≤ (R+1)^16 := (Nat.lt_pow_nthRoot_add_one (by decide) L).le
    _ ≤ (R^2)^16 := Nat.pow_le_pow_left hR2 _
    _ = _ := by ring
  have hRL : R ≤ L := (Nat.le_self_pow (by decide : 16≠0) R).trans hlo
  have hpL : 0 < Real.log L := log_pos (by exact_mod_cast (by omega : 1<L))
  have hRx : (64:ℝ) ≤ R := by exact_mod_cast hR
  have hlx : (R:ℝ)^16 ≤ L := by exact_mod_cast hlo
  have hlog : Real.log L ≤ 32*(R:ℝ) := by
    have hh := Real.log_le_log (by exact_mod_cast (by omega : 0<L))
      (show (L:ℝ)≤ (R:ℝ)^32 by exact_mod_cast hhi)
    rw [Real.log_pow] at hh; push_cast at hh; linarith [log_le_self R.cast_nonneg]
  have hRbig : (2048:ℝ) ≤ (R:ℝ)^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤64) hRx]
  have hfc : (F.card:ℝ) ≤ (R:ℝ)^4 := by
    have hs := sq_le_sq₀ hpL.le (show 0 ≤ 32*(R:ℝ) by positivity) |>.mpr hlog
    nlinarith only [hF,hs,mul_nonneg (sub_nonneg.mpr hRbig) (sq_nonneg (R:ℝ)),hRbig]
  have hmany {a : ℕ} (ha : a ∈ Icc 1 (R^4)) : (L:ℝ)/(8*a*Real.log L) ≤ (largePrimes L (R^4) F a).card := by
    obtain ⟨ha0,haB⟩ := mem_Icc.mp ha
    have hax : (a:ℝ)≤(R:ℝ)^4 := by exact_mod_cast haB
    apply prime_room ha0
    · apply (Nat.le_div_iff_mul_le ha0).mpr
      calc
        _ ≤ 4*R^4 := Nat.mul_le_mul_left _ haB
        _ ≤ R^12 * R^4 := Nat.mul_le_mul_right _ ((by omega : 4≤R).trans (Nat.le_self_pow (by decide : 12≠0) R))
        _ = _ := by rw [← pow_add]
        _ ≤ _ := hlo
    · push_cast
      calc
        _ ≤ 8*((R:ℝ)^4 + (R:ℝ)^4)*(R:ℝ)^4*(32*(R:ℝ)) := by gcongr
        _ = 512*(R:ℝ)^9 := by ring
        _ ≤ (R:ℝ)^7*(R:ℝ)^9 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (512:ℝ) ≤ 64^7 := by norm_num
               _ ≤ _ := by gcongr
        _ = (R:ℝ)^16 := by ring
        _ ≤ _ := hlx
  have hharm := (cut_product h (by omega : 2≤R) hRL hhi).trans (mul_le_mul_of_nonneg_right
    (euler_le_harmonic h (by omega : 2≤R)) (exp_pos 64).le)
  have hsum : u*(L:ℝ)/(8*Real.log L)*harmonicSum G (R^4) ≤ meanSum G L := by
    apply le_trans _ (large_prime_lift (B:=R^4) h hfree)
    rw [harmonicSum, mul_sum]
    apply sum_le_sum; intro a ha
    convert mul_le_mul_of_nonneg_right (hmany ha) (mul_nonneg (h.nonneg a) hu.le) using 1; ring
  apply le_trans _ hsum
  have hz := mul_le_mul_of_nonneg_left hharm (show 0 ≤ u*L/(16*exp 64*Real.log L) by positivity)
  convert hz using 1 <;> field_simp
  ring

private theorem unit_weight : MeanWeight (fun _ => 1) where
  one := rfl
  nonneg _ := zero_le_one
  mul_le _ _ := le_rfl
  coprime _ := by simp

private theorem harmonic_unit (L : ℕ) : harmonicSum (fun _ => 1) L = harmonic L := by
  simp [harmonicSum, harmonic_eq_sum_Icc, one_div]

private theorem unit_product_le (L : ℕ) : meanProduct (fun _ => 1) L ≤ 10*(1+Real.log L) := by
  by_cases hl : L < 2
  · interval_cases L <;> simp [meanProduct, Nat.primesLE]
  have he := euler_le_harmonic unit_weight (L := L) (by omega)
  rw [harmonic_unit] at he
  have hh := harmonic_le_one_add_log (L^4)
  rw [Nat.cast_pow, Real.log_pow] at hh
  push_cast at hh
  linarith [log_natCast_nonneg L]

private theorem log_le_unit (L : ℕ) : Real.log L ≤ eulerConstant * meanProduct (fun _ => 1) L := by
  apply le_trans _ (harmonic_le_euler unit_weight L)
  simpa [harmonic_unit] using log_le_harmonic_floor (L:ℝ) L.cast_nonneg

private theorem exceptional_product (T : Finset ℕ) (hp : ∀ p ∈ T, p.Prime) {J : ℕ} (hJ : T.card≤J) :
    (∏ p ∈ T, (1+(1:ℝ)/p)) ≤ 10*exp 1*(1+Real.log (J+3:ℕ)) := by
  let A := T.filter (·≤J)
  let D := T.filter fun p => ¬p≤J
  have hA : ∏ p ∈ A, (1+(1:ℝ)/p) ≤ meanProduct (fun _ => 1) J := by
    apply prod_le_prod_of_subset_of_one_le₀
    · intro p h; exact mem_primesLE.mpr ⟨(mem_filter.mp h).2,hp p (mem_filter.mp h).1⟩
    · intro p _; positivity
    · intro p _ _; exact le_add_of_nonneg_right (by positivity)
  have hD : (∏ p ∈ D, (1+(1:ℝ)/p)) ≤ exp 1 := by
    calc
      _ ≤ ∏ p ∈ D, exp (1/(p:ℝ)) := Finset.prod_le_prod₀ (fun _ _ => by positivity)
        (fun p _ => by linarith [Real.add_one_le_exp (1/(p:ℝ))])
      _ = _ := (Real.exp_sum ..).symm
      _ ≤ exp 1 := by
        apply exp_le_exp.mpr
        calc
          _ ≤ ∑ _p ∈ D, 1/((J:ℝ)+1) := by
            apply sum_le_sum; intro p h
            apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast (Nat.lt_of_not_ge (mem_filter.mp h).2)
          _ ≤ 1 := by
            simp only [sum_const, nsmul_eq_mul]
            have hc : (D.card : ℝ) ≤ J := by exact_mod_cast (card_filter_le ..).trans hJ
            rw [mul_one_div, div_le_one (by positivity)]; linarith
  have hj : Real.log J ≤ Real.log (J+3:ℕ) := by
    rcases eq_or_ne J 0 with rfl | hj
    · simpa using log_natCast_nonneg 3
    · apply log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hj); exact_mod_cast (by omega : J≤J+3)
  rw [← prod_filter_mul_prod_filter_not T (·≤J)]
  have hh := mul_le_mul (hA.trans (unit_product_le J)) hD (prod_nonneg fun _ _ => by positivity)
    (show 0 ≤ 10*(1+Real.log J) by positivity)
  have ht := mul_le_mul_of_nonneg_right hj (exp_pos 1).le
  nlinarith only [hh,ht]

/-- Primes with small weight cost at most one logarithmic factor in their number. -/
theorem product_lower {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) : ∃ c : ℝ, 0 < c ∧
    ∀ L (F : Finset ℕ) (G : ℕ → ℝ), MeanWeight G → (∀ p ∈ primesLE L, p ∉ F → u ≤ G p) →
    c * (Real.log L)^u / (1+Real.log (F.card+3:ℕ)) ≤ meanProduct G L := by
  refine ⟨(eulerConstant^u*10*exp 1)⁻¹, by positivity [eulerConstant_pos], ?_⟩
  intro L F G h hfree
  let T := (primesLE L).filter (·∈F)
  have he := exceptional_product T (fun p hp => (mem_primesLE.mp (mem_filter.mp hp).1).2)
    (show T.card ≤ F.card by apply card_le_card; exact fun p hp => (mem_filter.mp hp).2)
  have huP : (meanProduct (fun _ => 1) L)^u ≤ meanProduct G L * (∏ p ∈ T, (1+(1:ℝ)/p)) := by
    rw [meanProduct, ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    calc
      _ ≤ ∏ p ∈ primesLE L, ((1+G p/p)*(if p∈F then 1+1/(p:ℝ) else 1)) := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro p hp
        have hcon := rpow_one_add_le_one_add_mul_self (show -1 ≤ 1/(p:ℝ) by linarith [show (0:ℝ)≤1/p by positivity]) hu.le hu1
        apply hcon.trans
        by_cases hf : p ∈ F
        · simp only [hf, ↓reduceIte]
          have h1 : 1+u*(1/(p:ℝ)) ≤ 1+1/(p:ℝ) := by gcongr; simpa using mul_le_mul_of_nonneg_right hu1 (show (0:ℝ)≤1/p by positivity)
          exact h1.trans (le_mul_of_one_le_left (by positivity) (le_add_of_nonneg_right (div_nonneg (h.nonneg _) p.cast_nonneg)))
        · simp only [hf, ↓reduceIte, mul_one, ← div_eq_mul_one_div]
          gcongr; exact hfree p hp hf
      _ = _ := by rw [prod_mul_distrib]; simp [meanProduct,T,prod_filter]
  have hlo := Real.rpow_le_rpow (log_natCast_nonneg L) (log_le_unit L) hu.le
  rw [Real.mul_rpow eulerConstant_pos.le (zero_le_one.trans (meanProduct_one_le unit_weight L))] at hlo
  have hmain := hlo.trans (mul_le_mul_of_nonneg_left (huP.trans (mul_le_mul_of_nonneg_left he
    (zero_le_one.trans (meanProduct_one_le h L)))) (Real.rpow_nonneg eulerConstant_pos.le _))
  have hex : 0 < eulerConstant^u*10*exp 1 := by positivity [eulerConstant_pos]
  have hj : 0 < 1+Real.log (F.card+3:ℕ) := by linarith [log_natCast_nonneg (F.card+3)]
  apply (div_le_iff₀ hj).mpr
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hex).mpr
  convert hmain using 1; ring

private theorem prime_scaled_upper {s t : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) :
    1+s*t ≤ (1+t)^s * exp (2*t^2) := by
  have ht1 : 0 < 1+t := by linarith
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (exp_pos _).ne', Real.log_rpow ht1, Real.log_exp]
  have hx : t-t^2 ≤ 1-(1+t)⁻¹ := by
    apply (mul_le_mul_iff_of_pos_right ht1).mp
    field_simp
    nlinarith [pow_nonneg ht 3]
  have hlog := (hx.trans (Real.one_sub_inv_le_log_of_pos ht1))
  have hst := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+s*t)
  nlinarith [mul_le_mul_of_nonneg_left hlog hs, mul_le_mul_of_nonneg_right hs1 (sq_nonneg t)]

private theorem omega_product_le {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (L : ℕ) :
    meanProduct (omegaWeight s) L ≤ (meanProduct (fun _ => 1) L)^s * eulerConstant := by
  calc
    _ ≤ ∏ p ∈ primesLE L, (1+1/(p:ℝ))^s * exp (2*((p:ℝ)^2)⁻¹) := by
      apply Finset.prod_le_prod₀ (fun p _ => add_nonneg zero_le_one
        (div_nonneg ((omega_isMeanWeight hs hs1).nonneg p) p.cast_nonneg))
      intro p hp
      simpa [omegaWeight, (mem_primesLE.mp hp).2.primeFactors, div_eq_mul_inv, inv_pow] using
        prime_scaled_upper hs hs1 (inv_nonneg.mpr p.cast_nonneg)
    _ ≤ _ := by
      rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun _ _ => by positivity) s, ← Real.exp_sum, ← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Real.summable_nat_pow_inv.mpr (by decide : 1<2)).sum_le_tsum _ (by intros; positivity)

private theorem omega_product_log {s : ℝ} (hs : 0≤s) (hs1 : s≤1) {L : ℕ} (hL : 2≤L) :
    meanProduct (omegaWeight s) L ≤ (30^s*eulerConstant)*(Real.log L)^s := by
  have hl : (1:ℝ)/2 ≤ Real.log L := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have hb := Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤L by exact_mod_cast hL)
    norm_num at hh; linarith
  have ha : meanProduct (fun _ => 1) L ≤ 30*Real.log L := by linarith [unit_product_le L]
  have hb := Real.rpow_le_rpow (zero_le_one.trans (meanProduct_one_le unit_weight L)) ha hs
  rw [Real.mul_rpow (by norm_num) (log_natCast_nonneg L)] at hb
  apply (omega_product_le hs hs1 L).trans
  simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_right hb eulerConstant_pos.le

/-- The reciprocal sum of `s` to the number of distinct prime factors grows at most as `(log L)^s`. -/
theorem omega_harmonic {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 2 ≤ L →
    harmonicSum (omegaWeight s) L ≤ C*(Real.log L)^s := by
  refine ⟨eulerConstant*(30^s*eulerConstant), by positivity [eulerConstant_pos], ?_⟩
  intro L hL
  apply (harmonic_le_euler (omega_isMeanWeight hs.le hs1) L).trans
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left (omega_product_log hs.le hs1 hL) eulerConstant_pos.le

/-- The same weight has a full power of the logarithm more cancellation in an ordinary sum. -/
theorem omega_count {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 2 ≤ L →
    meanSum (omegaWeight s) L ≤ C*L*(Real.log L)^(s-1) := by
  obtain ⟨C,hC,hup⟩ := mean_upper
  refine ⟨C*(30^s*eulerConstant), by positivity [eulerConstant_pos], ?_⟩
  intro L hL
  have hl : 0 < Real.log L := Real.log_pos (by exact_mod_cast (by omega : 1<L))
  apply (hup _ (omega_isMeanWeight hs.le hs1) L hL).trans
  rw [Real.rpow_sub_one hl.ne']
  have hb := mul_le_mul_of_nonneg_left (omega_product_log hs.le hs1 hL) (mul_nonneg hC.le L.cast_nonneg)
  convert div_le_div_of_nonneg_right hb hl.le using 1; ring

end ErdosSuranyi708
