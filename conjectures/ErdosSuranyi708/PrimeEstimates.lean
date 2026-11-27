module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.PSeries

@[expose] public section
namespace ErdosSuranyi708

open Finset Nat Real Filter

/-- A nonnegative multiplicative function that decreases on multiples. -/
structure MeanWeight (G : ℕ → ℝ) : Prop where
  one : G 1 = 1
  nonneg (n : ℕ) : 0 ≤ G n
  mul_le {a b : ℕ} : 0 < a → 0 < b → G (a*b) ≤ G a
  coprime {a b : ℕ} : a.Coprime b → G (a*b) = G a * G b

noncomputable def meanSum (G : ℕ → ℝ) (L : ℕ) : ℝ := ∑ n ∈ Icc 1 L, G n
noncomputable def harmonicSum (G : ℕ → ℝ) (L : ℕ) : ℝ := ∑ n ∈ Icc 1 L, G n / n
noncomputable def meanProduct (G : ℕ → ℝ) (L : ℕ) : ℝ := ∏ p ∈ primesLE L, (1 + G p / p)
noncomputable def omegaWeight (s : ℝ) (n : ℕ) : ℝ := s ^ n.primeFactors.card

theorem MeanWeight.le_one {G : ℕ → ℝ} (h : MeanWeight G) {n : ℕ} (hn : 0 < n) : G n ≤ 1 := by
  simpa [h.one] using h.mul_le (a := 1) (by decide) hn

theorem meanProduct_one_le {G : ℕ → ℝ} (h : MeanWeight G) (L : ℕ) : 1 ≤ meanProduct G L := by
  exact one_le_prod₀ fun p _ => le_add_of_nonneg_right (div_nonneg (h.nonneg p) p.cast_nonneg)

theorem meanProduct_mono {G : ℕ → ℝ} (h : MeanWeight G) {a b : ℕ} (hab : a ≤ b) :
    meanProduct G a ≤ meanProduct G b := by
  apply prod_le_prod_of_subset_of_one_le₀ (primesLE_mono hab)
  · intro p _
    exact add_nonneg zero_le_one (div_nonneg (h.nonneg p) p.cast_nonneg)
  intro p _ _
  exact le_add_of_nonneg_right (div_nonneg (h.nonneg p) p.cast_nonneg)

theorem omega_isMeanWeight {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) : MeanWeight (omegaWeight s) where
  one := by simp [omegaWeight]
  nonneg _ := pow_nonneg hs _
  mul_le {a b} ha hb := by
    apply pow_le_pow_of_le_one hs hs1
    exact card_le_card (primeFactors_mono (dvd_mul_right a b) (Nat.mul_ne_zero ha.ne' hb.ne'))
  coprime {a b} hab := by
    simp [omegaWeight, hab.primeFactors_mul, card_union_of_disjoint hab.disjoint_primeFactors, pow_add]

noncomputable def eulerConstant : ℝ := exp (2 * ∑' n : ℕ, ((n : ℝ)^2)⁻¹)

theorem eulerConstant_pos : 0 < eulerConstant := exp_pos _

private theorem harmonicFactor_summable {G : ℕ → ℝ} (h : MeanWeight G) {p : ℕ} (hp : p.Prime) :
    Summable (fun n : ℕ => ‖G (p^n) / ((p^n : ℕ) : ℝ)‖) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  apply (summable_geometric_of_lt_one (inv_nonneg.mpr p.cast_nonneg) (inv_lt_one_of_one_lt₀ hp1)).of_nonneg_of_le
  · intro n; exact norm_nonneg _
  · intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (h.nonneg _) (Nat.cast_nonneg _)), Nat.cast_pow, inv_pow]
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right (h.le_one (pow_pos hp.pos n)) (inv_nonneg.mpr (pow_nonneg p.cast_nonneg n))

private theorem harmonicFactor_le {G : ℕ → ℝ} (h : MeanWeight G) {p : ℕ} (hp : p.Prime) :
    (∑' n : ℕ, G (p^n) / ((p^n : ℕ) : ℝ)) ≤ 1 + G p / ((p : ℝ)-1) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpi : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have ht := (harmonicFactor_summable h hp).of_norm
  rw [ht.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_one, div_one, h.one]
  apply add_le_add_right
  have geo := summable_geometric_of_lt_one (inv_nonneg.mpr p.cast_nonneg) hpi
  calc
    _ ≤ ∑' n : ℕ, (G p / p) * ((p : ℝ)⁻¹)^n := by
      apply Summable.tsum_le_tsum _ ((summable_nat_add_iff 1).mpr ht) (geo.mul_left _)
      intro n
      rw [pow_succ', Nat.cast_mul, Nat.cast_pow, div_eq_mul_inv, mul_inv, inv_pow]
      have hh := h.mul_le hp.pos (pow_pos hp.pos n)
      have hnn : 0 ≤ (p : ℝ)⁻¹ * ((p : ℝ)^n)⁻¹ := by positivity
      convert mul_le_mul_of_nonneg_right hh hnn using 1; ring
    _ = G p / ((p : ℝ)-1) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (inv_nonneg.mpr p.cast_nonneg) hpi]
      field_simp

private theorem eulerCorrection_le {g : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1) {p : ℝ} (hp : 2 ≤ p) :
    1 + g/(p-1) ≤ (1+g/p) * exp (2 * (p^2)⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p-1 := by linarith
  have hc : g/(p*(p-1)) ≤ 2*(p^2)⁻¹ := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ (mul_pos hp0 hp2) (pow_pos hp0 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hg1) (sq_nonneg p), mul_nonneg hp0.le (sub_nonneg.mpr hp)]
  have heq : g/(p-1) = g/p + g/(p*(p-1)) := by field_simp; ring
  calc
    _ ≤ (1+g/p)*(1+2*(p^2)⁻¹) := by
      rw [heq]
      nlinarith [mul_nonneg (div_nonneg hg hp0.le) (inv_nonneg.mpr (sq_nonneg p))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (2*(p^2)⁻¹)])
      (by positivity)

/-- The reciprocal sum and its finite Euler product differ by at most an absolute factor. -/
theorem harmonic_le_euler {G : ℕ → ℝ} (h : MeanWeight G) (L : ℕ) :
    harmonicSum G L ≤ eulerConstant * meanProduct G L := by
  classical
  let f : ℕ → ℝ := fun n => G n / n
  have hf1 : f 1 = 1 := by simp [f, h.one]
  have hmul : ∀ {m n}, m.Coprime n → f (m*n) = f m * f n := by
    intro m n hmn; simp only [f, h.coprime hmn, Nat.cast_mul]; ring
  obtain ⟨_, H⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf1 hmul
    (fun hp => harmonicFactor_summable h hp) (primesLE L)
  have he (n : {n // n ∈ Icc 1 L}) : (n : ℕ) ∈ factoredNumbers (primesLE L) :=
    mem_factoredNumbers_iff_forall_le.mpr ⟨Nat.one_le_iff_ne_zero.mp (mem_Icc.mp n.2).1, fun p hpn hp _ =>
      mem_primesLE.mpr ⟨hpn.trans (mem_Icc.mp n.2).2, hp⟩⟩
  let i : {n // n ∈ Icc 1 L} ↪ factoredNumbers (primesLE L) :=
    ⟨fun n => ⟨n.1,he n⟩, fun _ _ hnm => Subtype.ext (congrArg (fun x : factoredNumbers (primesLE L) => x.val) hnm)⟩
  let T := (Icc 1 L).attach.map i
  have hT := H.summable.sum_le_tsum T (fun m _ => div_nonneg (h.nonneg _) (Nat.cast_nonneg _))
  rw [H.tsum_eq, Finset.filter_true_of_mem (fun _ hp => (mem_primesLE.mp hp).2)] at hT
  have hs : harmonicSum G L ≤ ∏ p ∈ primesLE L, ∑' n : ℕ, f (p^n) := by
    rw [show T = (Icc 1 L).attach.map i from rfl, sum_map] at hT
    change (∑ n ∈ (Icc 1 L).attach, f (n : ℕ)) ≤ _ at hT
    rwa [sum_attach] at hT
  refine hs.trans ((Finset.prod_le_prod₀ (fun p _ => tsum_nonneg fun n => div_nonneg (h.nonneg _) (Nat.cast_nonneg _))
    (fun p hp => (harmonicFactor_le h (mem_primesLE.mp hp).2).trans
      (eulerCorrection_le (h.nonneg _) (h.le_one (mem_primesLE.mp hp).2.pos) (by exact_mod_cast (mem_primesLE.mp hp).2.two_le)))).trans ?_)
  rw [prod_mul_distrib, ← Real.exp_sum, ← mul_sum, mul_comm, meanProduct]
  apply mul_le_mul_of_nonneg_right _ (meanProduct_one_le h L |>.trans' zero_le_one)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (Real.summable_nat_pow_inv.mpr (by decide : 1<2)).sum_le_tsum _ (by intros; positivity)

private theorem divisor_interchange (L : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ Icc 1 L, ∑ d ∈ n.divisors, f d (n/d)) =
      ∑ d ∈ Icc 1 L, ∑ m ∈ Icc 1 (L/d), f d m := by
  classical
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (s := (Icc 1 L).sigma Nat.divisors)
    (t := (Icc 1 L).sigma (fun d => Icc 1 (L/d)))
    (fun a _ => ⟨a.2, a.1/a.2⟩) (fun b _ => ⟨b.1*b.2, b.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n,d⟩ hn
    obtain ⟨hn, hd⟩ := mem_sigma.mp hn
    obtain ⟨hdn,hn0⟩ := mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn0)
    have hdn' := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hd0, hdn'.trans (mem_Icc.mp hn).2⟩,
      mem_Icc.mpr ⟨Nat.div_pos hdn' hd0, Nat.div_le_div_right (mem_Icc.mp hn).2⟩⟩
  · rintro ⟨d,m⟩ hd
    obtain ⟨hd, hm⟩ := mem_sigma.mp hd
    obtain ⟨hd,hL⟩ := mem_Icc.mp hd
    obtain ⟨hm,hq⟩ := mem_Icc.mp hm
    have hmul : m*d ≤ L := (Nat.le_div_iff_mul_le hd).mp hq
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd hm, by simpa [mul_comm] using hmul⟩,
      mem_divisors.mpr ⟨dvd_mul_right d m, (Nat.mul_pos hd hm).ne'⟩⟩
  · rintro ⟨n,d⟩ hn
    have hd := (mem_divisors.mp (mem_sigma.mp hn).2).1
    simp [Nat.mul_div_cancel' hd]
  · rintro ⟨d,m⟩ hd
    have hd0 := (mem_Icc.mp (mem_sigma.mp hd).1).1
    simp [Nat.mul_div_cancel_left _ hd0]
  · intros; rfl

private theorem log_convolution (L : ℕ) :
    (∑ p ∈ Icc 1 L, (L/p : ℕ) * ArithmeticFunction.vonMangoldt p) =
      ∑ n ∈ Icc 1 L, Real.log n := by
  simpa [ArithmeticFunction.vonMangoldt_sum] using
    (divisor_interchange L (fun d _ => ArithmeticFunction.vonMangoldt d)).symm

/-- A logarithmic moment bound for primes, obtained by counting multiples. -/
theorem prime_log_moment {L : ℕ} (hL : 0 < L) :
    ∑ p ∈ primesLE L, Real.log p / p ≤ 2 * Real.log L := by
  apply (mul_le_mul_iff_of_pos_left (by exact_mod_cast hL : (0:ℝ)<L)).mp
  rw [mul_sum]
  calc
    _ ≤ 2 * ∑ p ∈ primesLE L, ((L/p : ℕ):ℝ)*ArithmeticFunction.vonMangoldt p := by
      rw [mul_sum]; apply sum_le_sum
      intro p hp
      obtain ⟨hpL,hp⟩ := mem_primesLE.mp hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hq : 1 ≤ L/p := Nat.div_pos hpL hp.pos
      have hmul : L ≤ (2*(L/p))*p := by
        calc L ≤ (L/p+1)*p := (Nat.lt_mul_div_succ L hp.pos).le.trans_eq (by ring)
             _ ≤ _ := Nat.mul_le_mul_right p (by omega)
      have hh : (L:ℝ)/p ≤ 2*(L/p:ℕ) := (div_le_iff₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hmul)
      convert mul_le_mul_of_nonneg_right hh (log_natCast_nonneg p) using 1 <;> ring
    _ ≤ 2 * ∑ p ∈ Icc 1 L, ((L/p : ℕ):ℝ)*ArithmeticFunction.vonMangoldt p := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp; obtain ⟨h1,h2⟩ := mem_primesLE.mp hp; exact mem_Icc.mpr ⟨h2.pos,h1⟩
      · intro p _ _; exact mul_nonneg (Nat.cast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := by
      rw [log_convolution]
      have hlog : (∑ n ∈ Icc 1 L, Real.log n) ≤ ∑ _n ∈ Icc 1 L, Real.log L :=
        sum_le_sum fun n hn => log_le_log (by exact_mod_cast (mem_Icc.mp hn).1) (by exact_mod_cast (mem_Icc.mp hn).2)
      simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ)≤2)

private theorem log_mean_le {G : ℕ → ℝ} (h : MeanWeight G) (L : ℕ) :
    (∑ n ∈ Icc 1 L, G n * Real.log n) ≤ (Real.log 4 + 4)*L*harmonicSum G L := by
  calc
    _ = ∑ n ∈ Icc 1 L, ∑ d ∈ n.divisors, G n * ArithmeticFunction.vonMangoldt (n/d) := by
      apply sum_congr rfl
      intro n _
      rw [← mul_sum, Nat.sum_div_divisors, ArithmeticFunction.vonMangoldt_sum]
    _ ≤ ∑ n ∈ Icc 1 L, ∑ d ∈ n.divisors, G d * ArithmeticFunction.vonMangoldt (n/d) := by
      apply sum_le_sum; intro n hn; apply sum_le_sum; intro d hd
      obtain ⟨hdn, hn0⟩ := mem_divisors.mp hd
      have hd0 := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn0)
      have hq := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn) hd0
      apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
      simpa [Nat.mul_div_cancel' hdn] using h.mul_le hd0 hq
    _ = _ := divisor_interchange L (fun d m => G d * ArithmeticFunction.vonMangoldt m)
    _ ≤ _ := by
      rw [harmonicSum, mul_sum]
      apply sum_le_sum; intro d hd; rw [← mul_sum]
      have hd0 := (mem_Icc.mp hd).1
      have hsum : (∑ m ∈ Icc 1 (L/d), ArithmeticFunction.vonMangoldt m) ≤ (Real.log 4+4)*((L/d : ℕ):ℝ) := by
        have he : Icc 1 (L/d) = Ioc 0 (L/d) := by ext x; simp; omega
        simpa [Chebyshev.psi, he] using
          Chebyshev.psi_le_const_mul_self (x:=((L/d:ℕ):ℝ)) (Nat.cast_nonneg _)
      have hdiv : ((L/d:ℕ):ℝ) ≤ (L:ℝ)/d := (le_div_iff₀ (by exact_mod_cast hd0)).mpr (by exact_mod_cast Nat.div_mul_le_self L d)
      calc
        _ ≤ G d * ((Real.log 4+4)*((L:ℝ)/d)) := mul_le_mul_of_nonneg_left
          (hsum.trans (mul_le_mul_of_nonneg_left hdiv (by positivity))) (h.nonneg d)
        _ = _ := by ring

/-- The upper mean estimate holds for every nonnegative decreasing multiplicative weight. -/
theorem mean_upper : ∃ C : ℝ, 0 < C ∧ ∀ (G : ℕ → ℝ), MeanWeight G → ∀ L : ℕ, 2 ≤ L →
    meanSum G L ≤ C * L * meanProduct G L / Real.log L := by
  refine ⟨(Real.log 4+5)*eulerConstant, mul_pos (by positivity) eulerConstant_pos, ?_⟩
  intro G h L hL
  have hLL : 0 < Real.log L := log_pos (by exact_mod_cast (by omega : 1 < L))
  apply (le_div_iff₀ hLL).mpr
  rw [meanSum, sum_mul]
  calc
    _ ≤ ∑ n ∈ Icc 1 L, (G n * Real.log n + L * (G n / n)) := by
      apply sum_le_sum; intro n hn
      have hn0 : 0 < (n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
      have hL0 : 0 < (L:ℝ) := by exact_mod_cast (by omega : 0<L)
      have hd := log_le_sub_one_of_pos (div_pos hL0 hn0)
      rw [log_div hL0.ne' hn0.ne'] at hd
      have hb : Real.log L ≤ Real.log n + (L:ℝ)/n := by linarith
      convert mul_le_mul_of_nonneg_left hb (h.nonneg n) using 1; ring
    _ ≤ (Real.log 4+5)*L*harmonicSum G L := by
      rw [sum_add_distrib, ← mul_sum, ← harmonicSum]
      linarith [log_mean_le h L, show (Real.log 4+5)*(L:ℝ)*harmonicSum G L =
        (Real.log 4+4)*L*harmonicSum G L + L*harmonicSum G L by ring]
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left (harmonic_le_euler h L)
        (show 0 ≤ (Real.log 4+5)*(L:ℝ) by positivity) using 1; ring

end ErdosSuranyi708
