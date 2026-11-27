module

public import conjectures.BilleyFahrbachTalmageClassification.Kernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A bound for the binomial tail after one gap

Above the truncation index, the absolute values of the weighted binomial
coefficients telescope. The difference of two powers supplies the weight. -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Finset Filter Set
open scoped Topology

private theorem choose_first (s : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * Ring.choose s (k + 1) = s * Ring.choose (s - 1) k := by
  simpa [Nat.choose_one_right, nsmul_eq_mul] using
    (Ring.choose_smul_choose s (n := k+1) (k := 1) (by omega))

private theorem choose_last (s : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * Ring.choose s (k+1) = Ring.choose s k * (s-k) := by
  simpa [Nat.choose_succ_self_right, nsmul_eq_mul] using
    (Ring.choose_smul_choose s (Nat.le_succ k))

private theorem tail_coefficient (s : ℝ) (k : ℕ) (hs : 1 ≤ s) (hk : s ≤ k + 2) :
    (k+2 : ℝ) * |Ring.choose s (k+2)| =
      s * (|Ring.choose (s-2) k| - |Ring.choose (s-2) (k+1)|) := by
  have h₁ := congrArg abs (choose_first s (k+1))
  have h₂ := congrArg abs (choose_first (s-1) k)
  have h₃ := congrArg abs (choose_last (s-2) k)
  rw [show s-1-1=s-2 by ring] at h₂
  simp only [abs_mul, Nat.cast_succ, abs_of_nonneg (by positivity : 0 ≤ (k:ℝ)+1+1),
    abs_of_nonneg (by positivity : 0 ≤ (k:ℝ)+1), abs_of_nonneg (by linarith : 0 ≤ s),
    abs_of_nonneg (by linarith : 0 ≤ s-1), abs_of_nonpos (by linarith : s-2-k ≤ 0)] at h₁ h₂ h₃
  apply mul_left_cancel₀ (a := (k:ℝ)+1) (by positivity)
  linear_combination ((k:ℝ)+1)*h₁ + s*h₂ + s*h₃

/-- The difference of two powers, divided by the exponent, decreases with the exponent. -/
theorem power_difference (s t : ℝ) (hs : 1 ≤ s) (hst : s ≤ t)
    {v u : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1) :
    s * (u^t-v^t) ≤ t * (u^s-v^s) := by
  let f (x : ℝ) := t*x^s - s*x^t
  have hd (x : ℝ) : HasDerivAt f (t*(s*x^(s-1)) - s*(t*x^(t-1))) x :=
    ((Real.hasDerivAt_rpow_const (Or.inr hs)).const_mul t).sub
      ((Real.hasDerivAt_rpow_const (Or.inr (hs.trans hst))).const_mul s)
  have hm : MonotoneOn f (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => (hd x).hasDerivWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hh := Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le (by linarith : s-1 ≤ t-1)
    nlinarith only [mul_nonneg (mul_nonneg (show 0≤s by linarith) (show 0≤t by linarith)) (sub_nonneg.mpr hh)]
  have h := hm ⟨hv, hvu.trans hu⟩ ⟨hv.trans hvu, hu⟩ hvu
  dsimp [f] at h
  linarith

private noncomputable def term (s u v : ℝ) (j : ℕ) : ℝ :=
  (-1)^j * Ring.choose s j * (u^j-v^j)

private theorem tail_term (s : ℝ) (k : ℕ) (hs : 1 ≤ s) (hk : s ≤ k+2)
    {v u : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1) :
    |term s u v (k+2)| ≤
      (|Ring.choose (s-2) k| - |Ring.choose (s-2) (k+1)|) * (u^s-v^s) := by
  have d := power_difference s (k+2 : ℕ) hs (by exact_mod_cast hk) hv hvu hu
  rw [Real.rpow_natCast, Real.rpow_natCast] at d
  push_cast at d
  have hpow : 0 ≤ u^(k+2) - v^(k+2) := sub_nonneg.mpr (pow_le_pow_left₀ hv hvu _)
  simp only [term, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hpow]
  apply (mul_le_mul_iff_right₀ (by linarith : 0 < s)).mp
  calc
    _ = |Ring.choose s (k+2)| * (s * (u^(k+2)-v^(k+2))) := by ring
    _ ≤ |Ring.choose s (k+2)| * (((k:ℝ)+2) * (u^s-v^s)) :=
      mul_le_mul_of_nonneg_left d (abs_nonneg _)
    _ = _ := by rw [← mul_assoc, mul_comm |Ring.choose s (k+2)|, tail_coefficient s k hs hk]; ring

private theorem power_series (s : ℝ) {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    HasSum (fun j : ℕ => Ring.choose s j * (-x)^j) ((1-x)^s) := by
  have hm : -x ∈ Metric.eball (0 : ℝ) 1 := by
    rwa [← ENNReal.ofReal_one, Metric.eball_ofReal, Metric.mem_ball, dist_zero_right,
      norm_neg, Real.norm_eq_abs, abs_of_nonneg hx₀]
  simpa only [binomialSeries_apply, List.ofFn_const, List.prod_replicate,
    smul_eq_mul, zero_add, sub_eq_add_neg] using
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := s)).hasSum hm

private theorem real_tail_interior {s u v : ℝ} (n : ℕ) (hs : 1 ≤ s) (hn : s ≤ n+2)
    (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u < 1) :
    |(1-u)^s - (1-v)^s - ∑ j ∈ range (n+2), term s u v j| ≤
      |Ring.choose (s-2) n| * (u^s-v^s) := by
  have hsum : HasSum (term s u v) ((1-u)^s-(1-v)^s) := by
    have h := (power_series s (hv.trans hvu) hu).sub (power_series s hv (hvu.trans_lt hu))
    convert h using 1
    funext j
    simp only [term, ← neg_one_mul u, ← neg_one_mul v, mul_pow]
    ring
  have hd : 0 ≤ u^s - v^s := sub_nonneg.mpr (Real.rpow_le_rpow hv hvu (by linarith))
  let b (i : ℕ) := |Ring.choose (s-2) (i+n)|
  apply le_of_tendsto' ((hasSum_nat_add_iff' (n+2)).mpr hsum).tendsto_sum_nat.abs
  intro N
  calc
    _ ≤ ∑ i ∈ range N, |term s u v (i+(n+2))| := abs_sum_le_sum_abs ..
    _ ≤ ∑ i ∈ range N, (b i - b (i+1)) * (u^s-v^s) := by
      apply sum_le_sum
      intro i _
      have h := tail_term s (i+n) hs (by push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]) hv hvu hu.le
      simpa only [b, Nat.add_assoc, Nat.add_comm 1 n] using h
    _ = (b 0 - b N) * (u^s-v^s) := by rw [← sum_mul, sum_range_sub']
    _ ≤ _ := by
      gcongr
      dsimp [b]
      rw [Nat.zero_add]
      exact sub_le_self _ (abs_nonneg _)

private theorem real_tail {s u v : ℝ} (n : ℕ) (hs : 1 ≤ s) (hn : s ≤ n+2)
    (hv : 0 ≤ v) (hv₁ : v < 1) (hvu : v ≤ u) (hu : u ≤ 1) :
    |(1-u)^s - (1-v)^s - ∑ j ∈ range (n+2), term s u v j| ≤
      |Ring.choose (s-2) n| * (u^s-v^s) := by
  have hc : Continuous (fun x : ℝ => x^s) := Real.continuous_rpow_const (by linarith)
  have hleft : Continuous (fun x : ℝ => |(1-x)^s - (1-v)^s -
      ∑ j ∈ range (n+2), term s x v j|) := by
    unfold term
    fun_prop (disch := linarith)
  have hright : Continuous (fun x : ℝ => |Ring.choose (s-2) n| * (x^s-v^s)) :=
    continuous_const.mul (hc.sub continuous_const)
  apply ContinuousWithinAt.closure_le (s := Set.Ico v 1) (x := u) _
    hleft.continuousAt.continuousWithinAt hright.continuousAt.continuousWithinAt
  · intro x hx
    exact real_tail_interior n hs hn hv hx.1 hx.2
  · rw [closure_Ico hv₁.ne]
    exact ⟨hvu, hu⟩

private theorem parity_sign (n j : ℕ) (hj : j ≤ n) :
    (-1 : ℂ)^(n-j) = (-1)^n * (-1)^j := by
  have he := pow_add (-1:ℂ) (n-j) j
  rw [Nat.sub_add_cancel hj] at he
  rw [he]
  rcases neg_one_pow_eq_or ℂ j with h|h <;> simp [h]

private theorem real_gap_error (n : ℕ) (s y u v : ℝ)
    (hu : u = (1+y)/2) (hv : v = (1-y)/2) (hu₀ : 0 ≤ u) (hv₀ : 0 ≤ v) :
    gapKernel [n+2] (s : ℂ) y + difference (s : ℂ) y =
      (-1 : ℂ)^(n+1) * (((u^s-v^s) + ∑ j ∈ range (n+2), term s u v j : ℝ) : ℂ) := by
  let d := difference (s:ℂ) y
  have dd : d = ((u^s-v^s : ℝ) : ℂ) := by
    simp only [d, difference, ← hu, ← hv, Complex.ofReal_sub, Complex.ofReal_cpow hu₀, Complex.ofReal_cpow hv₀]
  have dj (j : ℕ) : difference (j:ℂ) y = ((u^j-v^j : ℝ) : ℂ) := by
    simp only [difference, ← hu, ← hv, Complex.cpow_natCast, Complex.ofReal_sub, Complex.ofReal_pow]
  have zeroTerm : term s u v 0 = 0 := by simp [term]
  have ds : (if Even (n+2) then -2*d else 0) + d = (-1:ℂ)^(n+1)*d := by
    by_cases hh : Even (n+2)
    · have hodd : Odd (n+1) := by rw [Nat.even_iff] at hh; rw [Nat.odd_iff]; omega
      rw [ite_eq_left hh, hodd.neg_one_pow]; ring
    · have hev : Even (n+1) := by rw [Nat.even_iff] at hh ⊢; omega
      rw [ite_eq_right hh, hev.neg_one_pow]; ring
  have summ : (∑ j ∈ Finset.Ico 1 (n+2), (-1:ℂ)^(n+1-j) *
      Ring.choose (s:ℂ) j * difference (j:ℂ) y) =
      (-1:ℂ)^(n+1) * ((∑ j ∈ range (n+2), term s u v j : ℝ) : ℂ) := by
    calc
      _ = ∑ j ∈ Finset.Ico 1 (n+2), (-1:ℂ)^(n+1) * (term s u v j : ℂ) := by
        apply sum_congr rfl
        intro j hj
        rw [parity_sign _ _ (by have := (mem_Ico.mp hj).2; omega), dj]
        simp only [term, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_choose]
        ring
      _ = _ := by
        rw [← mul_sum, sum_Ico_eq_sub _ (by omega), sum_range_one, zeroTerm, Complex.ofReal_zero, sub_zero]
        push_cast
        rfl
  simp only [gapKernel, applyGaps, gapStep, Nat.zero_add]
  change ((if Even (n+2) then -2*d else 0) +
    ∑ j ∈ Finset.Ico 1 (n+2), (-1:ℂ)^(n+1-j) * Ring.choose (s:ℂ) j * difference (j:ℂ) y) + d = _
  rw [summ, add_right_comm, ds, dd, Complex.ofReal_add, mul_add]

/-- The error after one gap is bounded uniformly for the two sides of the valley. -/
theorem single_gap_error {h : ℕ} (hh : 10 ≤ h) {s y : ℝ}
    (hs₀ : (h:ℝ)-3 ≤ s) (hs₁ : s ≤ (h:ℝ)-1) (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) :
    ‖gapKernel [h] (s:ℂ) y + difference (s:ℂ) y‖ ≤
      |Ring.choose (s-2) (h-2)| * ‖difference (s:ℂ) y‖ := by
  let n := h-2
  let u := (1+y)/2
  let v := (1-y)/2
  have hh' : h=n+2 := by dsimp [n]; omega
  have hn : (s:ℝ) ≤ n+2 := by rw [hh'] at hs₁; push_cast at hs₁; linarith
  have hs : 1 ≤ s := by
    have : (10:ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hv₀ : 0 ≤ v := by dsimp [v]; linarith
  have hv₁ : v < 1 := by dsimp [v]; linarith
  have huv : v ≤ u := by dsimp [u,v]; linarith
  have hu₁ : u ≤ 1 := by dsimp [u]; linarith
  have hh₀ := real_tail n hs hn hv₀ hv₁ huv hu₁
  have hv : 1-u=v := by dsimp [u,v]; ring
  have hu : 1-v=u := by dsimp [u,v]; ring
  have he := real_gap_error n s y u v rfl rfl (hv₀.trans huv) hv₀
  rw [hh', he, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Nat.add_sub_cancel]
  have dd : difference (s:ℂ) y = ((u^s-v^s : ℝ) : ℂ) := by
    simp only [difference, Complex.ofReal_sub, Complex.ofReal_cpow (hv₀.trans huv), Complex.ofReal_cpow hv₀, u, v]
  rw [dd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hv₀ huv (by linarith)))]
  rw [hv, hu, show v^s-u^s - ∑ j ∈ range (n+2), term s u v j =
    -((u^s-v^s) + ∑ j ∈ range (n+2), term s u v j) by ring, abs_neg] at hh₀
  exact hh₀

end BilleyFahrbachTalmageClassification
