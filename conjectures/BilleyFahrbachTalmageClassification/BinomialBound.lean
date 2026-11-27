module

public import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace BilleyFahrbachTalmageClassification

/-- The binomial power series in one complex variable. -/
theorem hasSum_choose_pow {x : ℂ} (a : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * x^n) ((1+x)^a) := by
  have hm : x ∈ Metric.eball (0 : ℂ) 1 := by
    rwa [← ENNReal.ofReal_one, Metric.eball_ofReal, Metric.mem_ball, dist_zero_right]
  simpa only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul, zero_add] using
    (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum hm

theorem peak_choose_succ (a : ℂ) (n : ℕ) :
    Ring.choose a (n+1) = Ring.choose a n * (a-n)/(n+1) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose a (n+1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_natCast, Ring.descPochhammer_eq_factorial_smul_choose,
    Nat.factorial_succ] at h
  simp only [nsmul_eq_mul, pow_one, pow_zero, mul_one, Nat.cast_mul, Nat.cast_succ] at h
  apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero n : (n : ℂ) + 1 ≠ 0)).mpr
  apply mul_left_cancel₀ (a := (n.factorial : ℂ)) (by exact_mod_cast Nat.factorial_ne_zero n)
  linear_combination -h

/-- The complex point used to test real-rootedness. -/
noncomputable def peakTestPoint : ℂ := ⟨1,5/2⟩

private theorem norm_cc {x y a : ℝ} (ha : 0 ≤ a) (h : x*x+y*y ≤ a*a) :
    ‖(⟨x,y⟩ : ℂ)‖ ≤ a := by
  apply (sq_le_sq₀ (norm_nonneg _) ha).mp
  rw [Complex.sq_norm,Complex.normSq_apply]
  simpa only [pow_two] using h

private theorem norm_choose_test (n : ℕ) : ‖Ring.choose peakTestPoint n‖ ≤ 4 := by
  have h1 : ‖peakTestPoint‖ ≤ 3 := norm_cc (by norm_num) (by norm_num)
  have hsub : ‖peakTestPoint-1‖ ≤ 5/2 := by
    change ‖(⟨1-1,(5:ℝ)/2-0⟩:ℂ)‖ ≤ 5/2
    exact norm_cc (by norm_num) (by norm_num)
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simpa using h1.trans (by norm_num : (3:ℝ) ≤ 4)
    | succ n ih =>
      rw [peak_choose_succ, norm_div, norm_mul]
      have hrate : ‖peakTestPoint - ((n+1:ℕ) : ℂ)‖ ≤ (n:ℝ)+2 ∨ n = 0 := by
        by_cases hn : n = 0
        · exact Or.inr hn
        · left
          apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
          rw [Complex.sq_norm, Complex.normSq_apply]
          norm_num [Complex.sub_re, Complex.sub_im, peakTestPoint]
          have hl : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
          nlinarith
      rcases hrate with h | rfl
      · have hp : ‖((n+1 : ℕ) : ℂ) + 1‖ = (n:ℝ)+2 := by
          rw [show ((n+1:ℕ):ℂ)+1 = ((n+2:ℕ):ℂ) by push_cast; ring, Complex.norm_natCast]
          push_cast
          ring
        rw [hp]
        apply (div_le_iff₀ (by positivity)).mpr
        exact mul_le_mul ih h (norm_nonneg _) (by norm_num)
      · norm_num [Complex.norm_ofNat] at *
        nlinarith [mul_le_mul h1 hsub (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 3)]

noncomputable def truncTest (N : ℕ) (x : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, Ring.choose peakTestPoint n * x ^ n

/-- The discarded binomial tail has a uniform geometric bound on the closed half disk. -/
theorem truncTest_error (N : ℕ) {x : ℂ} (hx : ‖x‖ ≤ 1/2) :
    ‖(1+x)^peakTestPoint - truncTest N x‖ ≤ 8 * ‖x‖^N := by
  have hs := hasSum_choose_pow peakTestPoint (lt_of_le_of_lt hx (by norm_num))
  have he := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at he
  have he' : (1+x)^peakTestPoint - truncTest N x =
      ∑' i : ℕ, Ring.choose peakTestPoint (i+N) * x^(i+N) := by
    unfold truncTest
    rw [← he]
    abel
  rw [he']
  apply tsum_of_norm_bounded (g := fun i : ℕ => (4*‖x‖^N) * (1/2:ℝ)^i)
  · convert (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left (4*‖x‖^N) using 1
    norm_num
    ring
  · intro i
    rw [norm_mul, norm_pow, pow_add]
    calc _ ≤ 4 * ((1/2:ℝ)^i * ‖x‖^N) := by
           gcongr
           exact norm_choose_test _
         _ = _ := by ring

end BilleyFahrbachTalmageClassification
