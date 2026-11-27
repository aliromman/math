module

public import conjectures.ConsecutiveThreshold.Statement
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace ConsecutiveThreshold
open Filter
open scoped Topology

private theorem rescale {s : ℕ} (hs : 0<s) {x : ℝ} (hx : 0<x) (y : ℝ) :
    (y/x^(1-1/(s:ℝ)))^s=x*(y/x)^s := by
  have sp : (s:ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have exp : (1-1/(s:ℝ))*s=(s:ℝ)-1 := by field_simp
  have power : (x^(1-1/(s:ℝ)))^s=x^s/x := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx.le,exp,Real.rpow_sub_one hx.ne',Real.rpow_natCast]
  rw [div_pow,power,div_pow]
  field_simp

private theorem tilt_grows {s : ℕ} {m : ℕ → ℕ} (h : above s m) :
    Tendsto (fun n : ℕ => (n:ℝ)*((m n:ℝ)/(m n+n))^s) atTop atTop := by
  by_cases hs : s=0
  · subst s
    simpa using (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := h.resolve_left hs
  have hs' := Nat.pos_of_ne_zero hs
  have hc : 0 < (2:ℝ)^s := by positivity
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (b*2^s),
    ((tendsto_pow_atTop hs).comp h).eventually_ge_atTop (b*2^s)] with n hn large near
  have xn : (0:ℝ)<n := by exact_mod_cast hn
  have ym : 0≤(m n:ℝ) := by positivity
  change b*2^s ≤ ((m n:ℝ)/(n:ℝ)^(1-1/(s:ℝ)))^s at near
  rw [rescale hs' xn] at near
  by_cases low : (m n:ℝ)≤n
  · have u : ((m n:ℝ)/n)/2 ≤ (m n:ℝ)/(m n+n) := by
      rw [div_div]
      exact div_le_div_of_nonneg_left ym (by positivity) (by linarith)
    have v := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) u s) xn.le
    rw [div_pow,mul_div_assoc'] at v
    exact ((le_div_iff₀ hc).mpr near).trans v
  · have u : (1/2:ℝ) ≤ (m n:ℝ)/(m n+n) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    have v := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) u s) xn.le
    rw [one_div,inv_pow,←div_eq_mul_inv] at v
    exact ((le_div_iff₀ hc).mpr large).trans v

/-- The disjoint-block avoidance bound vanishes at the conjectured threshold. -/
theorem block_decay {k s : ℕ} (hk : 0<k) {m : ℕ → ℕ} (h : above s m) :
    Tendsto (fun n : ℕ => (1-((m n:ℝ)/(m n+n))^s/(k.factorial:ℝ))^((n/4)/k)) atTop (𝓝 0) := by
  let p (n : ℕ) := ((m n:ℝ)/(m n+n))^s / (k.factorial:ℝ)
  let B (n : ℕ) := n/4/k
  have kpos : (0:ℝ)<k := by exact_mod_cast hk
  have fac : (0:ℝ)<k.factorial := by positivity
  have grow : Tendsto (fun n : ℕ => ↑(B n)*p n) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ ((tilt_grows h).atTop_mul_const
      (show 0 < (8*(k:ℝ)*(k.factorial:ℝ))⁻¹ by positivity))
    filter_upwards [eventually_ge_atTop (4*k)] with n hn
    have bp : 1≤B n := by
      dsimp [B]
      rw [Nat.div_div_eq_div_mul]
      exact (Nat.le_div_iff_mul_le (by omega : 0<4*k)).2 (by simpa using hn)
    have length : n ≤ (8*k)*B n := by
      have u := Nat.lt_mul_div_succ n (show 0<4*k by omega)
      rw [← Nat.div_div_eq_div_mul] at u
      change n < 4*k*(B n+1) at u
      nlinarith only [u,Nat.mul_le_mul_left k bp]
    have l : (n:ℝ)≤8*(k:ℝ)*(B n:ℝ) := by exact_mod_cast length
    dsimp only [p]
    rw [←div_eq_mul_inv,mul_div_assoc']
    apply (div_le_div_iff₀ (by positivity) fac).mpr
    nlinarith only [mul_le_mul_of_nonneg_right l
      (show 0 ≤ ((m n:ℝ)/(m n+n))^s * (k.factorial:ℝ) by positivity)]
  have prob (n : ℕ) : p n≤1 := by
    have base : (m n:ℝ)/(m n+n)≤1 :=
      div_le_one_of_le₀ (le_add_of_nonneg_right (by positivity)) (by positivity)
    apply (div_le_one fac).2
    exact (pow_le_one₀ (by positivity) base).trans (by exact_mod_cast Nat.factorial_pos k)
  have empty := Real.tendsto_exp_neg_atTop_nhds_zero.comp grow
  change Tendsto (fun n => (1-p n)^(B n)) atTop (𝓝 0)
  apply squeeze_zero' (Eventually.of_forall fun n => pow_nonneg (sub_nonneg.mpr (prob n)) _) _ empty
  apply Eventually.of_forall
  intro n
  change (1-p n)^(B n)≤Real.exp (-((B n:ℝ)*p n))
  rw [←mul_neg,Real.exp_nat_mul]
  exact pow_le_pow_left₀ (sub_nonneg.mpr (prob n)) (by linarith [Real.add_one_le_exp (-p n)]) _

end ConsecutiveThreshold
