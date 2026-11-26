module

public import conjectures.CampbellCoupons.Frontier
public import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace CampbellCoupons
open Real Filter Set
open scoped Topology

private noncomputable def defect (t : ℝ) : ℝ := (t-log (1+t))/t^2

private theorem log_limit : Tendsto defect (𝓝[>]0) (𝓝 (1/2)) := by
  apply HasDerivAt.lhopital_zero_right_on_Ico (b := 1) (by norm_num)
    (f' := fun t => t/(1+t)) (g' := fun t => 2*t)
  · intro t h
    have p : 0<1+t := by linarith [h.1]
    convert (hasDerivAt_id t).sub (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).log p.ne') using 1
    · rfl
    · dsimp; field_simp; ring
  · intro t _
    convert (hasDerivAt_id t).pow 2 using 1
    · rfl
    · simp
  · apply ContinuousOn.sub continuousOn_id
    exact (continuousOn_const.add continuousOn_id).log fun t h => by
      change 1+t ≠ 0
      linarith [h.1]
  · fun_prop
  · intro t h
    exact mul_ne_zero (by norm_num) h.1.ne'
  · simp
  · simp
  · have simple : Tendsto (fun t : ℝ => 1/(2*(1+t))) (𝓝[>]0) (𝓝 (1/2)) := by
      have C : ContinuousAt (fun t : ℝ => 1/(2*(1+t))) 0 := by fun_prop (disch := norm_num)
      simpa using (C.continuousWithinAt (s := Ioi 0)).tendsto
    apply simple.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ne : t ≠ 0 := ht.ne'
    field_simp

private theorem exp_defect {k : ℕ} (hk : 0 < k) :
    exp (defect (1/(k:ℝ))) = (exp 1)^k * ((k:ℝ)/(k+1))^(k*k) := by
  have hp : (0:ℝ) < k := by exact_mod_cast hk
  have he : defect (1/(k:ℝ)) = (k : ℝ)*1 - ((k*k : ℕ) : ℝ)*log (((k:ℝ)+1)/k) := by
    have h : (1:ℝ)+1/k=(k+1)/k := by field_simp
    unfold defect
    rw [h]
    push_cast
    field_simp
  rw [he, exp_sub, exp_nat_mul, exp_nat_mul, exp_log (by positivity)]
  rw [div_pow, div_pow]
  field_simp

/-- The ratio grows as the square root of k, with an explicit leading constant. -/
theorem square_frontier_limit :
    Tendsto (fun k : ℕ => ratio k / √(k:ℝ)) atTop (𝓝 (exp (1/2) / (√2 * √π))) := by
  have tlim : Tendsto (fun k : ℕ => 1/(k:ℝ)) atTop (𝓝[>]0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_natCast_atTop_atTop.const_div_atTop 1, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact one_div_pos.mpr (by exact_mod_cast hk)
  have expLimit := Real.continuous_exp.continuousAt.tendsto.comp (log_limit.comp tlim)
  have plusLimit := tendsto_const_nhds (x := (1:ℝ)) |>.add (tendsto_nhds_of_tendsto_nhdsWithin tlim)
  have H := (plusLimit.mul expLimit).div
    (Stirling.tendsto_stirlingSeq_sqrt_pi.const_mul (√2)) (by positivity)
  simp only [add_zero, one_mul] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hp : (0:ℝ) < k := by exact_mod_cast hk
  change (1+1/(k:ℝ))*exp (defect (1/(k:ℝ))) / (√2 * Stirling.stirlingSeq k) = _
  rw [exp_defect hk, Stirling.stirlingSeq, Real.sqrt_mul (by norm_num : (0:ℝ)≤2),
    ratio_formula hk, div_pow (k:ℝ) (exp 1)]
  have hs := Real.mul_self_sqrt hp.le
  field_simp
  nlinarith

theorem unbounded_ratio : Tendsto ratio atTop atTop := by
  have H := Filter.Tendsto.pos_mul_atTop (by positivity) square_frontier_limit
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply H.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact div_mul_cancel₀ _ (by positivity)

end CampbellCoupons
