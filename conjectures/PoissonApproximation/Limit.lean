module

public import conjectures.PoissonApproximation.Cumulative
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace PoissonApproximation
open Filter Set Real ProbabilityTheory
open scoped Topology

private theorem log_second_order :
    Tendsto (fun t : ℝ ↦ (log (1-t)+t)/t^2) (𝓝[>]0) (𝓝 (-1/2)) := by
  apply HasDerivAt.lhopital_zero_right_on_Ico (b := 1) (by norm_num)
    (f' := fun t ↦ -t/(1-t)) (g' := fun t ↦ 2*t)
  · intro t h
    have p : 0<1-t := sub_pos.mpr h.2
    convert ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log p.ne').add (hasDerivAt_id t)) using 1
    · rfl
    · dsimp; field_simp; ring
  · intro t _
    convert (hasDerivAt_id t).pow 2 using 1
    · rfl
    · simp
  · apply ContinuousOn.add _ continuousOn_id
    exact (continuousOn_const.sub continuousOn_id).log fun t h ↦ (sub_pos.mpr h.2).ne'
  · fun_prop
  · intro t h
    exact mul_ne_zero (by norm_num) h.1.ne'
  · simp
  · simp
  · have simple : Tendsto (fun t : ℝ ↦ -1/(2*(1-t))) (𝓝[>]0) (𝓝 (-1/2)) := by
      have C : ContinuousAt (fun t : ℝ ↦ -1/(2*(1-t))) 0 := by fun_prop (disch := norm_num)
      simpa using (C.continuousWithinAt (s:=Ioi 0)).tendsto
    apply simple.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ne : t≠0 := ht.ne'
    field_simp

/-- The first-order error requested after equation (84). -/
theorem scaled_limit :
    Tendsto (fun k : ℕ ↦ (k+2:ℝ) *
      distance (binomial (k+2) (parameter (k+2) (by omega) 1)) (poissonMeasure 1))
      atTop (𝓝 (1/(2*exp 1))) := by
  let t (k : ℕ) : ℝ := 1/(k+2:ℝ)
  let w (k : ℕ) := (log (1-t k)+t k)/(t k)^2
  let z (k : ℕ) := t k*w k
  have tpos (k : ℕ) : 0<t k := by dsimp [t]; positivity
  have tsmall (k : ℕ) : t k<1 := (div_lt_one (by positivity : (0:ℝ)<k+2)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) k])
  have lt0 : Tendsto t atTop (𝓝[>]0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall tpos⟩
    exact Filter.Tendsto.const_div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop) 1
  have wlim : Tendsto w atTop (𝓝 (-1/2)) := log_second_order.comp lt0
  have zlim : Tendsto z atTop (𝓝 0) := by
    simpa using (tendsto_nhds_of_tendsto_nhdsWithin lt0).mul wlim
  have neq (k : ℕ) : z k≠0 := by
    have L := Real.log_lt_sub_one_of_pos (sub_pos.mpr (tsmall k)) (by linarith [tpos k] : 1-t k≠1)
    dsimp [z,w]
    exact mul_ne_zero (tpos k).ne' (div_ne_zero (by linarith) (pow_ne_zero _ (tpos k).ne'))
  have ez := ((Real.hasDerivAt_exp 0).tendsto_slope_zero).comp
    (tendsto_nhdsWithin_iff.mpr ⟨zlim,Eventually.of_forall (fun k ↦ (mem_compl_singleton_iff.mpr (neq k)))⟩)
  have el : Tendsto (fun k ↦ (exp (z k)-1)/(z k)) atTop (𝓝 1) := by
    simpa [Function.comp_def,div_eq_inv_mul] using ez
  have H := (wlim.mul el).const_mul (-(exp (-1)))
  have target : -(exp (-1)) * ((-1/2:ℝ)*1) = 1/(2*exp 1) := by rw [exp_neg]; ring
  rw [target] at H
  apply H.congr
  intro k
  have formula : distance (binomial (k+2) (parameter (k+2) (by omega) 1)) (poissonMeasure 1) =
      exp (-1) - (1-1/(k+2 : ℕ))^(k+2) := by
    convert many_trials (k+2) (by omega) 1 using 3
    congr 1
  rw [formula]
  have qp : 0<1-t k := sub_pos.mpr (tsmall k)
  have wtz : z k=(k+2:ℝ)*log (1-t k)+1 := by
    dsimp [z,w,t]
    field_simp
  have power : (1-t k)^(k+2)=exp (-1) * exp (z k) := by
    rw [←Real.exp_add,wtz,show (-1:ℝ)+((k+2:ℝ)*log (1-t k)+1)=(k+2:ℕ)*log (1-t k) by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log qp]
  push_cast
  change _ = (k+2:ℝ)*(exp (-1)-(1-t k)^(k+2))
  rw [power]
  have nz := neq k
  have zz : z k*(k+2:ℝ)=w k := by dsimp only [z,t]; field_simp
  field_simp
  rw [←zz]
  ring

end PoissonApproximation
