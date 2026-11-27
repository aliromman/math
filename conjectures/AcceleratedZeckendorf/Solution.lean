module

public import conjectures.AcceleratedZeckendorf.Expectation
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace AcceleratedZeckendorf
open Filter
open scoped Topology

noncomputable def widthConstant : ℝ := 2*(1 / Real.log 2+1)
noncomputable def lengthConstant : ℝ := 18*widthConstant*(2*widthConstant+6)

theorem cubic_log_bound (n : ℕ) (hn : 1≤Real.log (1+5*(n:ℝ))) :
    mean n ≤ lengthConstant*Real.log (1+5*(n:ℝ))^3 := by
  let u := Real.log (1+5*(n:ℝ))
  have hlog : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0≤widthConstant := by dsimp [widthConstant]; positivity
  have hnat := Real.natLog_le_logb (n+1) 2
  simp only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Real.logb] at hnat
  have hm : Real.log ((n:ℝ)+1) ≤ u :=
    Real.log_le_log (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hw : (width n : ℝ) ≤ widthConstant*u := by
    have hd := hnat.trans (div_le_div_of_nonneg_right hm hlog.le)
    unfold width widthConstant
    push_cast
    dsimp only [u] at *
    linarith [show (1 / Real.log 2 + 1) * Real.log (1 + 5 * (n : ℝ)) =
      Real.log (1+5*(n:ℝ))/Real.log 2 + Real.log (1+5*(n:ℝ)) by ring]
  have hh : 2*(width n:ℝ)+6≤(2*widthConstant+6)*u := by
    change 1≤u at hn
    nlinarith
  have hu : 0≤u := le_trans zero_le_one hn
  calc
    mean n ≤ 2*(scale n:ℝ)*u := mean_bound n
    _ = 18*(width n:ℝ)*(2*(width n:ℝ)+6)*u := by unfold scale; push_cast; ring
    _ ≤ 18*(widthConstant*u)*((2*widthConstant+6)*u)*u := by gcongr
    _ = lengthConstant*u^3 := by unfold lengthConstant; ring

theorem resolution : Conjecture := by
  have hx : Tendsto (fun n : ℕ => 1+5*(n:ℝ)) atTop atTop :=
    tendsto_atTop_mono (f:=fun n : ℕ => (n:ℝ)) (fun n => by
      change (n:ℝ) ≤ 1+5*(n:ℝ)
      linarith [Nat.cast_nonneg (α:=ℝ) n]) tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hx
  have hu := (Real.tendsto_pow_log_div_mul_add_atTop (1/5) (-1/5) 3 (by norm_num)).comp hx
  have hb : Tendsto (fun n : ℕ => lengthConstant*Real.log (1+5*(n:ℝ))^3/(n:ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x:=lengthConstant)).mul hu
    convert h using 1
    · ext n; dsimp; ring_nf
    · simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · exact Eventually.of_forall fun n => div_nonneg (mean_nonneg n) (Nat.cast_nonneg n)
  · filter_upwards [hlog.eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_right (cubic_log_bound n hn) (Nat.cast_nonneg n)

/-- info: 'AcceleratedZeckendorf.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'AcceleratedZeckendorf.mean_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mean_bound

end AcceleratedZeckendorf
