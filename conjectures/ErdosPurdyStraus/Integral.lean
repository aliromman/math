module

public import conjectures.ErdosPurdyStraus.Dual
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section
namespace ErdosPurdyStraus
open Set MeasureTheory intervalIntegral
open scoped Interval
variable {t : ℝ}

private theorem arc_integral (ht : Parameter t) :
    (∫ x in t..1,2*partner t x/radiusSq t)=Real.pi/2-2*Real.arctan t := by
  let F (x : ℝ) := x*partner t x/radiusSq t+Real.arctan (x/partner t x)
  have le := ht.mid_mem.1.trans ht.mid_mem.2
  have D (x : ℝ) (hx : x∈uIcc t 1) : HasDerivAt F (2*partner t x/radiusSq t) x := by
    rw [uIcc_of_le le] at hx
    have s := ht.partner_deriv hx
    have p := ht.1.trans_le (ht.partner_mem hx).1
    have sq := ht.partner_sq ⟨ht.1.le.trans hx.1,hx.2⟩
    have R := (radius_pos t).ne'
    have angle : HasDerivAt (fun x ↦ Real.arctan (x/partner t x)) (1/partner t x) x := by
      have q := ((hasDerivAt_id x).div s p.ne').arctan
      convert q using 1
      · rfl
      · change 1/partner t x=1/(1+(x/partner t x)^2)*((1*partner t x-x*(-x/partner t x))/partner t x^2)
        field_simp [p.ne']
        ring
    have z := (((hasDerivAt_id x).mul s).div_const (radiusSq t)).add angle
    convert z using 1
    · rfl
    · change 2*partner t x/radiusSq t=(1*partner t x+x*(-x/partner t x))/radiusSq t+1/partner t x
      field_simp [R,p.ne']
      linarith only [sq]
  have cont : Continuous (fun x ↦ 2*partner t x/radiusSq t) := by unfold partner; fun_prop
  rw [integral_eq_sub_of_hasDerivAt D (cont.intervalIntegrable ..)]
  simp only [F,ht.partner_low,ht.partner_high,one_mul,mul_one,div_one,one_div,Real.arctan_inv_of_pos ht.1]
  ring

private theorem cusp_integral (ht : Parameter t) :
    (∫ x in t..1,|1-slope t*x|)=2*middle t-1-t := by
  let m := middle t
  let a := slope t
  have mid : a*m=1 := ht.slope_mid
  have cont : Continuous (fun x ↦ |1-a*x|) := by fun_prop
  have line (u v : ℝ) : (∫ x in u..v,1-a*x) = v-u-a*((v^2-u^2)/2) := by
    rw [intervalIntegral.integral_sub (f:=fun _ : ℝ ↦ (1:ℝ)) (g:=fun x:ℝ ↦ a*x) intervalIntegrable_const ((by fun_prop : Continuous (fun x : ℝ ↦ a*x)).intervalIntegrable u v),
      integral_one,intervalIntegral.integral_const_mul,integral_id]
  have low : (∫ x in t..m,|1-a*x|)=∫ x in t..m,1-a*x := by
    apply integral_congr
    rw [uIcc_of_le ht.mid_mem.1]
    intro x hx
    apply abs_of_nonneg
    linarith only [mid,mul_le_mul_of_nonneg_left hx.2 ht.slope_pos.le]
  have high : (∫ x in m..1,|1-a*x|)= -(∫ x in m..1,1-a*x) := by
    rw [←intervalIntegral.integral_neg]
    apply integral_congr
    rw [uIcc_of_le ht.mid_mem.2]
    intro x hx
    apply abs_of_nonpos
    linarith only [mid,mul_le_mul_of_nonneg_left hx.1 ht.slope_pos.le]
  change (∫ x in t..1,|1-a*x|)=2*m-1-t
  rw [←integral_add_adjacent_intervals (cont.intervalIntegrable t m) (cont.intervalIntegrable m 1),low,high,line,line]
  have s : 2*m^2=1+t^2 := ht.mid_sq
  linarith only [congrArg (a * ·) s]

theorem Parameter.width_integral (ht : Parameter t) :
    2*(∫ x in (0:ℝ)..1,width t x)=Real.pi-4*Real.arctan t-t^2 := by
  have low : (∫ x in (0:ℝ)..t,width t x)=t+t^2/2 := by
    calc
      _ = ∫ x in (0:ℝ)..t,1+x := integral_congr fun x hx ↦ ht.width_low ((uIcc_of_le ht.1.le ▸ hx).2)
      _ = _ := by rw [intervalIntegral.integral_add (f:=fun _ : ℝ ↦ (1:ℝ)) (g:=fun x : ℝ ↦ x) intervalIntegrable_const (continuous_id.intervalIntegrable ..),integral_one,integral_id]; ring
  have h : t≤1 := ht.mid_mem.1.trans ht.mid_mem.2
  have c : Continuous (fun x ↦ 2*partner t x/radiusSq t) := by unfold partner; fun_prop
  have high : (∫ x in t..1,width t x) = (Real.pi/2-2*Real.arctan t)-(2*middle t-1-t) := by
    calc
      _ = ∫ x in t..1,2*partner t x/radiusSq t-|1-slope t*x| := by
        apply integral_congr
        rw [uIcc_of_le h]
        intro x hx; rw [width,roof_high hx.1]
      _ = _ := by rw [integral_sub (c.intervalIntegrable ..) ((by fun_prop : Continuous (fun x ↦ |1-slope t*x|)).intervalIntegrable ..),arc_integral ht,cusp_integral ht]
  rw [←integral_add_adjacent_intervals ((width_continuous t).intervalIntegrable 0 t) ((width_continuous t).intervalIntegrable t 1),low,high]
  unfold middle
  ring

end ErdosPurdyStraus
