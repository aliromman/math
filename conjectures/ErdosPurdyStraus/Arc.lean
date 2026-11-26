module

public import conjectures.ErdosPurdyStraus.Normalized
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace ErdosPurdyStraus
open Set

/-- Squared circle radius and height where the two conjugate heights agree. -/
def radiusSq (t : ℝ) := 1+t^2
def middle (t : ℝ) := (1+t)^2/2
def slope (t : ℝ) := 1+2*t/radiusSq t
def partner (t x : ℝ) := Real.sqrt (radiusSq t-x^2)

/-- Continue the circular arc to the left by its tangent at t. -/
def roof (t x : ℝ) := partner t (max t x)+t*(max t x-x)

def width (t x : ℝ) := 2*roof t x/radiusSq t-|1-slope t*x|

theorem parameter_unique : ∃! t, Parameter t := by
  let g (x : ℝ) := x^4+4*x^3+4*x^2+4*x-1
  have cont : Continuous g := by unfold g; fun_prop
  obtain ⟨t,⟨ht0,ht1⟩,hz⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1/4)
    cont.continuousOn (show (0:ℝ)∈Icc (g 0) (g (1/4)) by norm_num [g])
  have ht : Parameter t := by
    refine ⟨lt_of_le_of_ne ht0 ?_,lt_of_le_of_ne ht1 ?_,?_⟩
    · rintro rfl; norm_num [g] at hz
    · rintro rfl; norm_num [g] at hz
    · dsimp [g] at hz; linarith only [hz]
  have strict {a b : ℝ} (ha : 0≤a) (hab : a<b) : g a<g b := by
    dsimp [g]
    linarith only [pow_le_pow_left₀ ha hab.le 4,pow_le_pow_left₀ ha hab.le 3,
      pow_le_pow_left₀ ha hab.le 2,hab]
  refine ⟨t,ht,fun y hy ↦ ?_⟩
  have zero : g y=0 := by dsimp [g]; linarith only [hy.2.2]
  rcases lt_trichotomy y t with h|h|h
  · linarith only [zero,hz,strict hy.1.le h]
  · exact h
  · linarith only [zero,hz,strict ht.1.le h]

variable {t x y : ℝ}

theorem radius_pos (t : ℝ) : 0<radiusSq t := by unfold radiusSq; positivity

theorem Parameter.mid_sq (ht : Parameter t) : 2*middle t^2=radiusSq t := by
  unfold middle radiusSq
  linarith only [ht.2.2]

theorem Parameter.mid_mem (ht : Parameter t) : middle t∈Icc t 1 := by
  have t1 : t^2≤1 := by simpa using pow_le_pow_left₀ ht.1.le (show t≤1 by linarith [ht.2.1]) 2
  have p : 0<middle t := by unfold middle; positivity [ht.1]
  constructor
  · unfold middle; nlinarith only [sq_nonneg t]
  · have := ht.mid_sq; unfold radiusSq at this; nlinarith

theorem Parameter.slope_pos (ht : Parameter t) : 0<slope t := by
  unfold slope
  positivity [ht.1,radius_pos t]

theorem Parameter.slope_mid (ht : Parameter t) : slope t * middle t=1 := by
  have h : 2*middle t=radiusSq t+2*t := by unfold middle radiusSq; ring
  unfold slope
  field_simp [(radius_pos t).ne']
  linarith only [ht.mid_sq,congrArg (middle t * ·) h]

theorem Parameter.partner_sq (_ht : Parameter t) (hx : x∈Icc 0 1) :
    partner t x ^ 2=radiusSq t-x^2 := by
  have xx : x^2≤1 := by simpa using pow_le_pow_left₀ hx.1 hx.2 2
  exact Real.sq_sqrt (by unfold radiusSq; linarith [sq_nonneg t])

theorem partner_nn (t x : ℝ) : 0≤partner t x := Real.sqrt_nonneg _

theorem Parameter.partner_mem (ht : Parameter t) (hx : x∈Icc t 1) : partner t x∈Icc t 1 := by
  have hx' : x∈Icc 0 1 := ⟨ht.1.le.trans hx.1,hx.2⟩
  have p := ht.partner_sq hx'
  unfold radiusSq at p
  refine ⟨(sq_le_sq₀ ht.1.le (partner_nn ..)).mp ?_,(sq_le_sq₀ (partner_nn ..) zero_le_one).mp ?_⟩
  · nlinarith only [p,pow_le_pow_left₀ hx'.1 hx.2 2]
  · nlinarith only [p,pow_le_pow_left₀ ht.1.le hx.1 2]

theorem Parameter.partner_self (ht : Parameter t) (hx : x∈Icc 0 1) : partner t (partner t x)=x := by
  change Real.sqrt (radiusSq t-(partner t x)^2)=x
  rw [ht.partner_sq hx,sub_sub_cancel,Real.sqrt_sq hx.1]

theorem Parameter.partner_low (_ht : Parameter t) : partner t t=1 := by simp [partner,radiusSq]

theorem Parameter.partner_high (ht : Parameter t) : partner t 1=t := by
  simp [partner,radiusSq,Real.sqrt_sq ht.1.le]

theorem roof_high (hx : t≤x) : roof t x=partner t x := by simp [roof,max_eq_right hx]

theorem Parameter.roof_low (ht : Parameter t) (hx : x≤t) : roof t x=radiusSq t-t*x := by
  rw [roof,max_eq_left hx,ht.partner_low]; unfold radiusSq; ring

theorem Parameter.width_low (ht : Parameter t) (hx : x≤t) : width t x=1+x := by
  have hx' := mul_le_mul_of_nonneg_left (hx.trans ht.mid_mem.1) ht.slope_pos.le
  rw [ht.slope_mid] at hx'
  rw [width,ht.roof_low hx,abs_of_nonneg (sub_nonneg.mpr hx'),slope]
  field_simp [(radius_pos t).ne']
  ring

theorem Parameter.width_zero (ht : Parameter t) : width t 0=1 := by simpa using ht.width_low ht.1.le

theorem Parameter.width_one (ht : Parameter t) : width t 1=0 := by
  have t1 : t≤1 := by linarith [ht.2.1]
  have h := mul_le_mul_of_nonneg_left ht.mid_mem.2 ht.slope_pos.le
  rw [ht.slope_mid,mul_one] at h
  rw [width,roof_high t1,ht.partner_high,mul_one,abs_of_nonpos (sub_nonpos.mpr h),slope]
  ring

theorem width_continuous (t : ℝ) : Continuous (width t) := by
  unfold width roof partner; fun_prop (disch := positivity)

end ErdosPurdyStraus
end
