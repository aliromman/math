module

public import conjectures.ErdosPurdyStraus.Arc
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section
namespace ErdosPurdyStraus
open Set
variable {t x y z u : ℝ}

/-- Every tangent to the upper circular arc also supports its linear continuation. -/
private theorem support (ht : Parameter t) (hx : x∈Icc 0 1) (hu : u∈Icc t 1) :
    roof t x * partner t u + x*u ≤ radiusSq t := by
  have gu := ht.partner_sq ⟨ht.1.le.trans hu.1,hu.2⟩
  have gu1 := (ht.partner_mem hu).2
  by_cases h : t≤x
  · rw [roof_high h]
    linarith only [ht.partner_sq hx,gu,sq_nonneg (x-u),sq_nonneg (partner t x-partner t u)]
  · rw [ht.roof_low (le_of_not_ge h)]
    have low := ht.partner_sq ⟨ht.1.le,ht.mid_mem.1.trans ht.mid_mem.2⟩
    rw [ht.partner_low] at low
    have first : partner t u+t*u ≤ radiusSq t := by
      linarith only [low,gu,sq_nonneg (t-u),sq_nonneg (1-partner t u)]
    have p : 0≤u-t*partner t u := by nlinarith only [hu.1,mul_le_mul_of_nonneg_left gu1 ht.1.le]
    nlinarith only [first,mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) p,
      congrArg (· * partner t u) low]

private theorem tangent_at (ht : Parameter t) (hx : x∈Icc 0 1) :
    roof t x * partner t (max t x) + x*(max t x)=radiusSq t := by
  by_cases h : t≤x
  · rw [max_eq_right h,roof_high h]; nlinarith only [ht.partner_sq hx]
  · rw [max_eq_left (le_of_not_ge h),ht.roof_low (le_of_not_ge h),ht.partner_low]; ring

theorem Parameter.width_concave (ht : Parameter t) : ConcaveOn ℝ (Icc 0 1) (width t) := by
  constructor
  · exact convex_Icc ..
  intro x hx y hy a b ha hb hab
  change a*width t x+b*width t y ≤ width t (a*x+b*y)
  let v := a*x+b*y
  have hv : v∈Icc 0 1 := (convex_Icc (0:ℝ) 1) hx hy ha hb hab
  let u := max t v
  have hu : u∈Icc t 1 := ⟨le_max_left ..,max_le (by linarith [ht.2.1]) hv.2⟩
  have hpos := ht.1.trans_le (ht.partner_mem hu).1
  have tg := tangent_at ht hv
  change roof t v * partner t u+v*u=radiusSq t at tg
  have roof_le : a*roof t x+b*roof t y≤roof t v := by
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [mul_le_mul_of_nonneg_left (support ht hx hu) ha,
      mul_le_mul_of_nonneg_left (support ht hy hu) hb,tg,congrArg (· * radiusSq t) hab]
  have ab : |1-slope t*v|≤a*|1-slope t*x|+b*|1-slope t*y| := by
    rw [show 1-slope t*v=a*(1-slope t*x)+b*(1-slope t*y) by dsimp [v]; linarith only [hab]]
    simpa only [abs_mul,abs_of_nonneg ha,abs_of_nonneg hb] using
      (abs_add_le (a*(1-slope t*x)) (b*(1-slope t*y)))
  change a*(2*roof t x/radiusSq t-|1-slope t*x|)+b*(2*roof t y/radiusSq t-|1-slope t*y|)≤
    2*roof t v/radiusSq t-|1-slope t*v|
  have sc := mul_le_mul_of_nonneg_left roof_le (show 0≤2/radiusSq t by positivity [radius_pos t])
  simp only [div_eq_mul_inv] at sc ⊢
  linarith only [sc,ab]

theorem Parameter.width_lower (ht : Parameter t) (hx : x∈Icc 0 1) : 1-x ≤ width t x := by
  have c := ht.width_concave.2 (left_mem_Icc.mpr (zero_le_one : (0:ℝ)≤1))
    (right_mem_Icc.mpr (zero_le_one : (0:ℝ)≤1)) (sub_nonneg.mpr hx.2) hx.1 (show 1-x+x=1 by ring)
  simpa [ht.width_zero,ht.width_one] using c

theorem Parameter.width_upper (ht : Parameter t) (hx : x∈Icc 0 1) : width t x≤1+x := by
  have s := support ht hx (show t∈Icc t 1 from ⟨le_rfl,by linarith [ht.2.1]⟩)
  rw [ht.partner_low,mul_one] at s
  calc
    width t x ≤ 2*roof t x/radiusSq t-(1-slope t*x) := sub_le_sub_left (le_abs_self _) _
    _ ≤ 2*(radiusSq t-x*t)/radiusSq t-(1-slope t*x) := by
      gcongr <;> linarith only [s,radius_pos t]
    _ = 1+x := by unfold slope; field_simp [(radius_pos t).ne']; ring

private theorem high_pair (ht : Parameter t) (hy : y∈Icc t 1) (hz : z∈Icc t 1) :
    z-y+z*width t y+y*width t z ≤ 2 := by
  have y0 := ht.1.le.trans hy.1
  have z0 := ht.1.le.trans hz.1
  have c : z*partner t y+y*partner t z ≤ radiusSq t := by
    linarith only [ht.partner_sq ⟨y0,hy.2⟩,ht.partner_sq ⟨z0,hz.2⟩,
      sq_nonneg (z-partner t y),sq_nonneg (y-partner t z)]
  have a := mul_le_mul_of_nonneg_left (le_abs_self (1-slope t*y)) z0
  have b := mul_le_mul_of_nonneg_left (neg_le_abs (1-slope t*z)) y0
  simp only [width,roof_high hy.1,roof_high hz.1]
  have cs := mul_le_mul_of_nonneg_left c (show 0≤2/radiusSq t by positivity [radius_pos t])
  rw [div_mul_cancel₀ _ (radius_pos t).ne'] at cs
  simp only [div_eq_mul_inv] at cs ⊢
  linarith only [a,b,cs]

theorem Parameter.pair_bound (ht : Parameter t) (hy : y∈Icc 0 1) (hyz : y≤z) (hz : z≤1) :
    z-y+z*width t y+y*width t z ≤ 2 := by
  by_cases lo : t≤y
  · exact high_pair ht ⟨lo,hyz.trans hz⟩ ⟨lo.trans hyz,hz⟩
  rw [ht.width_low (le_of_not_ge lo)]
  by_cases hi : t≤z
  · have upper := high_pair ht (show t∈Icc t 1 from ⟨le_rfl,hi.trans hz⟩) ⟨hi,hz⟩
    rw [ht.width_low le_rfl] at upper
    nlinarith only [upper,mul_nonneg (sub_nonneg.mpr (le_of_not_ge lo))
      (show 0≤z-1+width t z by linarith only [ht.width_lower ⟨hy.1.trans hyz,hz⟩])]
  · rw [ht.width_low (le_of_not_ge hi)]
    have h1 : z≤1/4 := (le_of_not_ge hi).trans ht.2.1.le
    nlinarith only [h1,mul_le_mul_of_nonneg_left (hyz.trans hz) (hy.1.trans hyz)]

/-- At conjugate heights the triangle through the base endpoint has maximal area. -/
theorem Parameter.pair_tight (ht : Parameter t) (hy : y∈Icc t 1) (hyz : y≤partner t y) :
    let z := partner t y
    z-y+z*width t y+y*width t z = 2 := by
  let z := partner t y
  have hz : z∈Icc t 1 := ht.partner_mem hy
  have yy : y∈Icc 0 1 := ⟨ht.1.le.trans hy.1,hy.2⟩
  have zz := ht.partner_sq yy
  change z^2=radiusSq t-y^2 at zz
  have mm := ht.mid_sq
  have m0 := ht.1.le.trans ht.mid_mem.1
  have yy2 := pow_le_pow_left₀ yy.1 hyz 2
  change y^2≤z^2 at yy2
  have ym : y≤middle t := (sq_le_sq₀ yy.1 m0).mp (by linarith only [zz,yy2,mm])
  have mz : middle t≤z := (sq_le_sq₀ m0 (ht.1.le.trans hz.1)).mp (by linarith only [zz,yy2,mm])
  have sy := mul_le_mul_of_nonneg_left ym ht.slope_pos.le
  have sz := mul_le_mul_of_nonneg_left mz ht.slope_pos.le
  rw [ht.slope_mid] at sy sz
  change z-y+z*width t y+y*width t z=2
  rw [width,width,roof_high hy.1,roof_high hz.1,abs_of_nonneg (sub_nonneg.mpr sy),abs_of_nonpos (sub_nonpos.mpr sz)]
  have inv : partner t z=y := ht.partner_self yy
  rw [inv]
  change z-y+z*(2*z/radiusSq t-(1-slope t*y))+y*(2*y/radiusSq t- -(1-slope t*z))=2
  field_simp [(radius_pos t).ne']
  linarith only [zz]

end ErdosPurdyStraus
