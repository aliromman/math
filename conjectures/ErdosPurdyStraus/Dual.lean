module

public import conjectures.ErdosPurdyStraus.Profile
public import conjectures.ErdosPurdyStraus.Slices
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section
namespace ErdosPurdyStraus
open Set MeasureTheory
open scoped Interval
variable {t : ℝ} {K : Set Plane}

theorem Parameter.partner_deriv (ht : Parameter t) {x : ℝ} (hx : x∈Icc t 1) :
    HasDerivAt (partner t) (-x/partner t x) x := by
  have hp := ht.1.trans_le (ht.partner_mem hx).1
  have rad := Real.sqrt_pos.mp hp
  have d := ((hasDerivAt_const x (radiusSq t)).sub ((hasDerivAt_id x).pow 2)).sqrt rad.ne'
  convert d using 1
  · rfl
  · change -x/partner t x=(0-(2:ℝ)*x^(2-1:ℕ)*1)/(2*partner t x)
    field_simp
    ring

private theorem weighted_pair (h : Standard K) (ht : Parameter t) {x : ℝ} (hx : x∈Icc t 1) :
    let d := fun y ↦ sectionLength K y - width t y
    d x ≤ d (partner t x)*(-x/partner t x) := by
  let z := partner t x
  have hz := ht.partner_mem hx
  have xx : x∈Icc 0 1 := ⟨ht.1.le.trans hx.1,hx.2⟩
  have zz : z∈Icc 0 1 := ⟨ht.1.le.trans hz.1,hz.2⟩
  have paired : z*(sectionLength K x-width t x)+x*(sectionLength K z-width t z) ≤ 0 := by
    rcases le_total x z with le|le
    · have eq := ht.pair_tight hx le
      change z-x+z*width t x+x*width t z=2 at eq
      linarith only [eq,h.section_pair xx zz]
    · have inv : partner t z=x := ht.partner_self xx
      have eq := ht.pair_tight (y:=z) hz (inv ▸ le)
      dsimp only at eq
      rw [inv] at eq
      linarith only [eq,h.section_pair zz xx]
  change sectionLength K x-width t x≤(sectionLength K z-width t z)*(-x/z)
  rw [←mul_div_assoc,le_div_iff₀ (ht.1.trans_le hz.1)]
  linarith only [paired]

/-- The dual pairing on the upper interval bounds the area of every normalized body. -/
theorem Standard.area_le (h : Standard K) (ht : Parameter t) :
    volume.real K ≤ ∫ x in (0:ℝ)..1,width t x := by
  let d (x : ℝ) := sectionLength K x-width t x
  have integrable (a b : ℝ) : IntervalIntegrable d volume a b :=
    (h.section_integrable a b).sub ((width_continuous t).intervalIntegrable a b)
  have le1 := ht.mid_mem.1.trans ht.mid_mem.2
  have cont : ContinuousOn (partner t) [[t,1]] := by unfold partner; fun_prop
  have deriv (x) (hx : x∈Ioo (min t 1) (max t 1)) : HasDerivAt (partner t) (-x/partner t x) x := by
    rw [min_eq_left le1,max_eq_right le1] at hx
    exact ht.partner_deriv ⟨hx.1.le,hx.2.le⟩
  have nonpos (x) (hx : x∈Ioo (min t 1) (max t 1)) : -x/partner t x≤0 := by
    rw [min_eq_left le1] at hx
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (ht.1.trans hx.1).le) (partner_nn ..)
  have transform := @intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos t 1 (partner t)
    (fun x ↦ -x/partner t x) d cont deriv nonpos
  have equiv := @intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos t 1 (partner t)
    (fun x ↦ -x/partner t x) d cont deriv nonpos
  rw [ht.partner_low,ht.partner_high] at transform equiv
  have cmp := intervalIntegral.integral_mono_on le1 (integrable t 1) (equiv.mpr (integrable 1 t))
    (fun x hx ↦ weighted_pair h ht hx)
  rw [transform,intervalIntegral.integral_symm t 1] at cmp
  have neg : (∫ x in t..1,d x)≤0 := by linarith only [cmp]
  have lower : (∫ x in (0:ℝ)..t,sectionLength K x)≤∫ x in (0:ℝ)..t,width t x := by
    apply intervalIntegral.integral_mono_on ht.1.le (h.section_integrable ..) ((width_continuous t).intervalIntegrable ..)
    intro x hx
    rw [ht.width_low hx.2]
    exact h.section_upper ⟨hx.1,hx.2.trans le1⟩
  rw [h.area,←intervalIntegral.integral_add_adjacent_intervals (h.section_integrable 0 t) (h.section_integrable t 1),
    ←intervalIntegral.integral_add_adjacent_intervals ((width_continuous t).intervalIntegrable 0 t) ((width_continuous t).intervalIntegrable t 1)]
  change (∫ x in t..1,sectionLength K x-width t x)≤0 at neg
  rw [intervalIntegral.integral_sub (h.section_integrable t 1) ((width_continuous t).intervalIntegrable t 1)] at neg
  linarith only [neg,lower]

end ErdosPurdyStraus
