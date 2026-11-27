module

public import conjectures.ErdosPurdyStraus.Normalized
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace ErdosPurdyStraus
open Set MeasureTheory

/-- The length of the vertical section at height x. -/
def sectionLength (K : Set Plane) (x : ℝ) : ℝ := volume.real (Prod.mk x ⁻¹' K)

variable {K : Set Plane}

private theorem fiber_compact (h : IsCompact K) (x : ℝ) : IsCompact (Prod.mk x ⁻¹' K) := by
  have e : Prod.mk x ⁻¹' K = Prod.snd '' (K ∩ Prod.fst ⁻¹' {x}) := by
    ext y
    constructor
    · intro hy; exact ⟨(x,y),⟨hy,rfl⟩,rfl⟩
    · rintro ⟨⟨a,b⟩,⟨p,rfl : a=x⟩,rfl : b=y⟩; exact p
  rw [e]
  exact (h.inter_right (isClosed_singleton.preimage continuous_fst)).image continuous_snd

theorem Standard.fiber (h : Standard K) {x : ℝ} (hx : x∈Icc 0 1) :
    ∃ l u : ℝ, (x,l)∈K ∧ (x,u)∈K ∧ sectionLength K x=u-l := by
  let F := Prod.mk x ⁻¹' K
  have comp := fiber_compact h.compact x
  have point := h.convex h.hi h.top (sub_nonneg.mpr hx.2) hx.1 (show 1-x+x=1 by ring)
  have ne : F.Nonempty := by
    refine ⟨(1-x)*(1/2),?_⟩
    simpa [F,baseHi,apex,Prod.smul_mk,smul_eq_mul] using point
  let l := sInf F
  let u := sSup F
  have hl : l∈F := comp.sInf_mem ne
  have hu : u∈F := comp.sSup_mem ne
  have lu : l≤u := le_csSup comp.bddAbove hl
  have cv : Convex ℝ F := by
    intro y hy z hz a b ha hb hab
    have v := h.convex (show (x,y)∈K from hy) (show (x,z)∈K from hz) ha hb hab
    change (x,a*y+b*z)∈K
    have eq : a*x+b*x=x := by rw [←add_mul,hab,one_mul]
    simpa only [Prod.smul_mk,smul_eq_mul,Prod.mk_add_mk,eq] using v
  have bounds : F=Icc l u := Subset.antisymm
    (fun y hy ↦ ⟨csInf_le comp.bddBelow hy,le_csSup comp.bddAbove hy⟩)
    (by rw [←segment_eq_Icc lu]; exact cv.segment_subset hl hu)
  refine ⟨l,u,hl,hu,?_⟩
  change (volume F).toReal=u-l
  rw [bounds,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr lu)]

theorem Standard.section_pair (h : Standard K) {y z : ℝ} (hy : y∈Icc 0 1) (hz : z∈Icc 0 1) :
    z-y+z*sectionLength K y+y*sectionLength K z ≤ 2 := by
  obtain ⟨l,u,hl,hu,fy⟩ := h.fiber hy
  obtain ⟨v,w,hv,hw,fz⟩ := h.fiber hz
  have upper := (abs_le.mp (h.triangles baseHi h.hi (y,l) hl (z,w) hw)).2
  have lower := (abs_le.mp (h.triangles baseLo h.lo (y,u) hu (z,v) hv)).1
  rw [fy,fz]
  simp only [cross] at upper lower
  linarith only [upper,lower]

theorem Standard.section_upper (h : Standard K) {y : ℝ} (hy : y∈Icc 0 1) : sectionLength K y≤1+y := by
  have pair := h.section_pair hy (right_mem_Icc.mpr (zero_le_one : (0:ℝ)≤1))
  linarith only [pair,mul_nonneg hy.1 (show 0≤sectionLength K 1 from ENNReal.toReal_nonneg)]

private theorem integrable_sections (h : IsCompact K) : Integrable (sectionLength K) := by
  apply integrable_toReal_of_lintegral_ne_top (measurable_measure_prodMk_left h.measurableSet).aemeasurable
  rw [←Measure.prod_apply h.measurableSet,←Measure.volume_eq_prod]
  exact h.measure_lt_top.ne

theorem Standard.section_integrable (h : Standard K) (a b : ℝ) :
    IntervalIntegrable (sectionLength K) volume a b := (integrable_sections h.compact).intervalIntegrable

theorem Standard.area (h : Standard K) : volume.real K=∫ x in (0:ℝ)..1, sectionLength K x := by
  have all : volume.real K=∫ x,sectionLength K x := by
    change (volume K).toReal=∫ x,(volume (Prod.mk x ⁻¹' K)).toReal
    rw [Measure.volume_eq_prod,Measure.prod_apply h.compact.measurableSet,
      integral_toReal (measurable_measure_prodMk_left h.compact.measurableSet).aemeasurable]
    exact Filter.Eventually.of_forall fun x ↦ (fiber_compact h.compact x).measure_lt_top
  rw [all,intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  have empty : Prod.mk x ⁻¹' K=∅ := eq_empty_iff_forall_notMem.mpr fun y hy ↦ hx (h.height _ hy)
  simp [sectionLength,empty]

end ErdosPurdyStraus
end
