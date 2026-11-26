module

public import conjectures.PresuttiStromquist.Segments
public import conjectures.PresuttiStromquist.BubbleRate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace PresuttiStromquist
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

private theorem measurable_inside : MeasurableSet interiorSquare :=
  measurableSet_Ioo.prod measurableSet_Ioo

private theorem line_inside {u v J : ℝ} {μ : Measure Point} (h : TwoBubble u v J μ)
    (i : Fin 4) : ∀ᵐ z ∂(lineMeasure J v).map (turn i ∘ bottom), z ∈ interiorSquare := by
  apply (ae_map_iff (by fun_prop) measurable_inside).mpr
  filter_upwards [line_concentrated J v] with t ht
  obtain ⟨a,b⟩ := ht
  apply turn_interior i
  apply bottom_interior
  exact ⟨by linarith [h.first_pos, h.first_lt_second], by linarith [h.first_pos, h.first_lt_second]⟩

/-- The recursive copies give zero mass to the outer boundary. Their total mass is 2v < 1. -/
theorem TwoBubble.inside {u v J : ℝ} {μ : Measure Point} [IsFiniteMeasure μ] (h : TwoBubble u v J μ) :
    ∀ᵐ z ∂μ, z ∈ interiorSquare := by
  let C := interiorSquareᶜ
  let a := (u/2).toNNReal
  let b := ((v-u)/2).toNNReal
  have hC : MeasurableSet C := measurable_inside.compl
  have hb {l r : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1) (i : Fin 4) :
      (μ.map (turn i ∘ insertMap l r)) C ≤ μ C := by
    rw [Measure.map_apply (by fun_prop) hC]
    apply measure_mono
    intro z hz hz'
    exact hz (turn_interior i (insert_interior hl hlr hr hz'))
  have hline (i : Fin 4) : ((lineMeasure J v).map (turn i ∘ bottom)) C = 0 :=
    ae_iff.mp (line_inside h i)
  have bound : μ C ≤ 4*((a:ℝ≥0∞)+(b:ℝ≥0∞))*μ C := by
    calc
      μ C = (construction u v J μ) C := congrArg (fun η : Measure Point => η C) h.recurrence
      _ ≤ ∑ _i : Fin 4, ((a:ℝ≥0∞)*μ C + (b:ℝ≥0∞)*μ C) := by
        unfold construction
        rw [sum_apply]
        apply Finset.sum_le_sum
        intro i _
        simp only [quarterLaw, add_apply, smul_apply, hline, zero_add, ENNReal.smul_def, smul_eq_mul]
        exact add_le_add (mul_le_mul_right (hb (by linarith [h.first_lt_second, h.central_interval])
          (by linarith [h.first_pos]) le_rfl i) _)
          (mul_le_mul_right (hb h.first_pos.le h.first_lt_second (by linarith [h.central_interval]) i) _)
      _ = _ := by simp; ring
  have A : (a:ℝ) = u/2 := Real.coe_toNNReal _ (by linarith [h.first_pos])
  have B : (b:ℝ) = (v-u)/2 := Real.coe_toNNReal _ (by linarith [h.first_lt_second])
  have realBound := ENNReal.toReal_mono (by finiteness) bound
  simp [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness : (a:ℝ≥0∞) ≠ ⊤) (by finiteness : (b:ℝ≥0∞) ≠ ⊤), A, B] at realBound
  apply ae_iff.mpr
  change μ C = 0
  apply (measureReal_eq_zero_iff (μ := μ) (s := C)).mp
  by_contra hn
  have pos : 0 < μ.real C := (measureReal_nonneg).lt_of_ne' hn
  change (μ C).toReal ≠ 0 at hn
  change (μ C).toReal > 0 at pos
  nlinarith [mul_pos pos (show 0 < 1-2*v by linarith [h.central_interval])]

private theorem zero_quarter_le (u v J : ℝ) (μ : Measure Point) :
    quarterLaw u v J μ 0 ≤ construction u v J μ :=
  by
    apply Measure.le_iff'.mpr
    intro s
    unfold construction
    rw [sum_apply]
    exact Finset.single_le_sum (f := fun j => quarterLaw u v J μ j s) (fun _ _ => zero_le) (Finset.mem_univ (0 : Fin 4))

private theorem line_le (u v J : ℝ) (μ : Measure Point) :
    (lineMeasure J v).map bottom ≤ construction u v J μ :=
  by
    apply le_trans _ (zero_quarter_le u v J μ)
    apply Measure.le_iff'.mpr
    intro s
    change _ ≤ (_ + _ + _ : ℝ≥0∞)
    exact le_add_right (le_add_right le_rfl)

private theorem small_le (u v J : ℝ) (μ : Measure Point) :
    ((v-u)/2).toNNReal • μ.map (insertMap u v) ≤ construction u v J μ :=
  by
    apply le_trans _ (zero_quarter_le u v J μ)
    apply Measure.le_iff'.mpr
    intro s
    change _ ≤ (_ + _ : ℝ≥0∞)
    exact le_add_left le_rfl

theorem TwoBubble.corner_support {u v J : ℝ} {μ : Measure Point} (h : TwoBubble u v J μ) :
    bottom v ∈ μ.support := by
  apply (Measure.support_mono ((line_le u v J μ).trans_eq h.recurrence.symm))
  rw [Measure.support_eq_forall_isOpen]
  intro U hx hU
  rw [Measure.map_apply continuous_bottom.measurable hU.measurableSet]
  exact (Measure.mem_support_iff_forall _ |>.mp
    (line_endpoint_support h.integral_nonneg h.central_interval)) _
      (continuous_bottom.continuousAt.preimage_mem_nhds (hU.mem_nhds hx))

theorem TwoBubble.separation {u v J : ℝ} {μ : Measure Point} [IsFiniteMeasure μ] (h : TwoBubble u v J μ) :
    ∀ᵐ z ∂μ, z ∈ box (lower u v) (upper u v) ∨ outside (lower u v) (upper u v) z := by
  let P (z : Point) := z ∈ box (lower u v) (upper u v) ∨ outside (lower u v) (upper u v) z
  have hm : MeasurableSet {z | P z} := by unfold P box outside; measurability
  have hinside := h.inside
  rw [h.recurrence, construction, ae_finsetSum_measure_iff]
  intro i _
  simp only [quarterLaw, ae_add_measure_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply (ae_map_iff (by fun_prop) hm).mpr
    filter_upwards [line_concentrated J v] with t ht
    exact Or.inr (segment_separation h.first_pos h.first_lt_second h.central_interval i ht)
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (by fun_prop) hm).mpr
    filter_upwards [hinside] with p hp
    exact Or.inr (box_separation h.first_pos h.first_lt_second h.central_interval i hp).2
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (by fun_prop) hm).mpr
    filter_upwards [hinside] with p hp
    exact (box_separation h.first_pos h.first_lt_second h.central_interval i hp).1.imp And.right id

private theorem map_rate {u v : ℝ} (huv : u < v) (μ : Measure Point) [IsFiniteMeasure μ] :
    let η := μ.map (insertMap u v)
    mixed η η η η = mixed μ μ μ μ := by
  let f := insertMap u v
  have hf : Measurable f := (continuous_insertMap u v).measurable
  let f2 := Prod.map f f
  let f3 := Prod.map f f2
  let f4 := Prod.map f f3
  have hf2 : Measurable f2 := hf.prodMap hf
  have hf3 : Measurable f3 := hf.prodMap hf2
  have hx : 0 < (v-u)/2 := by linarith
  have hy : 0 < (v-u)/4 := by linarith
  have hpre : f4 ⁻¹' event = event := by
    ext ⟨a,b,c,d⟩
    simp [f4, f3, f2, f, insertMap, event, mul_lt_mul_iff_right₀ hx, mul_lt_mul_iff_right₀ hy]
  change ((μ.map f).prod ((μ.map f).prod ((μ.map f).prod (μ.map f)))).real event = _
  rw [Measure.map_prod_map μ μ hf hf, Measure.map_prod_map μ (μ.prod μ) hf hf2,
    Measure.map_prod_map μ (μ.prod (μ.prod μ)) hf hf3, map_measureReal_apply (hf.prodMap hf3) measurable_event]
  exact congrArg _ hpre

/-- Four points that fall inside this copy retain their order after rescaling. -/
theorem TwoBubble.internal_positive {u v J : ℝ} {μ : Measure Point} [IsFiniteMeasure μ]
    (h : TwoBubble u v J μ) (hr : 0 < mixed μ μ μ μ) :
    let η := μ.restrict (box (lower u v) (upper u v))
    0 < mixed η η η η := by
  let R := box (lower u v) (upper u v)
  let c := ((v-u)/2).toNNReal
  let ν := μ.map (insertMap u v)
  have inside : ∀ᵐ z ∂c • ν, z ∈ R := by
    apply Measure.ae_smul_measure
    apply (ae_map_iff (continuous_insertMap u v).measurable.aemeasurable
      (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
    filter_upwards [h.inside] with z hz
    obtain ⟨a,b,d,e⟩ := insert_bounds h.first_lt_second hz
    exact ⟨⟨a,b⟩,d,e⟩
  have dominated : c • ν ≤ μ.restrict R := by
    rw [← Measure.restrict_eq_self_of_ae_mem inside]
    exact Measure.restrict_mono_measure ((small_le u v J μ).trans_eq h.recurrence.symm) R
  apply lt_of_lt_of_le _ (mixed_mono dominated dominated dominated dominated)
  rw [mixed_smul, show mixed ν ν ν ν = mixed μ μ μ μ from map_rate h.first_lt_second μ]
  have cp : 0 < (c:ℝ) := by
    change (0:ℝ) < Real.toNNReal ((v-u)/2)
    rw [Real.coe_toNNReal _ (by linarith [h.first_lt_second])]
    linarith [h.first_lt_second]
  positivity

theorem TwoBubble.corner {u v J : ℝ} {μ : Measure Point} (h : TwoBubble u v J μ) :
    ∀ U ∈ 𝓝 ((upper u v).1,(lower u v).2), μ U ≠ 0 := by
  intro U hU
  exact ((Measure.mem_support_iff_forall _).mp h.corner_support U hU).ne'

theorem TwoBubble.bounds {u v J : ℝ} {μ : Measure Point} (h : TwoBubble u v J μ) :
    (lower u v).1 < (upper u v).1 ∧ (lower u v).2 < (upper u v).2 := by
  dsimp [lower,upper,bottom]
  constructor <;> linarith [h.first_lt_second]

end PresuttiStromquist
end
