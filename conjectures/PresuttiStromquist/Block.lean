module

public import conjectures.PresuttiStromquist.Variation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

@[expose] public section
noncomputable section
namespace PresuttiStromquist
open Set MeasureTheory Filter

private def enclosed (a b q : Point) : Prop :=
  a.1≤q.1 ∧ q.1≤b.1 ∧ a.2≤q.2 ∧ q.2≤b.2

private lemma enclosed_of_mem {a b q : Point} (h : q∈box a b) : enclosed a b q :=
  ⟨h.1.1.le,h.1.2.le,h.2.1.le,h.2.2.le⟩

private lemma same_exterior {a b p q u : Point} (hp : enclosed a b p)
    (hq : enclosed a b q) (h : outside a b u) : same p q u := by
  unfold outside at h
  unfold enclosed at hp hq
  unfold same
  grind

/-- In a 2413 occurrence no two or three points occupy an isolated rectangular block. -/
private lemma mixed_impossible {a b p : Point} {v : Triple} (i : Fin 4) (hp : enclosed a b p)
    (A : v.1∈box a b ∨ outside a b v.1) (B : v.2.1∈box a b ∨ outside a b v.2.1)
    (C : v.2.2∈box a b ∨ outside a b v.2.2)
    (inside : v.1∈box a b ∨ v.2.1∈box a b ∨ v.2.2∈box a b)
    (exterior : outside a b v.1 ∨ outside a b v.2.1 ∨ outside a b v.2.2) :
    insertPoint i (p,v) ∉ event := by
  intro h
  simp only [box,mem_prod,mem_Ioo,outside,enclosed] at hp A B C inside exterior
  fin_cases i <;> simp only [insertPoint,event,mem_ofPred_eq] at h <;> grind (splits := 32)

private lemma corner_impossible {a b : Point} {v : Triple} (i : Fin 4)
    (h : v.1∈box a b ∧ v.2.1∈box a b ∧ v.2.2∈box a b) :
    insertPoint i ((b.1,a.2),v)∉event := by
  intro e
  simp only [box,mem_prod,mem_Ioo] at h
  fin_cases i <;> simp only [insertPoint,event,mem_ofPred_eq] at e <;> grind

def threeBox (a b : Point) : Set Triple := box a b ×ˢ box a b ×ˢ box a b

theorem measurable_box (a b : Point) : MeasurableSet (box a b) := measurableSet_Ioo.prod measurableSet_Ioo
private theorem measurable_threeBox (a b : Point) : MeasurableSet (threeBox a b) :=
  (measurable_box a b).prod ((measurable_box a b).prod (measurable_box a b))

private theorem occurrences_split {a b q : Point} (hq : q∈box a b) {v : Triple} (i : Fin 4)
    (A : v.1∈box a b ∨ outside a b v.1) (B : v.2.1∈box a b ∨ outside a b v.2.1)
    (C : v.2.2∈box a b ∨ outside a b v.2.2) :
    occurs i q v = occurs i (b.1,a.2) v + (threeBox a b).indicator (occurs i q) v := by
  classical
  have hp : enclosed a b (b.1,a.2) := ⟨(lt_trans hq.1.1 hq.1.2).le,le_rfl,le_rfl,(lt_trans hq.2.1 hq.2.2).le⟩
  by_cases all : v∈threeBox a b
  · have nne := corner_impossible i all
    simp [all,occurs,nne]
  rw [indicator_of_notMem all,add_zero]
  by_cases some : v.1∈box a b ∨ v.2.1∈box a b ∨ v.2.2∈box a b
  · have ex : outside a b v.1 ∨ outside a b v.2.1 ∨ outside a b v.2.2 := by
      change ¬(_ ∧ _ ∧ _) at all
      tauto
    have e := mixed_impossible i hp A B C some ex
    have f := mixed_impossible i (enclosed_of_mem hq) A B C some ex
    simp [occurs,e,f]
  · apply occurs_same i
    all_goals apply same_exterior hp (enclosed_of_mem hq)
    all_goals tauto

private theorem integrable_fixed (μ : Measure Point) [IsFiniteMeasure μ] (i : Fin 4) (q : Point) :
    Integrable (occurs i q) (draws μ) :=
  (integrable_const 1).mono' (((measurable_occurs i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (.of_forall fun v ↦ norm_occurs i q v)

theorem link_split {μ : Measure Point} [IsFiniteMeasure μ] {a b q : Point} (hq : q∈box a b)
    (sep : ∀ᵐ u ∂μ, u∈box a b ∨ outside a b u) :
    link μ q = link μ (b.1,a.2) + link (μ.restrict (box a b)) q := by
  have restrict : draws (μ.restrict (box a b)) = (draws μ).restrict (threeBox a b) := by
    simp only [draws,threeBox,Measure.prod_restrict]
  have step (i : Fin 4) : atPosition μ i q = atPosition μ i (b.1,a.2) + atPosition (μ.restrict (box a b)) i q := by
    unfold atPosition
    rw [restrict,←integral_indicator (measurable_threeBox a b),←integral_add (integrable_fixed μ i _)
      ((integrable_fixed μ i _).indicator (measurable_threeBox a b))]
    apply integral_congr_ae
    filter_upwards [three_ae sep] with v h
    exact occurrences_split hq i h.1 h.2.1 h.2.2
  simp only [link,step,Finset.sum_add_distrib]

/-- An isolated block with positive internal packing cannot meet the support at its southeast corner. -/
theorem corner_obstruction {μ : Measure Point} {a b : Point} (bounds : a.1<b.1 ∧ a.2<b.2)
    (sep : ∀ᵐ u ∂μ, u∈box a b ∨ outside a b u)
    (support : ∀ U ∈ nhds (b.1,a.2), μ U ≠ 0)
    (positive : let ν := μ.restrict (box a b); 0 < mixed ν ν ν ν) : ¬Optimal μ := by
  intro opt
  let : IsProbabilityMeasure μ := opt.1
  let ν := μ.restrict (box a b)
  have avoid : ∀ᵐ u ∂μ, u.1≠b.1 ∧ u.2≠a.2 := by
    filter_upwards [sep] with u h
    simp only [box,mem_prod,mem_Ioo,outside] at h
    grind
  have val := opt.support_link support avoid
  have eq : ∀ᵐ q ∂ν, link ν q=0 := by
    filter_upwards [ae_restrict_mem (μ:=μ) (measurable_box a b),ae_restrict_of_ae opt.stationary] with q hq e
    change link (μ.restrict (box a b)) q=0
    linarith only [link_split hq sep,e,val]
  have z : (∫ q, link ν q ∂ν) = 0 := by rw [integral_congr_ae eq]; simp
  rw [link_integral] at z
  change 0 < mixed ν ν ν ν at positive
  unfold linearTerm at z
  linarith

end PresuttiStromquist
end
