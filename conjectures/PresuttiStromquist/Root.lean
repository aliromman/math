module

public import conjectures.PresuttiStromquist.Density
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

@[expose] public section
noncomputable section
namespace PresuttiStromquist
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

abbrev Triple := Point × Point × Point
def draws (μ : Measure Point) := μ.prod (μ.prod μ)
instance {μ : Measure Point} [IsFiniteMeasure μ] : IsFiniteMeasure (draws μ) := by
  unfold draws; infer_instance

def insertPoint : Fin 4 → Point × Triple → Four
  | 0, (p,x,y,z) => (p,x,y,z)
  | 1, (p,x,y,z) => (x,p,y,z)
  | 2, (p,x,y,z) => (x,y,p,z)
  | 3, (p,x,y,z) => (x,y,z,p)

def law (μ ν : Measure Point) : Fin 4 → Measure Four
  | 0 => ν.prod (μ.prod (μ.prod μ))
  | 1 => μ.prod (ν.prod (μ.prod μ))
  | 2 => μ.prod (μ.prod (ν.prod μ))
  | 3 => μ.prod (μ.prod (μ.prod ν))

private theorem firstSwap {X : Type*} [MeasurableSpace X] (a b : Measure Point) (c : Measure X)
    [IsFiniteMeasure a] [IsFiniteMeasure b] [IsFiniteMeasure c] :
    MeasurePreserving (fun v : Point × Point × X ↦ (v.2.1,v.1,v.2.2))
      (a.prod (b.prod c)) (b.prod (a.prod c)) :=
  (measurePreserving_prodAssoc b a c).comp (((Measure.measurePreserving_swap (μ:=a) (ν:=b)).prod
    (MeasurePreserving.id c)).comp ((measurePreserving_prodAssoc a b c).symm _))

theorem insert_preserving (μ ν : Measure Point) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (i : Fin 4) :
    MeasurePreserving (insertPoint i) (ν.prod (draws μ)) (law μ ν i) := by
  have h := firstSwap ν μ (μ.prod μ)
  have j := ((MeasurePreserving.id μ).prod (firstSwap ν μ μ)).comp h
  fin_cases i
  · exact MeasurePreserving.id _
  · exact h
  · exact j
  · exact ((MeasurePreserving.id μ).prod ((MeasurePreserving.id μ).prod
      (Measure.measurePreserving_swap (μ:=ν) (ν:=μ)))).comp j

theorem continuous_insert (i : Fin 4) : Continuous (insertPoint i) := by
  fin_cases i <;> unfold insertPoint <;> fun_prop

def occurs (i : Fin 4) (p : Point) (v : Triple) : ℝ := event.indicator 1 (insertPoint i (p,v))

theorem measurable_occurs (i : Fin 4) :
    Measurable (fun v : Point × Triple ↦ occurs i v.1 v.2) :=
  (measurable_const.indicator measurable_event).comp (continuous_insert i).measurable

theorem norm_occurs (i : Fin 4) (p : Point) (v : Triple) : ‖occurs i p v‖≤1 := by
  classical
  by_cases h : insertPoint i (p,v)∈event <;> simp [occurs,h]

def atPosition (μ : Measure Point) (i : Fin 4) (p : Point) :=
  ∫ v, occurs i p v ∂draws μ

def link (μ : Measure Point) (p : Point) := ∑ i, atPosition μ i p

private theorem integrable_occurs (μ ν : Measure Point) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (i : Fin 4) :
    Integrable (fun v : Point × Triple ↦ occurs i v.1 v.2) (ν.prod (draws μ)) :=
  (integrable_const 1).mono' (measurable_occurs i).aestronglyMeasurable
    (.of_forall fun v ↦ norm_occurs i v.1 v.2)

theorem integrable_position (μ ν : Measure Point) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (i : Fin 4) :
    Integrable (atPosition μ i) ν := (integrable_occurs μ ν i).integral_prod_left

theorem pos_integral (μ ν : Measure Point) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (i : Fin 4) :
    ∫ p, atPosition μ i p ∂ν = (law μ ν i).real event := by
  let f := fun v : Point × Triple ↦ occurs i v.1 v.2
  change (∫ p, ∫ v, f (p,v) ∂draws μ ∂ν) = _
  rw [←integral_prod f (integrable_occurs μ ν i)]
  have H := insert_preserving μ ν i
  have eq : f = ((insertPoint i) ⁻¹' event).indicator 1 := by
    classical
    funext v
    by_cases hv : insertPoint i v∈event <;> simp [f,occurs,hv]
  rw [eq,integral_indicator_one ((continuous_insert i).measurable measurable_event)]
  exact congrArg ENNReal.toReal (H.measure_preimage measurable_event.nullMeasurableSet)

theorem integrable_link (μ ν : Measure Point) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (link μ) ν := integrable_finsetSum _ (fun i _ ↦ integrable_position μ ν i)

theorem link_integral (μ ν : Measure Point) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ p, link μ p ∂ν = linearTerm μ ν := by
  unfold link
  rw [integral_finsetSum _ (fun i _ ↦ integrable_position μ ν i)]
  simp only [pos_integral,Fin.sum_univ_four]
  rfl

end PresuttiStromquist
end
