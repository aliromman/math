module

public import conjectures.PresuttiStromquist.Statement
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
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
open scoped NNReal ENNReal

theorem measurable_event : MeasurableSet event := by
  unfold event
  measurability

def box (a b : Point) : Set Point := Ioo a.1 b.1 ×ˢ Ioo a.2 b.2

def outside (a b u : Point) : Prop := (u.1<a.1 ∨ b.1<u.1) ∧ (u.2<a.2 ∨ b.2<u.2)

/-- Each of the four sampled positions can be the distinguished point. -/
def linearTerm (μ ν : Measure Point) : ℝ :=
  mixed ν μ μ μ + mixed μ ν μ μ + mixed μ μ ν μ + mixed μ μ μ ν

theorem mixed_nonneg (a b c d : Measure Point) : 0 ≤ mixed a b c d :=
  ENNReal.toReal_nonneg

@[simp] theorem mixed_smul (a b c d : Measure Point) [IsFiniteMeasure a] [IsFiniteMeasure b] [IsFiniteMeasure c] [IsFiniteMeasure d] (t : ℝ≥0) :
    mixed (t • a) (t • b) (t • c) (t • d) = (t : ℝ)^4 * mixed a b c d := by
  simp only [mixed,Measure.prod_smul_left,Measure.prod_smul_right,measureReal_nnreal_smul_apply]
  ring

theorem firstOrder (μ ν : Measure Point) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : ℝ≥0) :
    mixed μ μ μ μ + (t:ℝ)*linearTerm μ ν ≤
      mixed (μ+t•ν) (μ+t•ν) (μ+t•ν) (μ+t•ν) := by
  apply sub_nonneg.mp
  simp (disch := finiteness) only [linearTerm,mixed,Measure.add_prod,Measure.prod_add,Measure.prod_smul_left,
    Measure.prod_smul_right,smul_add,measureReal_add_apply,measureReal_nnreal_smul_apply]
  ring_nf
  positivity

/-- First variation of the degree-four probability at a maximizing measure. -/
theorem Optimal.linear_le {μ ν : Measure Point} (opt : Optimal μ) [IsProbabilityMeasure ν]
    (hsν : ν squareᶜ=0) : linearTerm μ ν ≤ 4*mixed μ μ μ μ := by
  let : IsProbabilityMeasure μ := opt.1
  let A := mixed μ μ μ μ
  have estimate (s : ℝ) (hs : 0<s) : linearTerm μ ν ≤ (4+6*s+4*s^2+s^3)*A := by
    let t : ℝ≥0 := ⟨s,hs.le⟩
    let c : ℝ≥0 := (1+t)⁻¹
    let ρ := c • (μ+t•ν)
    have ne : (1+t:ℝ≥0) ≠ 0 := by positivity
    have normal : IsProbabilityMeasure ρ := ⟨by
      change (c:ℝ≥0∞)*((μ+t•ν) univ) = 1
      rw [add_apply, measure_univ]
      change (c:ℝ≥0∞)*(1+(t:ℝ≥0∞)*(ν univ))=1
      rw [measure_univ,mul_one]
      exact_mod_cast inv_mul_cancel₀ ne⟩
    have supp : ρ squareᶜ=0 := by simp [ρ,opt.2.1,hsν]
    have upper := opt.2.2 ρ normal supp
    change 24*mixed (c • (μ+t•ν)) (c • (μ+t•ν)) (c • (μ+t•ν)) (c • (μ+t•ν)) ≤ 24*A at upper
    rw [mixed_smul] at upper
    have C : (c:ℝ)=1/(1+s) := by rw [one_div]; rfl
    rw [C] at upper
    field_simp [show (1+s)≠0 by positivity] at upper
    have low := firstOrder μ ν t
    change A + s*linearTerm μ ν ≤ _ at low
    apply le_of_mul_le_mul_left (a:=s) _ hs
    nlinarith only [low,upper]
  have tend : Filter.Tendsto (fun s : ℝ ↦ (4+6*s+4*s^2+s^3)*A)
      (nhdsWithin 0 (Ioi 0)) (nhds (4*A)) := by
    have e := (show ContinuousAt (fun s : ℝ ↦ (4+6*s+4*s^2+s^3)*A) 0 by fun_prop).tendsto.mono_left
      (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
    simpa using e
  exact le_of_tendsto_of_tendsto tendsto_const_nhds tend (Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), s∈Ioi 0) fun s hs ↦ estimate s hs)

end PresuttiStromquist
end
