module

public import conjectures.ErdosPurdyStraus.Boundary
public import conjectures.ErdosPurdyStraus.Normalize
public import conjectures.ErdosPurdyStraus.SingleSide
public import conjectures.ErdosPurdyStraus.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

public section
namespace ErdosPurdyStraus
open Set MeasureTheory

/-- The maximum in the 1982 triangle problem, including an extremizing convex body. -/
theorem sharp {t : ℝ} (ht : Parameter t) : IsAnswer (Real.pi-4*Real.arctan t-t^2) := by
  have value := ht.width_integral
  constructor
  · have attained := ht.standard_body.realizes
    rwa [ht.area_body,value] at attained
  · rintro r ⟨K,a,b,c,h,rfl⟩
    obtain ⟨B,standard,equal⟩ := normalize h
    rw [equal,←value]
    linarith only [standard.area_le ht]

/-- The parameter in the sharp area formula is unambiguous. -/
theorem resolution : ∃! t : ℝ, Parameter t ∧ IsAnswer (Real.pi-4*Real.arctan t-t^2) := by
  obtain ⟨t,ht,unique⟩ := parameter_unique
  exact ⟨t,⟨ht,sharp ht⟩,fun _ h ↦ unique _ h.1⟩

/-- The extremizer strictly exceeds the older proposed bound of √5. -/
theorem above_pentagon {t : ℝ} (ht : Parameter t) : Real.sqrt 5<Real.pi-4*Real.arctan t-t^2 := by
  have bound : t < 21/100 := by
    by_contra! h
    linarith only [ht.2.2,h,pow_le_pow_left₀ (by norm_num : (0:ℝ)≤21/100) h 2,
      pow_le_pow_left₀ (by norm_num : (0:ℝ)≤21/100) h 3,
      pow_le_pow_left₀ (by norm_num : (0:ℝ)≤21/100) h 4]
  have root : Real.sqrt 5 < 9/4 := (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    (by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]; norm_num)
  linarith only [root,Real.pi_gt_d2,Real.arctan_le_self ht.1.le,bound,pow_le_pow_left₀ ht.1.le bound.le 2]

/-- info: 'ErdosPurdyStraus.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end ErdosPurdyStraus
