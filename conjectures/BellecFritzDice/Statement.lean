module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section
namespace BellecFritzDice
open Set MeasureTheory

/-- The joint law of independent rolls of the same die. -/
noncomputable abbrev rolls (μ : Measure ℝ) (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi (fun _ => μ)

/-- The affirmative answer to the question after Theorem 1.5.
All three outcomes are nonnegative and have a common atomless law. -/
def Attainable : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ NullSingletonClass μ ∧ μ (Iio 0)=0 ∧
    (rolls μ 3).real {x | 2*x 0 < x 1+x 2} = 2/3

def below (m : ℕ) (i : Fin m) : Set (Fin m → ℝ) :=
  {x | (m:ℝ)*x i < ∑ j, x j}

noncomputable def chance (μ : Measure ℝ) (n : ℕ) : ℝ :=
  (rolls μ (n+3)).real (below (n+3) 0)

end BellecFritzDice
