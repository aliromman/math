module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section
noncomputable section
namespace PresuttiStromquist
open Set MeasureTheory
open scoped NNReal ENNReal

abbrev Point := ℝ × ℝ
abbrev Four := Point × Point × Point × Point

/-- The labeled event for 2413. Multiplication by 4! gives the unlabeled packing rate. -/
def event : Set Four := {v |
  v.1.1 < v.2.1.1 ∧ v.2.1.1 < v.2.2.1.1 ∧ v.2.2.1.1 < v.2.2.2.1 ∧
  v.2.2.1.2 < v.1.2 ∧ v.1.2 < v.2.2.2.2 ∧ v.2.2.2.2 < v.2.1.2}

def mixed (a b c d : Measure Point) : ℝ := (a.prod (b.prod (c.prod d))).real event

def rate (μ : Measure Point) : ℝ := 24 * mixed μ μ μ μ

def square : Set Point := Icc 0 1 ×ˢ Icc 0 1

def Optimal (μ : Measure Point) : Prop := IsProbabilityMeasure μ ∧ μ squareᶜ = 0 ∧
  ∀ ν : Measure Point, IsProbabilityMeasure ν → ν squareᶜ = 0 → rate ν ≤ rate μ

/-- The lower segment in equation (34). The other three are quarter turns. -/
def bottom (t : ℝ) : Point := (1/4+t/2, (1-t)/4)

def turn (i : Fin 4) (z : Point) : Point :=
  ![z, (1-z.2,z.1), (1-z.1,1-z.2), (z.2,1-z.1)] i

/-- The orientation-preserving rescaling of the entire square into this bubble. -/
def insertMap (l r : ℝ) (z : Point) : Point :=
  ((bottom l).1+(r-l)/2*z.1, (bottom r).2+(r-l)/4*z.2)

/-- The derivative of the middle branch of F in Section 10, with the segment mass 1/4. -/
def lineDensity (J t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + (t-1/2)/Real.sqrt ((t-1/2)^2+3/2+4*J))/4)

def lineMeasure (J v : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo v (1-v))).withDensity (lineDensity J)

def quarterLaw (u v J : ℝ) (μ : Measure Point) (i : Fin 4) : Measure Point :=
  ((lineMeasure J v).map (turn i ∘ bottom) +
    (u/2).toNNReal • μ.map (turn i ∘ insertMap (1-u) 1)) +
    ((v-u)/2).toNNReal • μ.map (turn i ∘ insertMap u v)

/-- Four turns of the central line and the two recursive boxes of Section 10. -/
def construction (u v J : ℝ) (μ : Measure Point) : Measure Point :=
  ∑ i : Fin 4, quarterLaw u v J μ i

/-- Every choice of the two positive bubble sizes is included. -/
structure TwoBubble (u v J : ℝ) (μ : Measure Point) : Prop where
  first_pos : 0 < u
  first_lt_second : u < v
  central_interval : v < 1/2
  integral_nonneg : 0 ≤ J
  recurrence : μ = construction u v J μ

/-- The branch between the two outer pairs of recursive rectangles. -/
def freeCDF (J x : ℝ) := Real.sqrt ((x-1/2)^2+3/2+4*J)+(x-3/2)

/-- The five pieces of the bottom-segment distribution in Section 10. -/
def segmentCDF (u v J x : ℝ) : ℝ :=
  if x≤u then 0 else if x≤v then 2*(x-u) else if x≤1-v then freeCDF J x
  else if x≤1-u then 1-2*u else 2*x-1

/-- The joins, integral condition and probability normalization used for the two-bubble candidate. -/
def SectionTen (μ : Measure Point) : Prop := ∃ u v J : ℝ,
  TwoBubble u v J μ ∧ freeCDF J v = 2*(v-u) ∧ J = (∫ x in (0:ℝ)..(1/2), segmentCDF u v J x) ∧
  IsProbabilityMeasure μ ∧ μ squareᶜ=0

/-- Conjecture 10.1: the measure optimized in the two-bubble family is optimal among all measures. -/
def Conjecture : Prop := ∃ μ : Measure Point, SectionTen μ ∧
  (∀ ν : Measure Point, SectionTen ν → rate ν ≤ rate μ) ∧ Optimal μ

end PresuttiStromquist
end
