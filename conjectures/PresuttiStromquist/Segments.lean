module

public import conjectures.PresuttiStromquist.Density
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
namespace PresuttiStromquist
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

/-- The two corners of the rectangle spanned by a decreasing subsegment. -/
def lower (l r : ℝ) : Point := ((bottom l).1, (bottom r).2)
def upper (l r : ℝ) : Point := ((bottom r).1, (bottom l).2)

def interiorSquare : Set Point := Ioo 0 1 ×ˢ Ioo 0 1

@[fun_prop] theorem continuous_turn (i : Fin 4) : Continuous (turn i) := by
  change Continuous (fun z => turn i z)
  fin_cases i <;> dsimp [turn] <;> fun_prop

@[fun_prop] theorem continuous_bottom : Continuous bottom := by unfold bottom; fun_prop

@[fun_prop] theorem continuous_insertMap (l r : ℝ) : Continuous (insertMap l r) := by
  unfold insertMap
  fun_prop

theorem turn_interior (i : Fin 4) {z : Point} (hz : z ∈ interiorSquare) :
    turn i z ∈ interiorSquare := by
  rcases hz with ⟨⟨h1,h2⟩,h3,h4⟩
  fin_cases i <;> dsimp [turn, interiorSquare] <;> grind

theorem insert_bounds {l r : ℝ} (hlr : l < r) {p : Point} (hp : p ∈ interiorSquare) :
    (lower l r).1 < (insertMap l r p).1 ∧ (insertMap l r p).1 < (upper l r).1 ∧
    (lower l r).2 < (insertMap l r p).2 ∧ (insertMap l r p).2 < (upper l r).2 := by
  rcases hp with ⟨⟨ha,hb⟩,hc,hd⟩
  dsimp [lower, upper, insertMap, bottom]
  have := sub_pos.mpr hlr
  have X := mul_pos this ha
  have Y := mul_pos this hc
  have X' := mul_pos this (sub_pos.mpr hb)
  have Y' := mul_pos this (sub_pos.mpr hd)
  constructor <;> [nlinarith; constructor <;> [nlinarith; constructor <;> nlinarith]]

theorem insert_interior {l r : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1)
    {p : Point} (hp : p ∈ interiorSquare) : insertMap l r p ∈ interiorSquare := by
  rcases insert_bounds hlr hp with ⟨a,b,c,d⟩
  dsimp [lower,upper,bottom] at a b c d
  change (0 < _ ∧ _ < 1) ∧ 0 < _ ∧ _ < 1
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem bottom_interior {t : ℝ} (ht : t ∈ Ioo 0 1) : bottom t ∈ interiorSquare := by
  rcases ht with ⟨h0,h1⟩
  change (0 < 1/4+t/2 ∧ 1/4+t/2 < 1) ∧ 0 < (1-t)/4 ∧ (1-t)/4 < 1
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem box_separation {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1/2)
    (i : Fin 4) {p : Point} (hp : p ∈ interiorSquare) :
    ((i = 0 ∧ turn i (insertMap u v p) ∈ box (lower u v) (upper u v)) ∨
      outside (lower u v) (upper u v) (turn i (insertMap u v p))) ∧
    outside (lower u v) (upper u v) (turn i (insertMap (1-u) 1 p)) := by
  have h := insert_bounds huv hp
  have h' := insert_bounds (show 1-u<1 by linarith) hp
  generalize hq : insertMap u v p = q at *
  generalize hq' : insertMap (1-u) 1 p = q' at *
  rcases h with ⟨a,b,c,d⟩
  rcases h' with ⟨e,f,g,h⟩
  dsimp [lower,upper,bottom] at a b c d e f g h
  fin_cases i <;> norm_num [turn, box, outside, lower, upper, bottom] <;> grind

theorem segment_separation {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1/2)
    (i : Fin 4) {t : ℝ} (ht : t ∈ Ioo v (1-v)) :
    outside (lower u v) (upper u v) (turn i (bottom t)) := by
  obtain ⟨a,b⟩ := ht
  fin_cases i <;> norm_num [outside, turn, lower, upper, bottom] <;> grind

theorem density_strict {J : ℝ} (hJ : 0 ≤ J) (t : ℝ) : lineDensity J t ≠ 0 := by
  have hpos : (t-1/2)^2+3/2+4*J > 0 := by nlinarith [sq_nonneg (t-1/2)]
  have hr := Real.sq_sqrt hpos.le
  have hs := Real.sqrt_pos.mpr hpos
  have h : -(Real.sqrt ((t-1/2)^2+3/2+4*J)) < t-1/2 := by
    by_contra! hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ -(t-1/2) + Real.sqrt ((t-1/2)^2+3/2+4*J) by linarith)]
  apply ENNReal.ofReal_ne_zero_iff.mpr
  apply div_pos _ (by norm_num)
  have := (lt_div_iff₀ hs).mpr (show -1 * Real.sqrt ((t-1/2)^2+3/2+4*J) < t-1/2 by linarith)
  linarith

theorem line_concentrated (J v : ℝ) : ∀ᵐ t ∂lineMeasure J v, t ∈ Ioo v (1-v) :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

theorem line_endpoint_support {J v : ℝ} (hJ : 0 ≤ J) (hv : v < 1/2) :
    v ∈ (lineMeasure J v).support := by
  have hv' : v < 1-v := by linarith
  apply (withDensity_absolutelyContinuous' (μ := volume.restrict (Ioo v (1-v)))
    (f := lineDensity J) (by unfold lineDensity; fun_prop)
    (.of_forall (density_strict hJ))).support_mono
  have hI : Ioo v (1-v) ⊆ ((volume : Measure ℝ).restrict (Ioo v (1-v))).support := by
    intro x hx
    apply Measure.interior_inter_support
    simp [isOpen_Ioo.interior_eq, hx, Measure.support_eq_univ]
  apply (Measure.isClosed_support.closure_subset_iff.mpr hI)
  rw [closure_Ioo hv'.ne]
  exact ⟨le_rfl,hv'.le⟩

end PresuttiStromquist
end
