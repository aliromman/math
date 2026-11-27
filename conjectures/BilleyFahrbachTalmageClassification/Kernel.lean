module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-! # The contribution of one prefix endpoint to each later peak -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification

/-- The two powers that count the possible sides of a valley. -/
noncomputable def difference (s : ℂ) (y : ℝ) : ℂ :=
  (((1+y)/2 : ℝ) : ℂ)^s - (((1-y)/2 : ℝ) : ℂ)^s

/-- Extend the prefix with a new peak at position `a+g` relative to the initial peak. -/
noncomputable def gapStep (a g : ℕ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  (if Even g then -2 * F s else 0) +
  ∑ j ∈ Finset.Ico (a+1) (a+g), (-1 : ℂ)^(a+g-1-j) * Ring.choose s j * F j

/-- Apply the remaining gaps in their chronological order. -/
noncomputable def applyGaps : List ℕ → ℕ → (ℂ → ℂ) → ℂ → ℂ
  | [], _, F => F
  | g :: gs, a, F => applyGaps gs (a+g) (gapStep a g F)

noncomputable def gapKernel (gaps : List ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  applyGaps gaps 0 (fun z => difference z y) s

@[simp] theorem gapStep_two (a : ℕ) (F : ℂ → ℂ) (s : ℂ) :
    gapStep a 2 F s = Ring.choose s (a+1) * F (a+1) - 2*F s := by
  have hi : Finset.Ico (a+1) (a+2) = {a+1} := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  simp [gapStep, hi, show Even 2 by decide]
  ring

theorem applyGaps_append (xs ys : List ℕ) (a : ℕ) (F : ℂ → ℂ) :
    applyGaps (xs ++ ys) a F = applyGaps ys (a + xs.sum) (applyGaps xs a F) := by
  induction xs generalizing a F with
  | nil => simp [applyGaps]
  | cons h t ih => simpa [applyGaps, Nat.add_assoc] using ih (a+h) (gapStep a h F)

end BilleyFahrbachTalmageClassification
