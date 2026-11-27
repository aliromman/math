module

public import conjectures.BilleyFahrbachTalmageClassification.ExtensionDensity
public import conjectures.BilleyFahrbachTalmageClassification.BinomialBound
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The four polynomials at the end of a two-gap or three-gap pattern -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset

/-- The monic polynomial with the specified integer roots, with multiplicity. -/
noncomputable def intFactors (xs : List ℤ) : ℝ[X] :=
  (xs.map (fun x => X-C (x:ℝ))).prod

/-- The peak polynomial for the first `r+1` positive even integers, for `r ≤ 3`. -/
noncomputable def baseModel : ℕ → ℝ[X]
  | 0 => intFactors [2]
  | 1 => C (1/6) * intFactors [-3,2,4]
  | 2 => C (1/30) * intFactors [2,4,6] * (X^2 + 2*X + 5)
  | 3 => C (1/2520) * intFactors [2,4,6,8] * (17*X^3 - 17*X^2 + 87*X + 105)
  | _ => 0

private noncomputable def smallChoose (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => smallChoose z n * (z-n)/(n+1)

private theorem smallChoose_eq (z : ℂ) (n : ℕ) : Ring.choose z n = smallChoose z n := by
  induction n with
  | zero => exact Ring.choose_zero_right _
  | succ n ih => rw [peak_choose_succ, ih]; rfl

private theorem three_step (z : ℂ) (y : ℝ) :
    gapStep 0 3 (fun w => difference w y) z = (y:ℂ)*(z/2)*(z-3) := by
  have hi : Ico 1 3 = ({1,2}:Finset ℕ) := by decide
  have d₂ : difference 2 y = (y:ℂ) := by
    rw [show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, difference]
    simp
    ring
  have h₃ : ¬ Even (3 : ℕ) := by decide
  norm_num [gapStep,hi,h₃,difference_one,d₂,smallChoose_eq,smallChoose]
  ring

theorem three_model (r : ℕ) (hr : r ≤ 3) (z : ℂ) (y : ℝ) :
    gapKernel (3::List.replicate r 2) z y = (y:ℂ)*(z/2)*aeval (z-1) (baseModel r) := by
  interval_cases r <;>
    norm_num [gapKernel,applyGaps,gapStep_two,three_step,smallChoose_eq,smallChoose,
      baseModel,intFactors,map_ofNat] <;> ring_nf
  simp

theorem two_model (r : ℕ) (hr : r ≤ 3) {z : ℂ} (hz : 0 < z.re) :
    gapKernel (2::List.replicate r 2) z 1 = aeval z (baseModel r) := by
  have he : gapKernel (2::List.replicate r 2) z 1 =
      applyGaps (2::List.replicate r 2) 0 (fun _ => 1) z := by
    apply applyGaps_congr _ _ _ hz
    intro w hw
    have hw' : w ≠ 0 := by rintro rfl; simp at hw
    simp [difference,Complex.zero_cpow hw']
  rw [he]
  interval_cases r <;>
    norm_num [applyGaps,gapStep_two,smallChoose_eq,smallChoose,baseModel,intFactors,map_ofNat] <;> ring_nf

end BilleyFahrbachTalmageClassification
