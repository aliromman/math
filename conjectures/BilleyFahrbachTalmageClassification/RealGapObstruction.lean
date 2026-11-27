module

public import conjectures.BilleyFahrbachTalmageClassification.GapMidpoint
public import conjectures.BilleyFahrbachTalmageClassification.LargeGaps
public import conjectures.BilleyFahrbachTalmageClassification.SmallGapCertificate
import Mathlib.Tactic.Linarith

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open PermutationPeaks PeakPolynomials

/-- A gap of length at least four, with at most three later gaps of length two,
forces a nonreal zero for every admissible prefix, including the empty prefix. -/
theorem real_gap_obstruction (A : Finset ℕ) (hA : Admissible A) (h r : ℕ)
    (hh : 4 ≤ h) (hr : r ≤ 3) : ¬(peakPolynomial (extend A (h::List.replicate r 2))).Splits := by
  apply gap_midpoint_obstruction A hA h r hh
  intro t ht₀ ht₁
  by_cases hlarge : 10 ≤ h
  · exact large_gap_sign A hA hlarge hr ht₀ ht₁
  · have ht : 0 < (t:ℂ).re := by
      have hh' : (4:ℝ) ≤ h := by exact_mod_cast hh
      change 0 < t
      linarith
    have hg : ∀ j ∈ h::List.replicate r 2, 2 ≤ j := by
      intro j hj
      simp only [List.mem_cons,List.mem_replicate] at hj
      rcases hj with rfl|⟨_,rfl⟩ <;> omega
    rw [normalized_re_kernel A hA _ hg ht, ← prefixIntegral_scale]
    exact prefixIntegral_pos A hA
      (continuous_const.mul (Complex.continuous_re.comp (gapKernel_continuous _ ht)))
      (fun y hy => small_gap_sign hh (by omega) hr ht₀ ht₁ hy)

end BilleyFahrbachTalmageClassification
