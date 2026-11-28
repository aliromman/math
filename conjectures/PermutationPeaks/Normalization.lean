module

public import conjectures.PermutationPeaks.PeakPolynomials

/-! # The counting identity for the full range in Billey–Burdzy–Sagan's theorem -/

@[expose] public section
namespace PermutationPeaks
open PeakPolynomials

/-- The count formula also holds at the final peak position, where both sides vanish. -/
theorem peak_count_normalization (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    (n : ℕ) (hn : maxPeak S ≤ n) :
    (peakCount n S : ℝ) = (2 : ℝ) ^ (n - S.card - 1) * (peakPolynomial S).eval (n : ℝ) := by
  rcases hn.eq_or_lt with rfl | hlt
  · rw [peakCount_zero_of_large_member _ S (maxPeak_mem hne) le_rfl, peakPolynomial_root S hS hne]
    simp
  · exact peakPolynomial_original_normalization S hS n hlt

end PermutationPeaks
