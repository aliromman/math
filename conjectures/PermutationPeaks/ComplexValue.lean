module

public import conjectures.PermutationPeaks.PeakPolynomials
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section
namespace PermutationPeaks
open PeakPolynomials Polynomial

/-- Evaluate the permutation peak polynomial at a complex argument. -/
noncomputable def peakValue (S : Finset ℕ) (z : ℂ) : ℂ := aeval z (peakPolynomial S)

end PermutationPeaks
