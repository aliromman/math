module

public import conjectures.PermutationPeaks.PeakPolynomials
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Billey, Fahrbach and Talmage, *Coefficients and roots of peak polynomials*,
Conjecture 1.6 (restated as Conjecture 6.4). -/

@[expose] public section
namespace PeakRootBounds
open PermutationPeaks PeakPolynomials Polynomial

/-- Evaluate the permutation peak polynomial at a complex argument. -/
noncomputable def peakValue (S : Finset ℕ) (z : ℂ) : ℂ := aeval z (peakPolynomial S)

/-- Both root bounds for every nonempty admissible set of peak positions. -/
def Conjecture : Prop := ∀ S : Finset ℕ, Admissible S → S.Nonempty → ∀ z : ℂ,
  peakValue S z = 0 → ‖z‖ ≤ maxPeak S ∧ -3 ≤ z.re

end PeakRootBounds
