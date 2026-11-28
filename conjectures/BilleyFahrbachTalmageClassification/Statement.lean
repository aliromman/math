module

public import conjectures.PermutationPeaks.PeakPolynomials
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Conjecture 6.5 of Billey, Fahrbach and Talmage -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification

open Polynomial PermutationPeaks.PeakPolynomials

/-- The two possible endings with a gap of three, and the four small peak sets. -/
def Listed (S : Finset ℕ) : Prop :=
  S = {2} ∨ S = {2, 4} ∨ S = {3} ∨ S = {3, 5} ∨
    ∃ A : Finset ℕ, A.Nonempty ∧
      (S = insert (maxPeak A + 3) A ∨ S = insert (maxPeak A + 5) (insert (maxPeak A + 3) A))

/-- Every complex zero of the peak polynomial is an integer. -/
def IntegralRoots (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, aeval z p = 0 → ∃ k : ℤ, z = k

/-- Conjecture 6.5 for the peak sets indexed in the source. -/
def Conjecture : Prop := ∀ S : Finset ℕ, Admissible S → S.Nonempty →
  ((peakPolynomial S).Splits ↔ Listed S) ∧
    ((peakPolynomial S).Splits → IntegralRoots (peakPolynomial S))

end BilleyFahrbachTalmageClassification
