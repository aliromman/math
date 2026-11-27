module

public import conjectures.BilleyFahrbachTalmageClassification.Classification
public import conjectures.BilleyFahrbachTalmageClassification.RealGapObstruction

/-! # Conjecture 6.5 and the empty-set convention -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial PermutationPeaks.PeakPolynomials

/-- The six families of Conjecture 6.5 exhaust the real-rooted nonempty peak sets. -/
theorem conjecture : Conjecture :=
  classification_of_gap_obstruction real_gap_obstruction

/-- The empty peak set has polynomial one and adds one case when all admissible sets are allowed. -/
theorem all_admissible (S : Finset ℕ) (hS : Admissible S) :
    ((peakPolynomial S).Splits ↔ S=∅ ∨ Listed S) ∧
      ((peakPolynomial S).Splits → IntegralRoots (peakPolynomial S)) := by
  by_cases hne : S.Nonempty
  · obtain ⟨h,hi⟩ := conjecture S hS hne
    simpa [hne.ne_empty] using And.intro h hi
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    simp only [peakPolynomial_empty, Polynomial.Splits.one, true_or, iff_self, true_implies, true_and]
    simpa using integralRoots_const (one_ne_zero : (1:ℝ)≠0)

private theorem splits_iff_real (p : ℝ[X]) (hn : p ≠ 0) :
    p.Splits ↔ ∀ z : ℂ, aeval z p=0 → ∃ t : ℝ, (t:ℂ)=z := by
  constructor
  · intro hp z hz
    apply hp.mem_range_of_isRoot hn (i:=algebraMap ℝ ℂ)
    simpa only [IsRoot.def,eval_map_algebraMap] using hz
  · intro h
    apply Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _)
    intro z hz
    exact h z ((mem_aroots.mp hz).2)

/-- The classification stated directly in terms of the complex zeros of the counting polynomial. -/
theorem complex_zeros (S : Finset ℕ) (hS : Admissible S) :
    ((∀ z : ℂ, aeval z (peakPolynomial S) = 0 → ∃ x : ℝ, (x:ℂ) = z) ↔ S = ∅ ∨ Listed S) ∧
    ((∀ z : ℂ, aeval z (peakPolynomial S) = 0 → ∃ x : ℝ, (x:ℂ) = z) →
      ∀ z : ℂ, aeval z (peakPolynomial S) = 0 → ∃ k : ℤ, z = k) := by
  rw [← splits_iff_real (peakPolynomial S) (peakPolynomial_ne_zero S hS)]
  exact all_admissible S hS

end BilleyFahrbachTalmageClassification
