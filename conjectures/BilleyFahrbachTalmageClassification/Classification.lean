module

public import conjectures.BilleyFahrbachTalmageClassification.Endings
public import conjectures.BilleyFahrbachTalmageClassification.SmallRoots
public import conjectures.BilleyFahrbachTalmageClassification.FourGapObstruction

/-! # The classification by the final gaps -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials

theorem listed_good (S : Finset ℕ) (ha : Admissible S) (h : Listed S) :
    (peakPolynomial S).Splits ∧ IntegralRoots (peakPolynomial S) := by
  have htwo (r : ℕ) (hr : r≤1) : (peakPolynomial (extend ∅ (2::List.replicate r 2))).Splits ∧
      IntegralRoots (peakPolynomial (extend ∅ (2::List.replicate r 2))) := by
    rw [two_factorization _ (by omega)]
    exact baseModel_good _ hr
  rcases h with h | h | h | h | ⟨A,hne,h | h⟩
  · rw [h,show ({2}:Finset ℕ)=extend ∅ (2::List.replicate 0 2) by decide]
    exact htwo 0 (by decide)
  · rw [h,show ({2,4}:Finset ℕ)=extend ∅ (2::List.replicate 1 2) by decide]
    exact htwo 1 (by decide)
  · rw [h,show ({3}:Finset ℕ)=extend ∅ (3::List.replicate 0 2) by decide]
    exact three_good ∅ (by simp [Admissible]) 0 (by decide)
  · rw [h,show ({3,5}:Finset ℕ)=extend ∅ (3::List.replicate 1 2) by decide]
    exact three_good ∅ (by simp [Admissible]) 1 (by decide)
  · subst S
    have hA := admissible_subset ha (subset_insert (maxPeak A+3) A)
    exact three_good A hA 0 (by decide)
  · subst S
    have hA := admissible_subset ha ((subset_insert (maxPeak A+3) A).trans (subset_insert _ _))
    have he : extend A (3::List.replicate 1 2) = insert (maxPeak A+5) (insert (maxPeak A+3) A) := by
      change insert (maxPeak (insert (maxPeak A+3) A)+2) (insert (maxPeak A+3) A) = _
      rw [max_insert (by omega : maxPeak A≤maxPeak A+3)]
    rw [← he]
    exact three_good A hA 1 (by decide)

theorem classification_of_gap_obstruction
    (H : ∀ (A : Finset ℕ), Admissible A → ∀ h r : ℕ, 4≤h → r≤3 →
      ¬ (peakPolynomial (extend A (h::List.replicate r 2))).Splits) :
    Conjecture := by
  intro S ha hne
  have hn : (peakPolynomial S).Splits → Listed S := by
    intro hs
    rcases endings_of_nonempty S ha hne with ⟨A,hA,hprefix,rfl⟩ | ⟨r,hr,rfl⟩ | ⟨A,h,r,hA,hh,hr,rfl⟩
    · exact (four_gap_obstruction A hA hprefix hs).elim
    · by_cases hgood : r≤1
      · exact listed_two r hgood
      · rw [two_factorization r hr] at hs
        exact (baseModel_bad r (by omega) hr hs).elim
    · by_cases hthree : h=3
      · subst h
        by_cases hgood : r≤1
        · exact listed_three A r hgood
        · exact (three_bad A hA r (by omega) hr hs).elim
      · exact (H A hA h r (by omega) hr hs).elim
  exact ⟨⟨hn,fun h => (listed_good S ha h).1⟩,fun hs => (listed_good S ha (hn hs)).2⟩

end BilleyFahrbachTalmageClassification
