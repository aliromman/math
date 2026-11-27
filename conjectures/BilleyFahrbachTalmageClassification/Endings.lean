module

public import conjectures.BilleyFahrbachTalmageClassification.Statement
public import conjectures.BilleyFahrbachTalmageClassification.GapValues
import Mathlib.Tactic.IntervalCases

/-! # Decomposition by the last gaps of a peak set -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials

theorem last_gap (S : Finset ℕ) (ha : Admissible S) (hne : S.Nonempty) :
    ∃ A : Finset ℕ, ∃ h : ℕ, Admissible A ∧ 2 ≤ h ∧ S = insert (maxPeak A+h) A := by
  obtain ⟨hm,hA,hg,he,_⟩ := last_peak_reduction ha hne
  let A := S.erase (maxPeak S)
  have hh : maxPeak A ≤ maxPeak S-2 := by
    apply Finset.sup_le
    intro j hj
    change j ≤ _
    have := (hg j hj).2
    omega
  refine ⟨A,maxPeak S-maxPeak A,hA,by omega,?_⟩
  rw [show maxPeak A+(maxPeak S-maxPeak A)=maxPeak S by omega]
  exact he.symm

/-- The first alternative has four terminal gaps of two and a nonempty prefix. -/
def Endings (S : Finset ℕ) : Prop :=
  (∃ A : Finset ℕ, Admissible A ∧ A.Nonempty ∧ S=extend A [2,2,2,2]) ∨
  (∃ r : ℕ, r≤3 ∧ S=extend ∅ (2::List.replicate r 2)) ∨
  (∃ A : Finset ℕ, ∃ h r : ℕ, Admissible A ∧ 3≤h ∧ r≤3 ∧ S=extend A (h::List.replicate r 2))

private theorem peel_twos (S : Finset ℕ) (ha : Admissible S) (r : ℕ) (hr : r≤4)
    (hn : S.Nonempty ∨ 0<r) : Endings (extend S (List.replicate r 2)) := by
  by_cases hne : S.Nonempty
  · by_cases h4 : r=4
    · exact Or.inl ⟨S,ha,hne,by subst r; rfl⟩
    · obtain ⟨A,h,hA,hh,he⟩ := last_gap S ha hne
      subst S
      by_cases h2 : h=2
      · subst h
        simpa [List.replicate_succ,extend] using peel_twos A hA (r+1) (by omega) (Or.inr (by omega))
      · exact Or.inr (Or.inr ⟨A,h,r,hA,by omega,by omega,rfl⟩)
  · have he := not_nonempty_iff_eq_empty.mp hne
    have hp : 0<r := hn.resolve_left hne
    subst S
    exact Or.inr (Or.inl ⟨r-1,by omega,by rw [← List.replicate_succ, Nat.sub_add_cancel hp]⟩)
termination_by 4-r

theorem endings_of_nonempty (S : Finset ℕ) (ha : Admissible S) (hne : S.Nonempty) : Endings S :=
  peel_twos S ha 0 (by decide) (Or.inl hne)

theorem listed_two (r : ℕ) (hr : r≤1) : Listed (extend ∅ (2::List.replicate r 2)) := by
  interval_cases r
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl (by decide))

theorem listed_three (A : Finset ℕ) (r : ℕ) (hr : r≤1) :
    Listed (extend A (3::List.replicate r 2)) := by
  by_cases hne : A.Nonempty
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨A,hne,?_⟩)))
    interval_cases r
    · exact Or.inl rfl
    · apply Or.inr
      change insert (maxPeak (insert (maxPeak A+3) A)+2) (insert (maxPeak A+3) A) = _
      rw [max_insert (by omega : maxPeak A ≤ maxPeak A+3)]
  · have he := not_nonempty_iff_eq_empty.mp hne
    subst A
    interval_cases r
    · exact Or.inr (Or.inr (Or.inl (by decide)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))

end BilleyFahrbachTalmageClassification
