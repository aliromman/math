module

public import conjectures.BilleyFahrbachTalmageClassification.GapValues

/-! # Each prescribed peak is a root -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials

theorem peak_root (S : Finset ℕ) (hS : Admissible S) {j : ℕ} (hj : j ∈ S) :
    (peakPolynomial S).eval (j:ℝ) = 0 := by
  have hne : S.Nonempty := ⟨j,hj⟩
  by_cases htop : j=maxPeak S
  · simpa only [htop] using peakPolynomial_root S hS hne
  obtain ⟨hm, he, hb, _, _⟩ := last_peak_reduction hS hne
  have hj' := mem_erase.mpr ⟨htop,hj⟩
  have hjm := (hb j hj').2
  let T := S.erase (maxPeak S)
  have hT : (peakPolynomial T).eval (j:ℝ)=0 := peak_root T he hj'
  have hU : (peakPolynomial (insert (maxPeak S-1) T)).eval (j:ℝ)=0 := by
    by_cases hu : Admissible (insert (maxPeak S-1) T)
    · exact peak_root _ hu (mem_insert_of_mem hj')
    · rw [peakPolynomial_inadmissible _ hu, eval_zero]
  have hc := aeval_binomial (maxPeak S) (by omega) (j:ℂ)
  have hz : (ReflectedNewton.choosePolynomial (maxPeak S)).eval (j:ℝ) = 0 := by
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hjm, Nat.cast_zero] at hc
    have hcast : aeval ((j:ℝ):ℂ) (ReflectedNewton.choosePolynomial (maxPeak S)) =
        (((ReflectedNewton.choosePolynomial (maxPeak S)).eval (j:ℝ):ℝ):ℂ) :=
      aeval_algebraMap_apply_eq_algebraMap_eval (j:ℝ) _
    rw [Complex.ofReal_natCast, hc] at hcast
    exact_mod_cast hcast.symm
  rw [peakPolynomial_recurrence S hS hne]
  change ((C _ * ReflectedNewton.choosePolynomial (maxPeak S) - C 2 * peakPolynomial T -
    peakPolynomial (insert (maxPeak S-1) T))).eval (j:ℝ) = 0
  simp [hz,hT,hU]
termination_by maxPeak S
decreasing_by
  all_goals first | exact (last_reductions_smaller hS hne).1 | exact (last_reductions_smaller hS hne).2

end BilleyFahrbachTalmageClassification
