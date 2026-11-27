module

public import conjectures.PermutationPeaks.ComplexValue
public import conjectures.PermutationPeaks.EndpointCoefficients
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Values and growth of the peak polynomial at and after its last peak. -/

@[expose] public section
namespace PermutationPeaks
open PeakPolynomials ReflectedNewton Polynomial Finset

noncomputable def leadingValue (S : Finset ℕ) : ℝ := peakCoefficient S 0

theorem leadingValue_pos (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    0 < leadingValue S := peakCoefficient_first_positive S hS hne

theorem grow_after_peak (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    ((maxPeak S : ℝ)-1)*leadingValue S ≤ (peakPolynomial S).eval ((maxPeak S : ℝ)+1) := by
  have hm := (last_peak_reduction hS hne).1
  have h := peakCoefficient_expansion S hS hne ((maxPeak S : ℝ)+1)
  simp only [add_sub_cancel_left, rising, Ring.multichoose_one, mul_one] at h
  rw [h]
  have hsum := sum_le_sum (s := range (maxPeak S-1)) (fun k hk =>
    peakCoefficient_lower_bound S hS hne k (by have := mem_range.mp hk; omega))
  rw [← peakCoefficient_endpoint S hS hne, sum_const, card_range, nsmul_eq_mul, Nat.cast_sub (by omega)] at hsum
  simpa only [leadingValue, Nat.cast_one] using hsum

theorem tail_mono (S : Finset ℕ) (hS : Admissible S) :
    MonotoneOn (fun n : ℕ => (peakPolynomial S).eval (n : ℝ)) (Set.Ici (maxPeak S)) := by
  intro i hi j _ hij
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hle ih =>
    apply (ih (hi.trans hle)).trans
    have h := peak_backward_nonnegative S hS (j+1) (by change maxPeak S ≤ i at hi; omega) 1
    simp only [backward, Nat.cast_add_one, add_sub_cancel_right] at h
    push_cast
    linarith

theorem aeval_rising (z : ℂ) (j : ℕ) :
    aeval z (risingPolynomial j) = Ring.multichoose z j := by
  simpa only [risingPolynomial, aeval_X] using
    (Ring.map_multichoose (aeval z : ℝ[X] →ₐ[ℝ] ℂ) (X : ℝ[X]) j)

theorem aeval_binomial (m : ℕ) (hm : 1 ≤ m) (z : ℂ) :
    aeval z (choosePolynomial m) = Ring.choose z (m-1) := by
  simp only [choosePolynomial, aeval_comp, map_add, aeval_X, aeval_C, aeval_rising, Ring.multichoose_eq]
  congr 1
  push_cast [Nat.cast_sub hm]
  ring

theorem max_insert {S : Finset ℕ} {n : ℕ} (h : maxPeak S ≤ n) :
    maxPeak (insert n S) = n := by
  simp [maxPeak, Finset.sup_insert] at *
  exact h

theorem extension_recurrence (S : Finset ℕ) (hS : Admissible S) (z : ℂ)
    (n : ℕ) (hn : maxPeak S+1 ≤ n) (hn' : 1 ≤ n) :
    peakValue (insert (n+1) S) z = (((peakPolynomial S).eval (n : ℝ) : ℝ) : ℂ) * Ring.choose z n -
      2 * peakValue S z - peakValue (insert n S) z := by
  have hp : n+1 ∉ S := fun hh => by have := le_maxPeak hh; omega
  have ha := admissible_insert_above S hS (n+1) (by omega) (fun i hi => by have := le_maxPeak hi; omega)
  have hb := peakPolynomial_recurrence (insert (n+1) S) ha (insert_nonempty _ _)
  rw [max_insert (by omega : maxPeak S ≤ n+1), erase_insert hp, Nat.add_sub_cancel] at hb
  unfold peakValue
  rw [hb]
  simp only [map_sub, map_mul, aeval_C, aeval_binomial _ (by omega : 1 ≤ n+1), Nat.add_sub_cancel, map_ofNat]
  rfl

theorem extension_leading (S : Finset ℕ) (hS : Admissible S) (n : ℕ)
    (hn : maxPeak S+1 ≤ n) (hn' : 1 ≤ n) :
    leadingValue (insert (n+1) S) = (peakPolynomial S).eval (n : ℝ) := by
  have hp : n+1 ∉ S := fun hh => by have := le_maxPeak hh; omega
  have ha := admissible_insert_above S hS (n+1) (by omega) (fun i hi => by have := le_maxPeak hi; omega)
  rw [leadingValue, peakCoefficient_endpoint _ ha (insert_nonempty _ _), max_insert (by omega : maxPeak S ≤ n+1),
    erase_insert hp, Nat.add_sub_cancel]

theorem adjacent_extension_zero (S : Finset ℕ) (hne : S.Nonempty) (z : ℂ) :
    peakValue (insert (maxPeak S+1) S) z = 0 := by
  have hbad : ¬ Admissible (insert (maxPeak S+1) S) := fun h =>
    h.2 _ (mem_insert_of_mem (maxPeak_mem hne)) (mem_insert_self ..)
  simp [peakValue, peakPolynomial_inadmissible _ hbad]

end PermutationPeaks
