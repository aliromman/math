module

public import conjectures.PeakRootBounds.DiskBasis
public import conjectures.PermutationPeaks.Values
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The concavity of the reverse Newton coefficients fixes their signs two steps
to the left of the last peak. Evaluation at the last peak gives the balance
between the positive leading term and the other terms. -/

@[expose] public section
namespace PeakRootBounds
open PermutationPeaks PeakPolynomials ReflectedNewton Polynomial Finset

private theorem two_steps (f : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    backward f j x = backward f j (x+2) - 2*backward f (j+1) (x+2) +
      backward f (j+2) (x+2) := by
  simp only [backward, show x+2-1 = x+1 by ring, add_sub_cancel_right]
  ring

private theorem padded_difference (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    (j : ℕ) : backward (peakPolynomial S).eval j (maxPeak S : ℝ) =
      peakPaddedCoefficient S ((j:ℤ)-1) := by
  cases j with
  | zero => simp [backward, peakPolynomial_root S hS hne, peakPaddedCoefficient]
  | succ j =>
    simp only [Nat.cast_succ, add_sub_cancel_right, peakPaddedCoefficient, Int.toNat_natCast]
    split_ifs with h
    · rfl
    · exact backward_polynomial_vanish _ (by have := peakPolynomial_degree S; omega) _

private theorem shifted_sign (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {n : ℕ} (hm : maxPeak S = n+2) (j : ℕ) (hj : j ≤ n) :
    backward (peakPolynomial S).eval j (n : ℝ) ≤ 0 := by
  have hx : (n:ℝ)+2 = maxPeak S := by rw [hm]; push_cast; rfl
  rw [two_steps, hx]
  simp only [padded_difference S hS hne, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    add_sub_cancel_right, show (j:ℤ)+2-1=j+1 by ring]
  have h := (peakCoefficient_symmetric_concave S hS hne).concave (j:ℤ) (by omega) (by omega)
  linarith

private theorem shifted_top (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {n : ℕ} (hm : maxPeak S = n+2) :
    0 < backward (peakPolynomial S).eval (n+1) (n : ℝ) := by
  have hx : (n:ℝ)+2 = maxPeak S := by rw [hm]; push_cast; rfl
  have hd := peakPolynomial_degree S
  rw [two_steps, hx, backward_polynomial_vanish _ (n := n+1+1) (by omega),
    backward_polynomial_vanish _ (n := n+1+2) (by omega), mul_zero, sub_zero, add_zero]
  change 0 < peakCoefficient S n
  have hlo := peakCoefficient_lower_bound S hS hne n (by omega)
  rw [← peakCoefficient_endpoint S hS hne] at hlo
  exact (peakCoefficient_first_positive S hS hne).trans_le hlo

private theorem newton_complex (P : ℝ[X]) {n : ℕ} (hd : P.natDegree ≤ n+1) (z : ℂ) :
    aeval z P = ∑ j ∈ range (n+2),
      ((backward P.eval j (n : ℝ) : ℝ) : ℂ) * Ring.multichoose (z-n) j := by
  have h := congrArg (aeval z : ℝ[X] →ₐ[ℝ] ℂ) (backward_newton_expansion P (n : ℝ))
  simp only [newtonPolynomial, map_sum, map_mul, aeval_C, aeval_comp, map_sub,
    aeval_X, aeval_rising] at h
  rw [← h]
  apply sum_subset (range_mono (by omega))
  intro j _ hj
  rw [backward_polynomial_vanish _ (by simp at hj; omega)]
  simp

private theorem balance (P : ℝ[X]) {n : ℕ} (hd : P.natDegree ≤ n+1)
    (hr : P.eval ((n:ℝ)+2) = 0) :
    ∑ j ∈ range (n+2), backward P.eval j (n : ℝ) * (j+1 : ℝ) = 0 := by
  have h := backward_newton_formula P (n : ℝ) 2
  rw [hr] at h
  simp only [rising, Ring.multichoose_two] at h
  rw [h]
  symm
  apply sum_subset (range_mono (by omega))
  intro j _ hj
  rw [backward_polynomial_vanish _ (by simp at hj; omega), zero_mul]

theorem peak_disk (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    {z : ℂ} (hz : (maxPeak S : ℝ) < ‖z‖) : peakValue S z ≠ 0 := by
  let n := maxPeak S-2
  have hm : maxPeak S = n+2 := by have := (last_peak_reduction hS hne).1; dsimp [n]; omega
  have hx : (n:ℝ)+2 = maxPeak S := by rw [hm]; push_cast; rfl
  have hd : (peakPolynomial S).natDegree ≤ n+1 := by have := peakPolynomial_degree S; omega
  unfold peakValue
  rw [newton_complex _ hd]
  apply disk_nonzero (hx ▸ hz) (fun j => backward (peakPolynomial S).eval j (n : ℝ))
    (shifted_sign S hS hne hm) (shifted_top S hS hne hm)
  exact balance _ hd (hx ▸ peakPolynomial_root S hS hne)

end PeakRootBounds
