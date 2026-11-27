module

public import conjectures.GatzweilerKrattenthalerShift.Statement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
open Polynomial
namespace GatzweilerKrattenthalerShift

private noncomputable def geom (l : ℕ) : ℝ[X] := ∑ i ∈ Finset.range l, X^(3*i)

private theorem telescope (l : ℕ) : (1-X^3)*geom l = 1-X^(3*l) := by
  induction l with
  | zero => simp [geom]
  | succ l ih =>
    rw [geom, Finset.sum_range_succ, ← geom, mul_add, ih, Nat.mul_succ, pow_add]
    ring

private noncomputable def block (a l : ℕ) : ℝ[X] := X^a * geom l

private theorem block_zero (a l k : ℕ) (h : ∀ i : ℕ, k ≠ a+3*i) :
    (block a l).coeff k = 0 := by
  simp only [block, geom, Finset.mul_sum, ← pow_add, finsetSum_coeff, coeff_X_pow]
  exact Finset.sum_eq_zero fun i _ => ite_eq_right (h i)

private theorem block_first (a l : ℕ) (hl : 0 < l) : (block a l).coeff a = 1 := by
  simp only [block, geom, Finset.mul_sum, ← pow_add, finsetSum_coeff, coeff_X_pow]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hl)]
  · simp
  · intro i _ hi
    exact ite_eq_right (by omega)

private noncomputable def cell (s a : ℕ) : ℝ[X] :=
  block a (6*s+1) + block (a+7*s) (6*s+1) - block (a+11*s+3) (s-1)

private noncomputable def quotient (s : ℕ) :=
  cell s 0 + cell s (9*s) + cell s (10*s) + cell s (19*s)

private theorem cell_eq (s a : ℕ) : cell s a = X^a *
    ((1+(X^s)^7)*geom (6*s+1) - (X^s)^11*(X^3*geom (s-1))) := by
  simp only [cell, block, pow_add, ← pow_mul, Nat.mul_comm s]
  ring

private theorem quotient_eq (s : ℕ) : quotient s = (1+(X^s)^9)*(1+(X^s)^10) *
    ((1+(X^s)^7)*geom (6*s+1) - (X^s)^11*(X^3*geom (s-1))) := by
  simp only [quotient, cell_eq, pow_zero, one_mul, ← pow_mul, Nat.mul_comm s]
  rw [show 19*s = 9*s+10*s by omega, pow_add]
  ring

private theorem polynomial_identity (s : ℕ) (hs : 2 ≤ s) :
    (1-X^3)*(1-X^(7*s))*(1-X^(9*s))*(1-X^(10*s))*quotient s =
    (1-X^(11*s+3))*(1-X^(18*s))*(1-X^(20*s))*(1-X^(21*s)) := by
  let z : ℝ[X] := X^s
  have hp (t : ℕ) : (X:ℝ[X])^(t*s) = z^t := by rw [← pow_mul, Nat.mul_comm]
  have h₁ : (1-X^3)*geom (6*s+1) = 1-X^3*z^18 := by
    rw [telescope, show 3*(6*s+1)=3+18*s by omega, pow_add, hp]
  have h₂ : (1-X^3)*(X^3*geom (s-1)) = X^3-z^3 := by
    rw [mul_left_comm, telescope, mul_sub, mul_one, ← pow_add, show 3+3*(s-1)=3*s by omega, hp]
  rw [quotient_eq, pow_add]
  simp only [hp]
  change (1-X^3)*(1-z^7)*(1-z^9)*(1-z^10)*((1+z^9)*(1+z^10)*
    ((1+z^7)*geom (6*s+1) - z^11*(X^3*geom (s-1)))) = _
  calc
    _ = (1-z^7)*(1-z^9)*(1-z^10)*(1+z^9)*(1+z^10) *
        ((1+z^7)*((1-X^3)*geom (6*s+1)) - z^11*((1-X^3)*(X^3*geom (s-1)))) := by ring
    _ = _ := by rw [h₁,h₂]; ring

private theorem negative (s : ℕ) (hs : 2 ≤ s) (hmod : ¬ 3 ∣ s) :
    (quotient s).coeff (11*s+3) = -1 := by
  simp only [quotient, cell, coeff_add, coeff_sub, Nat.zero_add]
  simp (disch := first | omega | intro i; omega) only [block_zero, block_first]
  norm_num

/-- Use one factor at each of the four indices and no factors elsewhere. -/
def exponent (s i : ℕ) : ℕ := if i ∈ ({3,7*s,9*s,10*s} : Finset ℕ) then 1 else 0

private theorem four_factors (s m : ℕ) (hs : 2 ≤ s) :
    factors m (10*s) (exponent s) =
      (1-X^(m+3))*(1-X^(m+7*s))*(1-X^(m+9*s))*(1-X^(m+10*s)) := by
  let S : Finset ℕ := {3,7*s,9*s,10*s}
  have hS : S ⊆ Finset.Icc 1 (10*s) := by
    intro i hi
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  unfold factors
  rw [← Finset.prod_subset hS (fun i _ hi => by simp [exponent, S] at hi ⊢; tauto)]
  have E : ∀ i ∈ S, (1-(X:ℝ[X])^(m+i))^(exponent s i) = 1-X^(m+i) :=
    fun i hi => by
      change i ∈ ({3,7*s,9*s,10*s} : Finset ℕ) at hi
      simp [exponent, hi]
  rw [Finset.prod_congr rfl E]
  have h3 : 3 ∉ ({7*s,9*s,10*s} : Finset ℕ) := by simp; omega
  have h7 : 7*s ∉ ({9*s,10*s} : Finset ℕ) := by simp; omega
  have h9 : 9*s ∉ ({10*s} : Finset ℕ) := by simp; omega
  simp only [S, Finset.prod_insert h3, Finset.prod_insert h7, Finset.prod_insert h9,
    Finset.prod_singleton]
  ring

/-- Each parameter gives a polynomial quotient and a coefficient equal to minus one. -/
theorem counterexample_family (s : ℕ) (hs : 2 ≤ s) (hmod : ¬ 3 ∣ s) :
    ∃ P : ℝ[X], factors 0 (10*s) (exponent s)*P = factors (11*s) (10*s) (exponent s) ∧
      P.coeff (11*s+3) = -1 := by
  refine ⟨quotient s, ?_, negative s hs hmod⟩
  rw [four_factors s 0 hs, four_factors s (11*s) hs]
  simpa only [Nat.zero_add, show 11*s+7*s=18*s by omega, show 11*s+9*s=20*s by omega,
    show 11*s+10*s=21*s by omega] using polynomial_identity s hs

theorem not_conjecture : ¬ Conjecture := by
  intro H
  obtain ⟨P,hP,hneg⟩ := counterexample_family 2 (by decide) (by decide)
  have h := H 22 20 (by decide) (by decide) (by decide) (exponent 2) P hP 25
  norm_num at hneg
  rw [hneg] at h
  norm_num at h

/-- info: 'GatzweilerKrattenthalerShift.not_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_conjecture

end GatzweilerKrattenthalerShift
