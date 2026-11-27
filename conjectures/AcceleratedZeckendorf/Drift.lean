module

public import conjectures.AcceleratedZeckendorf.Weights
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace AcceleratedZeckendorf
open Finset

/-- Total number of unit replacements over all legal batches. -/
def batches (p : Position) := ∑ r ∈ rules p, ∑ j ∈ range (cap p r), (j+1)

private theorem triangular (k : ℕ) :
    k≤∑ j ∈ range k,(j+1) ∧ k^2≤2*∑ j ∈ range k,(j+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    constructor <;> nlinarith [ih.1, ih.2]

theorem moves_le_batches (p : Position) : moves p ≤ batches p :=
  sum_le_sum (fun r _ => (triangular (cap p r)).1)

private theorem card_le_moves (p : Position) : p.card ≤ 2*moves p+width (mass p) := by
  have h : ∑ i ∈ p.toFinset, cap p (i,false) ≤ moves p := by
    rw [moves, rules, Finset.sum_product]
    exact sum_le_sum fun i _ => single_le_sum (f := fun b => cap p (i,b))
      (fun b _ => Nat.zero_le _) (mem_univ false)
  calc
    p.card = ∑ i ∈ p.toFinset,p.count i := (Multiset.toFinset_sum_count_eq p).symm
    _ ≤ ∑ i ∈ p.toFinset,(2*cap p (i,false)+1) := by
      apply sum_le_sum
      intro i _
      simp only [cap]
      omega
    _ = 2*(∑ i ∈ p.toFinset, cap p (i,false))+p.toFinset.card := by
      rw [sum_add_distrib, mul_sum]
      simp
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left 2 h) (support_le p)

private theorem moves_squared (p : Position) :
    (moves p)^2 ≤ (2*width (mass p))*(2*batches p) := by
  have hr : (rules p).card ≤ 2*width (mass p) := by
    simpa [rules, mul_comm] using Nat.mul_le_mul_left 2 (support_le p)
  have hb : ∑ r ∈ rules p, (cap p r)^2 ≤ 2*batches p := by
    rw [batches, mul_sum]
    exact sum_le_sum (fun r _ => (triangular (cap p r)).2)
  exact (sq_sum_le_card_mul_sum_sq (s := rules p) (f := cap p)).trans (Nat.mul_le_mul hr hb)

def scale (n : ℕ) := 9*width n*(2*width n+6)

theorem work_drift (p : Position) : work p * moves p ≤ scale (mass p) * batches p := by
  let L := width (mass p)
  have hh : L * moves p ≤ L * batches p := Nat.mul_le_mul_left L (moves_le_batches p)
  have hcard : p.card*moves p ≤ 9*L*batches p := calc
    _ ≤ (2*moves p+L)*moves p := Nat.mul_le_mul_right _ (card_le_moves p)
    _ = 2*(moves p)^2+L*moves p := by ring
    _ ≤ 2*((2*L)*(2*batches p))+L*batches p :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (moves_squared p)) hh
    _ = _ := by ring
  calc
    _ ≤ ((2*L+6)*p.card)*moves p := Nat.mul_le_mul_right _ (work_le p)
    _ = (2*L+6)*(p.card*moves p) := Nat.mul_assoc _ _ _
    _ ≤ (2*L+6)*(9*L*batches p) := Nat.mul_le_mul_left _ hcard
    _ = _ := by unfold scale; dsimp [L]; ring

end AcceleratedZeckendorf
