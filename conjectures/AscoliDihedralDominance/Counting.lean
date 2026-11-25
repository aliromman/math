module

public import conjectures.AscoliDihedralDominance.Statement
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open Finset
namespace AscoliDihedral

variable {X : Type*}

/-- An indicator for a strict surplus gains one whenever there is at least one
witness and loses at most one for each obstruction. -/
theorem indicator_bound (q p : ℕ) :
    (if 0 < q then 1 else 0) + (if q < p then 1 else 0) ≤ p + (if p < q then 1 else 0) := by
  split_ifs <;> omega

/-- A first and second moment bound for a finite family of witnesses. -/
theorem cauchy_card (S : Finset X) (q : X → ℕ) :
    (∑ x ∈ S, q x)^2 ≤ (S.filter fun x => 0 < q x).card * ∑ x ∈ S, q x ^ 2 := by
  classical
  let U := S.filter fun x => 0 < q x
  have h₁ : ∑ x ∈ U, q x = ∑ x ∈ S, q x := by
    rw [show U = _ from rfl, sum_filter]
    apply sum_congr rfl
    intro x hx
    split_ifs with h
    · rfl
    · simp [show q x = 0 by omega]
  have h₂ : ∑ x ∈ U, q x^2 = ∑ x ∈ S, q x^2 := by
    rw [show U = _ from rfl, sum_filter]
    apply sum_congr rfl
    intro x hx
    split_ifs with h
    · rfl
    · simp [show q x = 0 by omega]
  have h := sq_sum_le_card_mul_sum_sq (s := U) (f := q)
  rwa [h₁,h₂] at h

/-- If the total number of obstructions is below the guaranteed number of
witnessed objects, strictly more objects have a surplus than a deficit. -/
theorem dominance_of_moments (S : Finset X) (q p w : X → ℕ) (hw : ∀ x ∈ S, w x ≤ q x)
    (hm : (∑ x ∈ S, p x) * (∑ x ∈ S, w x ^ 2) < (∑ x ∈ S, w x)^2) :
    (S.filter fun x => q x < p x).card < (S.filter fun x => p x < q x).card := by
  classical
  have hC := cauchy_card S w
  have hlt : ∑ x ∈ S, p x < (S.filter fun x => 0 < w x).card :=
    Nat.lt_of_mul_lt_mul_right (hm.trans_le hC)
  have hb (x : X) (hx : x ∈ S) :
      (if 0 < w x then 1 else 0) + (if q x < p x then 1 else 0) ≤
      p x + (if p x < q x then 1 else 0) := by
    have := hw x hx
    have := indicator_bound (q x) (p x)
    split_ifs at * <;> omega
  have hb' := sum_le_sum hb
  simp only [sum_add_distrib, sum_boole, Nat.cast_id] at hb'
  omega

end AscoliDihedral
