module

public import Mathlib.LinearAlgebra.Matrix.Permanent

@[expose] public section

namespace HwangPermanent

/-- The lower triangular board with the cells of `s` added. -/
def board (n : ℕ) (s : Finset (Fin n × Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ if j ≤ i ∨ (i, j) ∈ s then 1 else 0

/-- The first `d` cells on the antidiagonal, from the top right corner. -/
def antidiagonal (n d : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p ↦ p.1.val < d ∧ p.1.val + p.2.val + 1 = n

/-- Hwang's conjecture in Section 3 of *Permutations with partially forbidden positions*. -/
def Conjecture : Prop :=
  ∀ n d : ℕ, 0 < n → 2 * d ≤ n → ∀ s : Finset (Fin n × Fin n),
    s.card = d → (∀ p ∈ s, p.1 < p.2) →
    (board n s).permanent ≤ (board n (antidiagonal n d)).permanent

end HwangPermanent
