module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section
namespace TriangularSporadic

/-- The triangular number of index `a`. -/
def triangular (a : ℕ) : ℕ := a * (a + 1) / 2

/-- Two distinct positive triangular numbers have square product after adding `n`. -/
def HasPair (n : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ triangular a ≠ triangular b ∧
    ∃ c : ℤ, (triangular a : ℤ) * triangular b + n = c ^ 2

/-- Bagchi and Zhou-Zheng, *Diophantine m-tuples of Triangular Numbers*, Conjecture 12. -/
def Conjecture : Prop :=
  Set.Infinite {n : ℤ | n % 9 ≠ 2 ∧ n % 9 ≠ 5 ∧ ¬ HasPair n}

end TriangularSporadic
