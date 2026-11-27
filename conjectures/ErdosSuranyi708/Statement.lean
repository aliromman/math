module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Int.Interval
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace ErdosSuranyi708

def window (x M : ℕ) : Finset ℕ := Finset.Ioc x (x + M)

def Covers (A B : Finset ℕ) : Prop := (∏ a ∈ A, a) ∣ ∏ b ∈ B, b

/-- A uniform selection bound in every integer interval, with a lower limit
on the input integers. -/
def IntegerIntervalBound (lower : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (A : Finset ℕ) (hA : A.Nonempty),
    N ≤ A.card → (∀ a ∈ A, lower ≤ a) → ∀ x : ℤ,
      ∃ B ⊆ Finset.Ioc x (x + (A.max' hA : ℤ)),
        (B.card : ℝ) ≤ (2 + ε) * A.card ∧ (∏ a ∈ A, (a : ℤ)) ∣ ∏ b ∈ B, b

/-- The input domain and interval domain of numbered Problem 708. -/
def Conjecture : Prop := IntegerIntervalBound 2

/-- Erdős's 1992 form uses a nonnegative shift and a strict upper bound for
all input sizes greater than a threshold. -/
def Erdos1992 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (A : Finset ℕ) (hA : A.Nonempty),
    N < A.card → (∀ a ∈ A, 2 ≤ a) → ∀ x : ℕ,
      ∃ B ⊆ window x (A.max' hA), (B.card : ℝ) < (2 + ε) * A.card ∧ Covers A B

end ErdosSuranyi708
