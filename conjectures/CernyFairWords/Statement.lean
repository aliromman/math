module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Count
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section
namespace CernyFairWords

/-- The number of scattered occurrences of the ordered pair of letters. -/
def pairs {α : Type*} [DecidableEq α] (a b : α) : List α → ℕ
  | [] => 0
  | x :: w => (if x = a then w.count b else 0) + pairs a b w

def Fair {α : Type*} [DecidableEq α] (w : List α) : Prop :=
  ∀ a b, pairs a b w = pairs b a w

/-- Words of length n on a fixed alphabet of size k. -/
noncomputable def count (k n : ℕ) : ℕ := Nat.card {w : Fin n → Fin k // Fair (List.ofFn w)}

/-- Černý's Conjecture 34 in “On Fair Words” (2009). -/
def Conjecture : Prop := ∀ n : ℕ, 0 < n → ∃ p : Polynomial ℤ,
  (p = 0 ∨ p.natDegree + 2 ≤ (n+1)/2) ∧ p.eval 1 = 0 ∧
    ∀ k : ℕ, 0 < k → (count k n : ℤ) = k*((k:ℤ)^((n+1)/2-1) + p.eval (k:ℤ))

end CernyFairWords
