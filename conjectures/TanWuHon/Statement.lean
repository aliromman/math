module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Nat.Find

@[expose] public section
namespace TanWuHon
open Multiset

/-- A partition avoids f when none of its submultisets sums to f. -/
def Avoids (f : ℕ) (P : Multiset ℕ) : Prop := ∀ Q≤P, Q.sum≠f

def Partition (f n : ℕ) (P : Multiset ℕ) : Prop :=
  (∀ x∈P, 0<x) ∧ P.sum=n ∧ Avoids f P

/-- The largest number of parts in a partition of n that avoids f. -/
noncomputable def rho (f n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k ↦ ∃ P, Partition f n P ∧ P.card=k) n

/-- Every positive integer below L divides f, and L does not divide f. -/
def LeastNondivisor (f L : ℕ) : Prop := 0<L ∧ ¬L∣f ∧ ∀ s, 0<s → s<L → s∣f

/-- The explicit period threshold proposed by Tan, Wu, and Hon in §5, problem 1. -/
def Conjecture : Prop := ∀ f r L : ℕ, 0<f → f≤r → LeastNondivisor f L →
  2*(f-1)*L<r → rho f (f+r+L)=rho f (f+r)+1

end TanWuHon
