module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Lattice.Nat

@[expose] public section
namespace ExclusiveSumBound

def SumLabels {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V ↪ ℤ, ∃ D : Finset ℤ, D.card ≤ k ∧ ∀ x y, G.Adj x y → f x + f y ∈ D

noncomputable def sumIndex {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | SumLabels G k}

/-- Proposition 1 of Haslegrave gives this equivalent definition with positive integers. -/
def ExclusiveLabels {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V ↪ ℤ, (∀ x, 0 < f x) ∧ ∃ T : Finset ℤ, (∀ t ∈ T, 0 < t) ∧ T.card ≤ k ∧
    ∀ x y, x ≠ y → (G.Adj x y ↔ f x + f y ∈ T)

noncomputable def exclusiveNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | ExclusiveLabels G k}

/-- Question 3 asks if a fixed sum index bound permits arbitrarily large exclusive sum numbers. -/
def UnboundedExclusive : Prop := ∃ k : ℕ, ∀ m : ℕ, ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
  sumIndex G ≤ k ∧ m < exclusiveNumber G

end ExclusiveSumBound
