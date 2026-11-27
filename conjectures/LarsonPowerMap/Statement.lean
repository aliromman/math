module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section
namespace LarsonPowerMap

/-- The graph of a map, with orientation and loops discarded. -/
def mapGraph {α : Type*} (f : α → α) : SimpleGraph α :=
  SimpleGraph.fromRel fun x y => f x = y

/-- The number of weak components of the graph of a map. -/
noncomputable def componentCount {α : Type*} (f : α → α) : ℕ :=
  Nat.card (mapGraph f).ConnectedComponent

abbrev Sn (n : ℕ) := Equiv.Perm (Fin n)

noncomputable def N (n a : ℕ) : ℕ := componentCount (fun x : Sn n => x^a)

/-- Larson's Question 2 asks for an exponent satisfying this predicate. -/
def Maximizes (n a : ℕ) : Prop :=
  2 ≤ a ∧ a < Monoid.exponent (Sn n) ∧
    ∀ b, 2 ≤ b → b < Monoid.exponent (Sn n) → N n b ≤ N n a

/-- A complete answer lists all maximizing exponents, including empty ranges. -/
def ExactAnswer (A : ℕ → Finset ℕ) : Prop :=
  ∀ n a, a ∈ A n ↔ Maximizes n a

end LarsonPowerMap
