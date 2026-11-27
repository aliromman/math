module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.Lattice.Nat

@[expose] public section
namespace HaslegraveBipartite

/-- An injective integer labelling realizes at most k values of the indicated edge operation. -/
def Admits {V : Type*} (G : SimpleGraph V) (op : ℤ → ℤ → ℤ) (k : ℕ) : Prop :=
  ∃ f : V ↪ ℤ, ∃ D : Finset ℤ, D.card ≤ k ∧ ∀ x y, G.Adj x y → op (f x) (f y) ∈ D

noncomputable def sumIndex {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | Admits G (· + ·) k}

noncomputable def diffIndex {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | Admits G (fun a b => |a-b|) k}

/-- Haslegrave's Question 1. Integer division expresses the ceiling of half the sum index. -/
def UnboundedGap : Prop := ∀ K : ℕ, ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
  G.Connected ∧ Nontrivial V ∧ G.Colorable 2 ∧ (sumIndex G + 1)/2 + K < diffIndex G

end HaslegraveBipartite
