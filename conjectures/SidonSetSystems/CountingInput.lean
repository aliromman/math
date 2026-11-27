module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card

@[expose] public section
namespace SidonSetSystems
open Finset
open scoped Pointwise Classical

def shapes (k n : ℕ) : Finset (Finset ℕ) :=
  ((range n).powersetCard k).filter (0∈·)

def Bad (A B C D : Finset ℕ) : Prop :=
  A+B=C+D ∧ ¬((A=C ∧ B=D) ∨ (A=D ∧ B=C))

noncomputable def neighbors (G : Finset (Finset ℕ)) (a : Finset ℕ) : Finset (Finset ℕ) :=
  G.filter fun b => a≠b ∧ ∃ A∈G, ∃ B∈G, ∃ C∈G, ∃ D∈G, Bad A B C D ∧
    a∈({A,B,C,D} : Finset (Finset ℕ)) ∧ b∈({A,B,C,D} : Finset (Finset ℕ))

def SparseShapes (k : ℕ) : Prop :=
  ∃ D : ℕ, ∀ n, ∃ G : Finset (Finset ℕ), G⊆shapes k n ∧
    (shapes k n).card≤G.card+D*(n+1)^(k-2) ∧ ∀ a∈G, (neighbors G a).card≤D

end SidonSetSystems
