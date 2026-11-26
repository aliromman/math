module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Data.Set.Card

@[expose] public section
namespace GallianRusinGame
open Polynomial Finset

/-- The coefficient at i is the number of faces labeled i+1. -/
def Die (m : ℕ) (P : ℤ[X]) : Prop := (∀ i,0≤P.coeff i) ∧ P.eval 1=m

noncomputable def standard (m : ℕ) : ℤ[X] := ∑ j ∈ range m, X^j

/-- The list contains the other dice in a game with the given sum frequencies. -/
def Plays (m k : ℕ) (P : ℤ[X]) : Prop :=
  Die m P ∧ ∃ others : List ℤ[X], others.length+1=k ∧ (∀ Q ∈ others, Die m Q) ∧
    P * others.prod = standard m ^ k

def SolutionDie (m : ℕ) (P : ℤ[X]) : Prop := ∃ k, 1<k ∧ Plays m k P

/-- Gallian and Rusin, p. 256 (1979). The maximum of the minimum game sizes is four. -/
def Conjecture : Prop :=
  (∀ P, SolutionDie 30 P → ∃ k, k≤4 ∧ Plays 30 k P) ∧
    ∃ P, Plays 30 4 P ∧ ∀ k<4, ¬Plays 30 k P

end GallianRusinGame
