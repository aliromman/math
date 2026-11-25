module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Data.Set.Card

@[expose] public section
namespace GallianRusinDice
open Polynomial Finset

/-- The coefficient at i is the number of faces labeled i+1. -/
def Die (m : ℕ) (P : ℤ[X]) : Prop := (∀ i,0≤P.coeff i) ∧ P.eval 1=m

noncomputable def standard (m : ℕ) : ℤ[X] := ∑ j ∈ range m, X^j

/-- A solution die is a member of a finite game with the usual sum frequencies. -/
def SolutionDie (m : ℕ) (P : ℤ[X]) : Prop :=
  Die m P ∧ ∃ others : List ℤ[X], others≠[] ∧ (∀ Q ∈ others, Die m Q) ∧
    P * others.prod = standard m ^ (others.length+1)

/-- Gallian and Rusin, final paragraph (1979). -/
def Conjecture : Prop := Set.ncard {P : ℤ[X] | SolutionDie 105 P}=40

end GallianRusinDice
