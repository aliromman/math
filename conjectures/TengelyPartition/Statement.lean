module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace TengelyPartition
open Finset

/-- Fix the multiplicities of the parts a and two. The unused weight consists of ones. -/
def parts (a n : ℕ) : ℕ :=
  ∑ z∈range (n/a+1), ((range (n+1)).filter fun y ↦ 2*y+a*z≤n).card

/-- Tengely and Ulas, Conjecture 4.6, with both partition arguments strictly positive. -/
def Conjecture : Prop := ∀ a b : ℕ, 3≤a → a<b →
    {v : ℕ×ℕ | 0<v.1 ∧ 0<v.2 ∧ parts a v.1=parts b v.2}.Infinite

end TengelyPartition
