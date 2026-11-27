module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace PracticalPolygons
open Finset

/-- A sum of distinct positive divisors of a number. -/
def DivisorSum (n k : ℕ) : Prop := ∃ a : Finset ℕ,
  (∀ d∈a, 0<d ∧ d∣n) ∧ ∑ d∈a, d = k

/-- Every positive integer through a practical number is a sum of its distinct divisors. -/
def Practical (n : ℕ) : Prop := 0<n ∧ ∀ k, 0<k → k≤n → DivisorSum n k

/-- The polygonal number at a nonnegative index, including the value zero. -/
def polygonal (s n : ℕ) : ℕ := (s-2)*n.choose 2+n

def Orders (s : ℕ) : Prop := s=4 ∨ s=5 ∨ s=6 ∨ s=7 ∨ s=8 ∨ s=10

def Represented (s n : ℕ) : Prop := ∃ p x y : ℕ,
  Practical p ∧ n=p+polygonal s x+polygonal s y

/-- Conjecture 14 of Somu and Tran. -/
def Conjecture : Prop := ∀ s, Orders s → ∀ n, 0<n → Represented s n

end PracticalPolygons
