module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Set.Card

@[expose] public section
open Finset Complex
namespace PalssonYu
noncomputable section

/-- Squared side lengths determine congruence, including for three collinear vertices. -/
def D (u v : ℂ) : ℝ := normSq (u-v)

def triangle (a b c : ℂ) : Multiset ℝ := {D a b, D b c, D c a}

def triangleTypes (S : Finset ℂ) : Finset (Multiset ℝ) :=
  S.biUnion fun a => S.biUnion fun b => S.biUnion fun c =>
    if a≠b ∧ b≠c ∧ c≠a then {triangle a b c} else ∅

/-- The set of triangle shapes of an arbitrary subset of the plane. -/
def allTypes (A : Set ℂ) : Set (Multiset ℝ) := {m | ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
  a≠b ∧ b≠c ∧ c≠a ∧ m=triangle a b c}

/-- A regular heptagon consists of the seven rotations of a noncentral point. -/
def RegularHeptagon (S : Finset ℂ) : Prop := ∃ c z ω : ℂ, z≠0 ∧ IsPrimitiveRoot ω 7 ∧
  S = univ.image fun k : Fin 7 => c + z*ω^k.val

/-- Palsson and Yu, Conjecture 10. -/
def Conjecture : Prop := (∃ S : Finset ℂ, S.card=7 ∧ (triangleTypes S).card=4) ∧
  (∀ A : Set ℂ, (allTypes A).encard=4 → A.encard≤7) ∧
  ∀ S : Finset ℂ, (S.card=7 ∧ (triangleTypes S).card=4) ↔ RegularHeptagon S

end
end PalssonYu
