module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Fintype.Fin

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

/-- A regular heptagon consists of the seven rotations of a noncentral point. -/
def RegularHeptagon (S : Finset ℂ) : Prop := ∃ c z ω : ℂ, z≠0 ∧ IsPrimitiveRoot ω 7 ∧
  S = univ.image fun k : Fin 7 => c + z*ω^k.val

/-- Pálsson and Yu, Conjecture 10. -/
def Conjecture : Prop := (∃ S : Finset ℂ, S.card=7 ∧ (triangleTypes S).card=4) ∧
  (∀ S : Finset ℂ, (triangleTypes S).card=4 → S.card≤7) ∧
  ∀ S : Finset ℂ, (S.card=7 ∧ (triangleTypes S).card=4) ↔ RegularHeptagon S

end
end PalssonYu
