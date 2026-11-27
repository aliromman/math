module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

@[expose] public section
namespace FeketeEquidistribution
open Finset Polynomial

def unitsTo (n : ℕ) : Finset ℕ := (Icc 1 n).filter fun a ↦ a.Coprime n

noncomputable def fekete (n : ℕ) : ℤ[X] := ∑ a ∈ (range n).filter (fun a ↦ a.Coprime n), X ^ a

def residueCount (n d s : ℕ) : ℕ :=
  ((unitsTo n).filter fun a ↦ a % d = s % d).card

def Equidistributed (n d : ℕ) : Prop :=
  ∀ a ∈ Icc 1 d, a.Coprime (d.gcd n) →
  ∀ b ∈ Icc 1 d, b.Coprime (d.gcd n) → residueCount n d a = residueCount n d b

/-- Chidambaram, Mináč, Nguyen and Tân, Conjecture 2.11. -/
def Conjecture : Prop := ∀ n : ℕ, 0 < n → Squarefree n →
  ∀ d : ℕ, 1 < d → ¬d ∣ n → (cyclotomic d ℤ ∣ fekete n ↔ Equidistributed n d)

end FeketeEquidistribution
