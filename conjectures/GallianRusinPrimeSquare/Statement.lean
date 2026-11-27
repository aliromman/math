module

public import conjectures.GallianRusin.Die
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section
namespace GallianRusinPrimeSquare
open Polynomial Finset

export GallianRusin (Die standard SolutionDie)

/-- Gallian and Rusin (1979), page 259, just before the final variation. -/
def Conjecture : Prop := ∀ p q : ℕ, p.Prime → q.Prime → p≠q →
  Set.ncard {P : ℤ[X] | SolutionDie (p^2*q) P}=22

end GallianRusinPrimeSquare
