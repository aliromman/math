module

public import conjectures.GallianRusin.Die
public import Mathlib.Data.Set.Card

@[expose] public section
namespace GallianRusinDice
open Polynomial Finset

export GallianRusin (Die standard SolutionDie)

/-- Gallian and Rusin, final paragraph (1979). -/
def Conjecture : Prop := Set.ncard {P : ℤ[X] | SolutionDie 105 P}=40

end GallianRusinDice
