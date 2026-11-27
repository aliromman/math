module

public import conjectures.GallianRusin.Die
public import Mathlib.Data.Set.Card

@[expose] public section
namespace GallianRusinGame
open Polynomial Finset

export GallianRusin (Die standard SolutionDie Plays)

/-- Gallian and Rusin, p. 256 (1979). The maximum of the minimum game sizes is four. -/
def Conjecture : Prop :=
  (∀ P, SolutionDie 30 P → ∃ k, k≤4 ∧ Plays 30 k P) ∧
    ∃ P, Plays 30 4 P ∧ ∀ k<4, ¬Plays 30 k P

end GallianRusinGame
