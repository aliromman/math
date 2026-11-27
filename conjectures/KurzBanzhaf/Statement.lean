module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace KurzBanzhaf
open Finset

/-- Losing coalitions form a downward closed family. The empty coalition loses and the full coalition wins. -/
structure VotingGame (V : Type*) [Fintype V] [DecidableEq V] where
  losing : Finset (Finset V)
  empty_loses : ∅ ∈ losing
  full_wins : univ ∉ losing
  down {S T} : S ⊆ T → T ∈ losing → S ∈ losing

namespace VotingGame
variable {V : Type*} [Fintype V] [DecidableEq V] (g : VotingGame V)

/-- Adding this voter turns the losing coalition into a winning one. -/
def swingSets (i : V) := g.losing.filter fun S ↦ insert i S ∉ g.losing

def swings (i : V) : ℕ := (g.swingSets i).card

noncomputable def banzhaf (i : V) : ℝ := (g.swings i : ℝ) / ∑ j, (g.swings j : ℝ)

end VotingGame

/-- Kurz's inverse problem for the power vector (2,...,2,1)/(2n−1). -/
def Conjecture : Prop :=
  ∀ n : ℕ, 6≤n → ∃ g : VotingGame (Fin n), ∀ i,
    g.banzhaf i = (if i.val+1=n then 1 else 2) / (2*(n:ℝ)-1)

end KurzBanzhaf
