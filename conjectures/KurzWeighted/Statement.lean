module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace KurzWeighted
open Finset

abbrev Rule (V : Type*) := Finset V → ℝ

noncomputable def weighted {V : Type*} (w : V → ℝ) (q : ℝ) : Rule V :=
  fun S ↦ if q ≤ ∑ i ∈ S, w i then 1 else 0

/-- Sum the changes from no to yes over coalitions that do not contain the voter. -/
noncomputable def swings {V : Type*} [Fintype V] [DecidableEq V] (f : Rule V) (i : V) : ℝ :=
  ∑ S : Finset V, if i ∈ S then 0 else f (insert i S) - f S

noncomputable def banzhaf {V : Type*} [Fintype V] [DecidableEq V] (f : Rule V) (i : V) : ℝ :=
  swings f i / ∑ j, swings f j

/-- Kurz's weighted-game conjecture for the normalized Banzhaf index, with the last voter distinguished. -/
def Conjecture : Prop := ∃ c : ℝ, 0<c ∧ ∀ (n : ℕ), 2≤n →
  ∀ (w : Fin n → ℝ) (q : ℝ), (∀ i, 0≤w i) → 0<q → q≤∑ i,w i →
    c/n ≤ ∑ i : Fin n, |banzhaf (weighted w q) i - (if i.val+1=n then 1 else 2) / (2*(n:ℝ)-1)|

end KurzWeighted
