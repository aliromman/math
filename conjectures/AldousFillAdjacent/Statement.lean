module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
namespace AldousFillAdjacent
open Finset Filter
open scoped BigOperators Topology Asymptotics

abbrev Deck (m : ℕ) := Equiv.Perm (Fin m)

/-- An absent index holds the deck. An index swaps its card and the next card
on the circle. All m+1 choices have the same probability. -/
def move {m : ℕ} : Option (Fin m) → Deck m
  | none => 1
  | some i => Equiv.swap i ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Expected time to the target deck, stopped after t steps. -/
noncomputable def stopped (m : ℕ) : ℕ → Deck m → Deck m → ℝ
  | 0,_,_ => 0
  | t+1,y,x => if x=y then 0 else 1 + (𝔼 i, stopped m t y (x * move i))

/-- The starting and target decks are independent and uniform. Taking the limit
in t gives the stationary average hitting time. -/
noncomputable def mean (m t : ℕ) : ℝ := 𝔼 y, 𝔼 x, stopped m t y x

/-- The prediction of Aldous and Fill, Example 7.22. The limit of the stopped
means specifies the full expected first hitting time. -/
def Prediction : Prop :=
  ∃ τ : ℕ → ℝ, (∀ᶠ m in atTop, Tendsto (mean m) atTop (𝓝 (τ m))) ∧
    (fun m ↦ τ m / m.factorial - (1+1/(m:ℝ))) =O[atTop] (fun m : ℕ ↦ (1:ℝ)/m^2)

end AldousFillAdjacent
