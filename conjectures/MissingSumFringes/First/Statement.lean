module

public import conjectures.MissingSumFringes.Basic
public import Mathlib.Data.Finset.Max

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

/-- The first sum of a nonempty set, with value zero on the empty set.
The first sum is twice the least element of A. -/
def firstPresent (A : Finset ℕ) : ℕ := if h : A.Nonempty then 2*A.min' h else 0

/-- Conjecture 8.1 of Lazarev, Miller and O'Bryant. -/
def FirstConjecture : Prop := ∃ e : ℕ → ℝ,
  (∀ k, Tendsto (fun n ↦ conditionalMean n k (fun _ A ↦ firstPresent A)) atTop (𝓝 (e k))) ∧
  ∃ c : ℝ, 0<c ∧ Tendsto (fun k : ℕ ↦ e k / k) atTop (𝓝 c)

end MissingSumFringes
