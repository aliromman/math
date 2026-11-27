module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Finset.Card

@[expose] public section
namespace MatrixWidth
open Finset Filter
open scoped Topology

/-- State x represents a width of k+x. Each participant independently selects a uniform subset. -/
abbrev Draw (k d x : ℕ) := {s : Finset (Fin (k+x)) // s.card=min d (k+x)}
abbrev Outcome (k d x : ℕ) := Fin k → Draw k d x

def covered {k d x : ℕ} (f : Outcome k d x) := univ.biUnion fun i => (f i).val
def next {k d x : ℕ} (f : Outcome k d x) : ℕ := k+x-(covered f).card

noncomputable def transition (k d x y : ℕ) : ℝ :=
  ((univ.filter (fun f : Outcome k d x => next f=y)).card : ℝ) / Fintype.card (Outcome k d x)

def Stationary (P : ℕ → ℕ → ℝ) (π : ℕ → ℝ) : Prop :=
  (∀ x,0≤π x) ∧ HasSum π 1 ∧ ∀ y, HasSum (fun x => π x * P x y) (π y)

/-- Probability of missing state a during the next t steps, from x. -/
noncomputable def avoid (P : ℕ → ℕ → ℝ) (a : ℕ) : ℕ → ℕ → ℝ
  | 0,_ => 1
  | t+1,x => ∑' y, if y=a then 0 else P x y * avoid P a t y

/-- Positive recurrence requires a finite mean first return time at each state. -/
def PositiveRecurrent (P : ℕ → ℕ → ℝ) : Prop := ∀ x, Summable (fun t => avoid P x t x)

/-- The recurrence and stationary-distribution conjecture in Jacob et al., Section VIII.C,
for k>d>1, on the post-initial states of width at least k. -/
def Conjecture : Prop := ∀ k d : ℕ, 2≤d → d<k →
  PositiveRecurrent (transition k d) ∧ ∃ π, Stationary (transition k d) π

end MatrixWidth
