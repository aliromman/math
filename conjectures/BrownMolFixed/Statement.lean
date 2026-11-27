module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
noncomputable section
namespace BrownMolFixed
open Finset
variable {V : Type*}

/-- A nonempty induced subgraph is connected if it has no partition into two nonempty sides without an edge. -/
def Connected (G : SimpleGraph V) (live : V→Bool) : Prop :=
  (∃ v,live v=true) ∧ ∀ color : V→Bool,
    (∀ x y,live x=true → live y=true → G.Adj x y → color x=color y) →
      ∀ x y,live x=true → live y=true → color x=color y

/-- On live vertices, edge-constant colorings characterize the connected components. -/
def SameComponent (G : SimpleGraph V) (live : V→Bool) (x y : V) : Prop :=
  ∀ color : V→Bool, (∀ a b,live a=true → live b=true → G.Adj a b → color a=color b) →
    color x=color y

/-- Deleting a cut vertex separates two vertices that were in the same component. -/
def Cut (G : SimpleGraph V) [DecidableEq V] (v : V) : Prop :=
  ∃ x≠v, ∃ y≠v, SameComponent G (fun _ ↦ true) x y ∧
    ¬SameComponent G (fun u ↦ decide (u≠v)) x y

def bern (p : ℝ) (b : Bool) := if b then p else 1-p

/-- The probability that a nonempty connected set remains after independent vertex failures. -/
def reliability [Fintype V] (G : SimpleGraph V) (p : ℝ) : ℝ := by
  classical exact ∑ f : V→Bool,(if Connected G f then 1 else 0)*∏ v,bern p (f v)

/-- Brown and Mol's conjecture after Corollary 4.2 in The shape of node reliability. -/
def Conjecture : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  (∃ u v : V,u≠v ∧ Cut G u ∧ Cut G v) →
    ∃! p : ℝ,p∈Set.Ioo 0 1 ∧ reliability G p=p

end BrownMolFixed
end
