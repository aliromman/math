module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

@[expose] public section
namespace GaoLiSandpile
open SimpleGraph Matrix

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Nonsinks (s : V) := {v : V // v ≠ s}
abbrev Config (s : V) := Nonsinks s → ℕ

def Stable (s : V) (c : Config s) : Prop := ∀ v, c v < G.degree v.val

/-- Fire an active vertex. A chip sent to the sink leaves the configuration. -/
def Fires (s : V) (c d : Config s) : Prop :=
  ∃ u : Nonsinks s, G.degree u.val ≤ c u ∧ ∀ v, d v =
    if v=u then c v-G.degree u.val else c v + if G.Adj u.val v.val then 1 else 0

/-- Definition 2.2. From each stable configuration, add chips and stabilize at c. -/
def Recurrent (s : V) (c : Config s) : Prop := Stable G s c ∧
  ∀ d : Config s, Stable G s d → ∃ e : Config s, Relation.ReflTransGen (Fires G s) (d+e) c

/-- Definition 2.3. The recurrent identity is recurrent and is zero modulo the reduced Laplacian. -/
def RecurrentIdentity (s : V) (c : Config s) : Prop := Recurrent G s c ∧
  ∃ f : Nonsinks s → ℤ, (G.lapMatrix ℤ).submatrix Subtype.val Subtype.val *ᵥ f = fun v => (c v:ℤ)

def maximal (s : V) : Config s := fun v => G.degree v.val-1

def CompleteMaximalIdentity : Prop := ∀ s, RecurrentIdentity G s (maximal G s)

def Biconnected : Prop := G.Connected ∧ ∀ x : V, (G.induce {v | v≠x}).Connected

/-- Gao and Li, Question 3.5. Every finite graph can use arbitrary vertex labels. -/
def Conjecture : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) [DecidableRel H.Adj],
  Odd (Fintype.card V) → Biconnected H → CompleteMaximalIdentity H →
  Nonempty (H ≃g cycleGraph (Fintype.card V)) ∨ H=⊤

end GaoLiSandpile
