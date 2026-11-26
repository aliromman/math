module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Order.Lattice.Nat

@[expose] public section
namespace EternalTreeDomination
open SimpleGraph
variable {V : Type*}

/-- A distance-k dominating assignment for labeled guards. Different guards may share a vertex. -/
def Dominates {I : Type*} (G : SimpleGraph V) (k : ℕ) (p : I → V) : Prop :=
  ∀ v, ∃ i, G.edist (p i) v≤k

/-- All the guards may move at each attack, each by at most k edges. -/
def Defends {I : Type*} (G : SimpleGraph V) (k : ℕ) (p : I → V) : List V → Prop
  | [] => True
  | a::as => ∃ q : I → V, (∀ i, G.edist (p i) (q i)≤k) ∧ (∃ i, q i=a) ∧ Defends G k q as

def domCount (G : SimpleGraph V) (k r : ℕ) := ∃ p : Fin r → V, Dominates G k p

def eternalCount (G : SimpleGraph V) (k r : ℕ) :=
  ∃ p : Fin r → V, ∀ attacks : List V, Defends G k p attacks

noncomputable def gamma (G : SimpleGraph V) (k : ℕ) := sInf {r | domCount G k r}
noncomputable def eternal (G : SimpleGraph V) (k : ℕ) := sInf {r | eternalCount G k r}

/-- Clow and van Bommel, Conjecture 8.2. The graph is a finite tree and k > 2. -/
def Conjecture : Prop := ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree →
  ∀ k : ℕ, 2<k → gamma T k=eternal T k → eternal T k=gamma T (k/2)

end EternalTreeDomination
