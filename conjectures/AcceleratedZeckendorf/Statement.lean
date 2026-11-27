module

public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.FinsetOps
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
namespace AcceleratedZeckendorf
open Finset Multiset Filter
open scoped Topology
abbrev Position := Multiset ℕ
abbrev Rule := ℕ × Bool

/-- Index zero represents the first summand, one. The following indices give 2, 3, 5, … . -/
def coin (i : ℕ) : ℕ := Nat.fib (i+2)

/-- A true flag combines consecutive indices. A false flag replaces two equal indices. -/
def input : Rule → Position
  | (i,true) => i ::ₘ (i+1) ::ₘ 0
  | (i,false) => i ::ₘ i ::ₘ 0

def output : Rule → Position
  | (i,true) => (i+2) ::ₘ 0
  | (0,false) => 1 ::ₘ 0
  | (1,false) => 0 ::ₘ 2 ::ₘ 0
  | (i+2,false) => i ::ₘ (i+3) ::ₘ 0

def cap (p : Position) : Rule → ℕ
  | (i,true) => min (p.count i) (p.count (i+1))
  | (i,false) => p.count i/2

def rules (p : Position) : Finset Rule := p.toFinset ×ˢ (univ : Finset Bool)
def moves (p : Position) := ∑ r ∈ rules p, cap p r
def play (p : Position) (r : Rule) (k : ℕ) := p-k • input r + k • output r

/-- The expected number of moves through a finite horizon. Every legal pair (type, batch size) has the same probability. -/
noncomputable def turns : ℕ → Position → ℝ
  | 0,_ => 0
  | h+1,p => if moves p=0 then 0 else
    1+(∑ r ∈ rules p, ∑ j ∈ range (cap p r), turns h (play p r (j+1)))/(moves p : ℝ)

/-- The full mean is the supremum over all observation horizons. -/
noncomputable def mean (n : ℕ) : ℝ := sSup (Set.range fun h => turns h (replicate n 0))

/-- Conjecture 1.11 of Garcia-Fernandezsesma, Miller, Rascon, Vandegrift, and Yamin. -/
def Conjecture : Prop := Tendsto (fun n : ℕ => mean n/(n:ℝ)) atTop (𝓝 0)

end AcceleratedZeckendorf
