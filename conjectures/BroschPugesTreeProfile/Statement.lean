module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section
open Filter Topology
namespace BroschPugesTreeProfile

/-- Each internal vertex of a rooted binary tree has two children. -/
inductive Tree where
  | leaf
  | fork (left right : Tree)

namespace Tree

def leaves : Tree → ℕ
  | leaf => 1
  | fork L R => L.leaves + R.leaves

/-- Root-preserving isomorphism permits an exchange of the two children. -/
def same : Tree → Tree → Bool
  | leaf, leaf => true
  | fork A B, fork L R => (same A L && same B R) || (same A R && same B L)
  | _, _ => false

/-- Copies in a fork either use one branch or split between its two branches.
For isomorphic children the two assignments count the same subsets. -/
def copies (T S : Tree) : ℕ :=
  match T with
  | leaf => match S with
    | leaf => 1
    | fork _ _ => 0
  | fork L R => L.copies S + R.copies S + match S with
    | leaf => 0
    | fork A B => L.copies A * R.copies B + if same A B then 0 else L.copies B * R.copies A

/-- The caterpillar with `n+1` leaves. -/
def cat : ℕ → Tree
  | 0 => leaf
  | n+1 => fork leaf (cat n)

/-- The even tree with six leaves has two branches of three leaves each. -/
def evenSix : Tree := fork (cat 2) (cat 2)

noncomputable def density (S T : Tree) : ℝ := (T.copies S : ℝ) / T.leaves.choose S.leaves

end Tree

/-- Both densities come from the same strictly increasing tree sequence.
All finite pattern densities must converge along that sequence. -/
def InProfile (A B : Tree) (x y : ℝ) : Prop :=
  ∃ T : ℕ → Tree, StrictMono (fun n => (T n).leaves) ∧
    (∀ S : Tree, ∃ d : ℝ, Tendsto (fun n => S.density (T n)) atTop (𝓝 d)) ∧
    Tendsto (fun n => A.density (T n)) atTop (𝓝 x) ∧
    Tendsto (fun n => B.density (T n)) atTop (𝓝 y)

/-- Equation (12) gives the caterpillar density on the double-caterpillar curve. -/
def doubleCat (k : ℕ) (p : ℝ) : ℝ :=
  p^k + (1-p)^k + k * (p*(1-p)^(k-1) + (1-p)*p^(k-1))

/-- Equation (13) gives the even-tree density on that curve. -/
def doubleEven (p : ℝ) : ℝ := 20*p^3*(1-p)^3

/-- Brosch and Puges, Conjecture 1. The curve gives the greatest attainable
even-tree density at each of its caterpillar densities. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ p : ℝ, p ∈ Set.Icc 0 1 →
    IsGreatest {y | InProfile (.cat (k-1)) .evenSix (doubleCat k p) y} (doubleEven p)

end BroschPugesTreeProfile
