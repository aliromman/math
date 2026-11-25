module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section
namespace ChauveHistoryGrowth

inductive Tree where
  | tip
  | fork (left right : Tree)
  deriving DecidableEq

def Tree.leaves : Tree → ℕ
  | .tip => 1
  | .fork a b => a.leaves + b.leaves

theorem Tree.leaves_pos (t : Tree) : 0 < t.leaves := by
  induction t with
  | tip => decide
  | fork a b ha hb => simp only [leaves]; omega

def Tree.Caterpillar : Tree → Prop
  | .tip => True
  | .fork a b => (a = .tip ∧ b.Caterpillar) ∨ (b = .tip ∧ a.Caterpillar)

def Tree.Balanced : Tree → Prop
  | .tip => True
  | .fork a b => a.Balanced ∧ b.Balanced ∧
      a.leaves ≤ b.leaves + 1 ∧ b.leaves ≤ a.leaves + 1

structure Family where
  α : Type
  finite : Fintype α

instance : CoeSort Family Type := ⟨Family.α⟩
attribute [instance] Family.finite

def Family.terminal (n : ℕ) : Family := ⟨Fin (if n=0 then 1 else 0), inferInstance⟩

def Family.choice (a b : Family) : Family := ⟨a ⊕ b, inferInstance⟩

/-- An ordered pair of positive-size histories with a specified total size. -/
def Family.pairs (n : ℕ) (left right : Fin n → Family) : Family :=
  ⟨(i : Fin n) × left i × right i, inferInstance⟩

/-- The disjoint alternatives in the unranked duplication-loss grammar.
The index n counts terminal leaves after the first one. -/
noncomputable def histories (t : Tree) (n : ℕ) : Family :=
  match t with
  | .tip =>
    (Family.terminal n).choice
      (.pairs n (fun i => histories .tip i) (fun i => histories .tip (n - (i.val + 1))))
  | .fork a b =>
    let dupl := Family.pairs n (fun i => histories (.fork a b) i)
      (fun i => histories (.fork a b) (n - (i.val + 1)))
    let spec := Family.pairs n (fun i => histories a i)
      (fun i => histories b (n - (i.val + 1)))
    dupl.choice (spec.choice ((histories a n).choice (histories b n)))
termination_by (n, t.leaves)
decreasing_by
  all_goals first
    | apply Prod.Lex.left; omega
    | apply Prod.Lex.right; simp only [Tree.leaves]; have := a.leaves_pos; have := b.leaves_pos; omega

noncomputable def count (t : Tree) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Fintype.card (histories t n)

noncomputable def nthRoot (t : Tree) (n : ℕ) : ℝ := (count t n : ℝ) ^ (1 / (n : ℝ))

noncomputable def growth (t : Tree) : ℝ :=
  sSup {x | ∃ n : ℕ, 0 < n ∧ x = nthRoot t n}

open Filter Topology

/-- Conjecture 4.5, with the exponential factor specified by the actual count limit. -/
def Conjecture : Prop :=
  (∀ k, 0 < k → ∃ N, ∀ n ≥ N, ∀ t : Tree, t.leaves = k →
    (t.Caterpillar ↔ ∀ u : Tree, u.leaves = k → count u n ≤ count t n) ∧
    (t.Balanced ↔ ∀ u : Tree, u.leaves = k → count t n ≤ count u n)) ∧
  (∀ t : Tree, Tendsto (nthRoot t) atTop (𝓝 (growth t))) ∧
  (∀ C : ℝ, ∃ K, ∀ t : Tree, t.Caterpillar → K ≤ t.leaves → C * t.leaves ≤ growth t) ∧
  (∃ c C : ℝ, 0 < c ∧ ∀ t : Tree, t.Balanced →
    c * t.leaves ≤ growth t ∧ growth t ≤ C * t.leaves)

end ChauveHistoryGrowth
