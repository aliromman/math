module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section
open Filter Topology
namespace WagnerTreeInducibility

/-- Every internal vertex of a rooted binary tree has two children. -/
inductive Tree where
  | leaf
  | fork (left right : Tree)

namespace Tree

def leaves : Tree → ℕ
  | leaf => 1
  | fork L R => L.leaves + R.leaves

/-- Four leaves induce the balanced tree if they lie in one branch or split two and two. -/
def quartets : Tree → ℕ
  | leaf => 0
  | fork L R => L.quartets + R.quartets + L.leaves.choose 2 * R.leaves.choose 2

/-- A copy of A₅ in both branches uses a single leaf and a balanced quartet. -/
def copies : Tree → ℕ
  | leaf => 0
  | fork L R => L.copies + R.copies + L.leaves * R.quartets + R.leaves * L.quartets

/-- The even tree on `n` leaves. The zero case only supplies a value for small indices. -/
def even (n : ℕ) : Tree :=
  if 2 ≤ n then fork (even (n / 2)) (even (n - n / 2)) else leaf
termination_by n
decreasing_by all_goals omega

end Tree

/-- The four even branches and their order in Figure 6. -/
noncomputable def branch (x : ℝ) (n : ℕ) : Tree := Tree.even ⌊x * n⌋₊

noncomputable def candidate (x y z w : ℝ) (n : ℕ) : Tree :=
  .fork (branch x n) (.fork (branch y n) (.fork (branch z n) (branch w n)))

/-- The proportion of five-leaf subsets that induce A₅. -/
noncomputable def density (T : Tree) : ℝ := (T.copies : ℝ) / T.leaves.choose 5

/-- The inducibility is the limit of the greatest density among all trees of each size. -/
def IsInducibility (I : ℝ) : Prop :=
  ∃ f : ℕ → ℝ, (∀ n, 0 < n → IsGreatest {d | ∃ T : Tree, T.leaves = n ∧ density T = d} (f n)) ∧
    Tendsto f atTop (𝓝 I)

/-- Dossou-Olory and Wagner's four-branch sequence attains the inducibility of A₅. -/
def Conjecture : Prop :=
  ∃ x y z w I : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < w ∧ x + y + z + w = 1 ∧
    IsInducibility I ∧ Tendsto (fun n => density (candidate x y z w n)) atTop (𝓝 I)

end WagnerTreeInducibility
