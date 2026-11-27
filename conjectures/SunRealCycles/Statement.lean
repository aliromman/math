module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section
namespace SunRealCycles

/-- A single circular order has distinct values of the operation and distinct products. -/
def HasCircle {n : ℕ} (x : Fin n → ℝ) (op : ℝ → ℝ → ℝ) : Prop :=
  ∃ p : Equiv.Perm (Fin n),
    Function.Injective (fun i => op (x (p i)) (x (p (finRotate n i)))) ∧
    Function.Injective (fun i => x (p i) * x (p (finRotate n i)))

def TwoOppositePairs {n : ℕ} (x : Fin n → ℝ) : Prop :=
  n = 4 ∧ ∃ s t : ℝ, Set.range x = {s, -s, t, -t}

/-- Sun, *Some new problems in additive combinatorics*, Conjecture 3.10 (2019). -/
def Conjecture : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), Function.Injective x → (∀ i, x i ≠ 0) →
    (2 < n →
      ¬ (TwoOppositePairs x ∨ (n = 5 ∧ ∃ r s t : ℝ, Set.range x = {r, s, -s, t, -t}) ∨
        (n = 6 ∧ ∃ r s t : ℝ, Set.range x = {r, -r, s, -s, t, -t})) →
      HasCircle x (· + ·)) ∧
    (3 < n → ¬ TwoOppositePairs x → HasCircle x (· - ·))

end SunRealCycles
