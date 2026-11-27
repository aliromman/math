module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace WordPacking121

open Filter Topology

/-- An occurrence starts with an adjacent rise and ends at a later copy of its first letter. -/
def occurrences : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
    (match xs with
      | [] => 0
      | y :: _ => if x < y then xs.count x else 0) + occurrences xs

/-- The largest number of occurrences in a word of length `n` on `k` ordered letters. -/
noncomputable def maximum (k n : ℕ) : ℕ :=
  Finset.univ.sup fun w : Fin n → Fin k => occurrences ((List.ofFn w).map Fin.val)

/-- The denominator counts all choices of the adjacent pair and the final position. -/
noncomputable def density (k n : ℕ) : ℝ := (maximum k n : ℝ) / (n - 1).choose 2

def IteratedLimit (f : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  ∃ g : ℕ → ℝ, (∀ i, Tendsto (f i) atTop (𝓝 (g i))) ∧ Tendsto g atTop (𝓝 v)

/-- Burstein, Hästö and Mansour, Section 3.2 of *Packing patterns into words*. -/
def Conjecture : Prop :=
  IteratedLimit density (1 / 3) ∧ IteratedLimit (fun n k => density k n) (1 / 3)

end WordPacking121
