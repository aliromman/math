module

public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Rat.Defs

@[expose] public section
namespace ConsecutivePatternValley

def inversions : List ℕ → ℕ
  | [] => 0
  | x :: xs => xs.countP (· < x) + inversions xs

/-- Replace each entry by the number of smaller entries in this window. -/
def ranks (w : List ℕ) : List ℕ := w.map fun x => w.countP (· < x)

def occurrences (p w : List ℕ) : ℕ :=
  (List.range (w.length + 1 - p.length)).countP fun j =>
    ranks ((w.drop j).take p.length) == p

/-- Total occurrences and number of permutations in one inversion layer. -/
def layerCounts (p : List ℕ) (n m : ℕ) : ℕ × ℕ :=
  let layer := (List.range n).permutations'.filter fun w => inversions w == m
  ((layer.map (occurrences p)).sum, layer.length)

def expectation (p : List ℕ) (n m : ℕ) : ℚ :=
  (layerCounts p n m).1 / ((layerCounts p n m).2 : ℚ)

def Unimodal (N : ℕ) (f : ℕ → ℚ) : Prop := ∃ peak ≤ N,
  (∀ i j, i ≤ j → j ≤ peak → f i ≤ f j) ∧
  (∀ i j, peak ≤ i → i ≤ j → j ≤ N → f j ≤ f i)

/-- Conjecture 22 of Bevan and Threlfall, with labels starting at zero. -/
def Conjecture : Prop := ∀ k ≥ 1, ∀ p : List ℕ, p.Perm (List.range k) →
  ∀ n ≥ k+2, Unimodal (n*(n-1)/2) (expectation p n)

end ConsecutivePatternValley
