module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Perm

@[expose] public section
namespace ConsecutiveThreshold
open Finset Filter Equiv
open scoped BigOperators Topology Classical

/-- The number of pairs of positions that occur in reverse order. -/
def inversions {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, (univ.filter fun j : Fin n ↦ i < j ∧ σ j < σ i).card

/-- A fixed pattern occurs at a consecutive set of positions. -/
def contains {k n : ℕ} (π : Perm (Fin k)) (σ : Perm (Fin n)) : Prop :=
  ∃ offset : ℕ, ∃ room : offset+k≤n, ∀ i j : Fin k,
    π i < π j ↔ σ ⟨offset+i,by have := i.isLt; omega⟩ < σ ⟨offset+j,by have := j.isLt; omega⟩

/-- The uniform probability on permutations with exactly m inversions. -/
noncomputable def occurrence {k : ℕ} (π : Perm (Fin k)) (n m : ℕ) : ℝ :=
  let layer := univ.filter fun σ : Perm (Fin n) ↦ inversions σ=m
  ((layer.filter (contains π)).card : ℝ)/layer.card

/-- A monotone pattern has no threshold on the side where it costs zero inversions. -/
def above (s : ℕ) (m : ℕ → ℕ) : Prop := s=0 ∨
  Tendsto (fun n : ℕ ↦ (m n : ℝ)/(n:ℝ)^(1-1/(s:ℝ))) atTop atTop

/-- Conjecture 21 of Bevan and Threlfall, with the thresholds at both ends. -/
def Conjecture : Prop := ∀ (k : ℕ) (π : Perm (Fin k)) (m : ℕ → ℕ),
  (∀ᶠ n in atTop, m n ≤ n.choose 2) → above (inversions π) m →
  above (k.choose 2-inversions π) (fun n ↦ n.choose 2-m n) →
  Tendsto (fun n ↦ occurrence π n (m n)) atTop (𝓝 1)

end ConsecutiveThreshold
