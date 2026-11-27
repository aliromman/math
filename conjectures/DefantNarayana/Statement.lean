module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

namespace DefantNarayana

/-- Move one unit from coordinate `i` to coordinate `j`. -/
def transfer {n : ℕ} (p : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  fun k => (p k - (if k = i then 1 else 0)) + (if k = j then 1 else 0)

/-- The positive lattice points of an integral generalized permutohedron, in the
symmetric exchange characterization. The ordering of the point list is arbitrary. -/
def GeneralizedPermutohedron {n : ℕ} (s : List (Fin n → ℕ)) : Prop :=
  s ≠ [] ∧ s.Nodup ∧ (∀ p ∈ s, ∀ i, 0 < p i) ∧
  (∀ p ∈ s, ∀ q ∈ s, (List.ofFn p).sum = (List.ofFn q).sum) ∧
  ∀ p ∈ s, ∀ q ∈ s, ∀ i, q i < p i → ∃ j, p j < q j ∧
    transfer p i j ∈ s ∧ transfer q j i ∈ s

/-- The Narayana polynomial of degree `m`, evaluated at `z`. -/
noncomputable def narayana (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m, ((m.choose (k + 1) : ℂ) * m.choose k / m) * z ^ (k + 1)

noncomputable def narayanaSum {n : ℕ} (s : List (Fin n → ℕ)) (z : ℂ) : ℂ :=
  (s.map fun p => ((List.ofFn p).map (narayana · z)).prod).sum

/-- Defant, *Fertilitopes*, Question 6.1, second question. -/
def Conjecture : Prop := ∀ (k : ℕ) (s : List (Fin (k + 1) → ℕ)),
  GeneralizedPermutohedron s → ∀ z : ℂ, narayanaSum s z = 0 → z.im = 0

end DefantNarayana
