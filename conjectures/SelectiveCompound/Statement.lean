module

public import Mathlib.Order.Lattice.Nat

@[expose] public section
namespace SelectiveCompound

/-- The depth of a position is the maximum number of moves from it to a terminal position. -/
structure Game (α : Type*) where
  move : α → α → Prop
  depth : α → ℕ
  shorter {a b} : move a b → depth b < depth a
  deepest (a) : 0 < depth a → ∃ b, move a b ∧ depth b + 1 = depth a

namespace Game
variable {α : Type*} (G : Game α)

/-- A selective move changes the auxiliary heap, the game, or both. -/
def Option (p q : α × ℕ) : Prop :=
  (q.1 = p.1 ∧ q.2 < p.2) ∨ (G.move p.1 q.1 ∧ q.2 ≤ p.2)

theorem option_decreases {p q : α × ℕ} (h : G.Option p q) :
    G.depth q.1 + q.2 < G.depth p.1 + p.2 := by
  obtain ⟨h, hk⟩ | ⟨h, hk⟩ := h
  · rw [h]
    omega
  · have := G.shorter h
    omega

/-- The Grundy value is the least natural number outside the set of option values. -/
noncomputable def grundy (p : α × ℕ) : ℕ :=
  sInf {n | ¬ ∃ q, ∃ _ : G.Option p q, grundy q = n}
termination_by G.depth p.1 + p.2
decreasing_by exact G.option_decreases ‹_›

/-- The property in Question 3, with the auxiliary heap size as the variable. -/
def Stabilizes (a : α) : Prop :=
  ∃ k₀ : ℕ, ∀ k > k₀, G.grundy (a, k) = k + G.depth a

end Game
end SelectiveCompound
