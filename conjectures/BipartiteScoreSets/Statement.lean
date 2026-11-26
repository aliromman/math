module

public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
namespace BipartiteScoreSets

/-- At a pair of vertices, 0 means an arc from left to right, 1 means no edge,
and 2 means an arc from right to left. -/
abbrev Orientation (m n : ℕ) := Fin m → Fin n → Fin 3

/-- Each opponent contributes one point, plus one for a win or minus one for a loss. -/
def scores {m n : ℕ} (G : Orientation m n) : Finset ℕ :=
  Finset.univ.image (fun i => ∑ j, (2 - (G i j : ℕ))) ∪
  Finset.univ.image (fun j => ∑ i, (G i j : ℕ))

/-- Pirzada, Naikoo and Chishti, *Score sets in oriented bipartite graphs* (2006). -/
def Conjecture : Prop :=
  ∀ S : Finset ℕ, S.Nonempty → (∀ a ∈ S, 0 < a) →
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ ∃ G : Orientation m n, scores G = S

end BipartiteScoreSets
