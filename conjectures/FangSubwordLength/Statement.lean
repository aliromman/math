module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Sublists

@[expose] public section

namespace FangSubwordLength

/-- Each choice of positions occurs once in `sublists`. Equal words from different
choices of positions are counted separately. -/
def occurrences {α : Type*} [BEq α] (w v : List α) : ℕ :=
  w.sublists.count v

def MostFrequent {α : Type*} [BEq α] (w v : List α) : Prop :=
  ∀ u, occurrences w u ≤ occurrences w v

/-- Fang, Conjecture 5.7. The quotient below is the rounded-up half length. -/
def Conjecture : Prop :=
  ∀ (α : Type) [Fintype α] [BEq α] [LawfulBEq α] (w : List α), 2 ≤ w.length →
    ∃ v : List α, MostFrequent w v ∧ v.length ≤ (w.length + 1) / 2

end FangSubwordLength
