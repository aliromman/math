module

public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section
namespace GallianRusin
open Polynomial Finset

/-- The coefficient of degree `i` counts the faces labeled `i + 1`. -/
def Die (m : ℕ) (P : ℤ[X]) : Prop := (∀ i, 0 ≤ P.coeff i) ∧ P.eval 1 = m

/-- The die with face labels 1 through `m`, each used once. -/
noncomputable def standard (m : ℕ) : ℤ[X] := ∑ j ∈ range m, X ^ j

/-- A die belongs to a game with at least two dice and the standard sum frequencies. -/
def SolutionDie (m : ℕ) (P : ℤ[X]) : Prop :=
  Die m P ∧ ∃ others : List ℤ[X], others ≠ [] ∧ (∀ Q ∈ others, Die m Q) ∧
    P * others.prod = standard m ^ (others.length + 1)

/-- The die `P` belongs to a game of exactly `k` dice with the standard sum frequencies. -/
def Plays (m k : ℕ) (P : ℤ[X]) : Prop :=
  Die m P ∧ ∃ others : List ℤ[X], others.length + 1 = k ∧ (∀ Q ∈ others, Die m Q) ∧
    P * others.prod = standard m ^ k

/-- A solution die occurs in a game with at least two dice. -/
theorem solutionDie_iff_plays {m : ℕ} {P : ℤ[X]} :
    SolutionDie m P ↔ ∃ k, 1 < k ∧ Plays m k P := by
  constructor
  · rintro ⟨h, others, nonempty, dice, product⟩
    refine ⟨others.length + 1, ?_, h, others, rfl, dice, product⟩
    exact Nat.succ_lt_succ (List.length_pos_iff.mpr nonempty)
  · rintro ⟨_, size, h, others, rfl, dice, product⟩
    refine ⟨h, others, ?_, dice, product⟩
    rintro rfl
    simp at size

end GallianRusin
