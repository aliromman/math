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

end GallianRusin
