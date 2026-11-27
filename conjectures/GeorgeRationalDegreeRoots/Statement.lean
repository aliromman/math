module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Rat.Cast.Defs

@[expose] public section

namespace GeorgeRationalDegreeRoots

open Polynomial

noncomputable def degreePolynomial {V : Type*} [Fintype V] (G : SimpleGraph V) : ℤ[X] := by
  classical exact ∑ v, X ^ G.degree v

/-- A graph of order `n` has `x` as a degree root. -/
def Occurs (n : ℕ) (x : ℚ) : Prop :=
  ∃ (V : Type) (f : Fintype V) (G : SimpleGraph V),
    letI := f
    Fintype.card V = n ∧ (degreePolynomial G).eval₂ (Int.castRingHom ℚ) x = 0

/-- George's divisibility prediction for a rational root in lowest terms (§4.1). -/
def Conjecture : Prop :=
  ∀ n p q : ℕ, 0 < q → p.Coprime q →
    Occurs n (-(p : ℚ) / q) → p + q ∣ n

end GeorgeRationalDegreeRoots
