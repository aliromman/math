module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace FerroniFacePrefix

variable {E : Type} [DecidableEq E]

/-- The finite basis-exchange axioms. Elements in no basis are loops. -/
def IsMatroid (B : Finset (Finset E)) : Prop := B.Nonempty ∧
  ∀ X ∈ B, ∀ Y ∈ B, ∀ i ∈ X \ Y, ∃ j ∈ Y \ X, insert j (X.erase i) ∈ B

/-- The ground set includes every element of every basis, and can also contain loops. -/
def IsMatroidOn (U : Finset E) (B : Finset (Finset E)) : Prop :=
  IsMatroid B ∧ ∀ b ∈ B, b ⊆ U

/-- A nonempty face is determined by the bases that maximize one linear functional. -/
def IsFace (B F : Finset (Finset E)) : Prop := F.Nonempty ∧
  ∃ w : E → ℝ, ∀ X, X ∈ F ↔ X ∈ B ∧ ∀ Y ∈ B, ∑ i ∈ Y, w i ≤ ∑ i ∈ X, w i

/-- Coordinate vectors and the indicator vector of a basis. -/
def unit (i j : E) : ℝ := if i = j then 1 else 0

noncomputable def vertex (b : Finset E) : E → ℝ := ∑ i ∈ b, unit i

/-- The affine dimension of the convex hull of the vertex indicator vectors. -/
noncomputable def faceDimension (F : Finset (Finset E)) :=
  Module.finrank ℝ (vectorSpan ℝ (vertex '' (F : Set (Finset E))))

noncomputable def faceNumber (B : Finset (Finset E)) (i : ℕ) : ℕ := by
  classical
  exact (B.powerset.filter fun F => IsFace B F ∧ faceDimension F = i).card

/-- Ferroni and Schröter, Problem 3.5. -/
def Conjecture : Prop := ∃ c : ℕ, ∀ (E D : Type) [Fintype E] [DecidableEq E]
    [Fintype D] [DecidableEq D] (U : Finset E) (V : Finset D)
    (B : Finset (Finset E)) (C : Finset (Finset D)),
    IsMatroidOn U B → IsMatroidOn V C → (∀ i < c, faceNumber B i = faceNumber C i) →
    ∀ i, faceNumber B i = faceNumber C i

end FerroniFacePrefix
