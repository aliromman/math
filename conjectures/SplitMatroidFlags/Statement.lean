module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace SplitMatroidFlags

open Finset

variable {E : Type} [DecidableEq E]

/-- A connected split matroid in the hypergraph presentation of Bérczi et al. -/
def ConnectedSplit (U : Finset E) (B : Finset (Finset E)) : Prop :=
  (∃ r ≤ U.card, ∃ H : Finset (Finset E × ℕ),
    (∀ h ∈ H, h.1 ⊆ U ∧ r ≤ (U \ h.1).card + h.2) ∧
    (∀ h ∈ H, ∀ g ∈ H, h ≠ g → (h.1 ∩ g.1).card + r ≤ h.2 + g.2) ∧
    ∀ b, b ∈ B ↔ b ⊆ U ∧ b.card = r ∧ ∀ h ∈ H, (b ∩ h.1).card ≤ h.2) ∧
  U.Nonempty ∧ ∀ i ∈ U, ∀ j ∈ U, i = j ∨ ∃ s : Finset E, i ∉ s ∧ j ∉ s ∧ insert i s ∈ B ∧ insert j s ∈ B

/-- A nonempty set of bases that maximizes one real linear functional on the base polytope. -/
def IsFace (B F : Finset (Finset E)) : Prop := F.Nonempty ∧
  ∃ w : E → ℝ, ∀ b, b ∈ F ↔ b ∈ B ∧ ∀ t ∈ B, ∑ i ∈ t, w i ≤ ∑ i ∈ b, w i

/-- The coordinate vector at element `i`, evaluated at `j`. -/
def unit (i j : E) : ℝ := if i = j then 1 else 0
/-- The zero–one indicator vector of a basis. -/
noncomputable def vertex (b : Finset E) : E → ℝ := ∑ i ∈ b, unit i

/-- The affine dimension of the convex hull of the face vertices, via their direction space. -/
noncomputable def dimension (F : Finset (Finset E)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ (vertex '' (F : Set (Finset E))))

/-- All exposed nonempty faces of a prescribed dimension. -/
noncomputable def faces (B : Finset (Finset E)) (i : ℕ) : Finset (Finset (Finset E)) := by
  classical exact B.powerset.filter fun F => IsFace B F ∧ dimension F = i

/-- The flag entries count chains of faces with prescribed decreasing dimensions. -/
noncomputable def flags (B : Finset (Finset E)) : List ℕ → Finset (Finset E) → ℕ
  | [], _ => 1
  | k :: ks, top => ∑ F ∈ (faces B k).filter (· ⊆ top), flags B ks F

/-- Faustini and Vargas, Problem 6.7 of the revised paper (Problem 6.5 in the first version). -/
def Conjecture : Prop := ∀ (E D : Type) [DecidableEq E] [DecidableEq D]
    (U : Finset E) (V : Finset D) (B : Finset (Finset E)) (C : Finset (Finset D)),
  ConnectedSplit U B → ConnectedSplit V C → (∀ i, (faces B i).card = (faces C i).card) →
    ∀ ranks : List ℕ, ranks.Pairwise (· > ·) → flags B ranks B = flags C ranks C

end SplitMatroidFlags
