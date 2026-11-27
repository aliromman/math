module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
namespace BaranyFurediCover

abbrev Plane := Fin 2 → ℝ
abbrev Lattice := Fin 2 → ℤ

def pt (z : Lattice) : Plane := fun i => z i

def LatticePolygon (C : Set Plane) : Prop :=
  ∃ V : Finset Lattice, C = convexHull ℝ (pt '' (V : Set Lattice))

/-- The endpoints of a string of k+1 lattice points on one line. In a convex
polygon the whole string lies between its endpoints. -/
def lengths (C : Set Plane) : Set ℕ :=
  {k | ∃ z v : Lattice, v ≠ 0 ∧ pt z ∈ C ∧ pt (z + k • v) ∈ C}

noncomputable def stringDiameter (C : Set Plane) := sSup (lengths C)

/-- Count the lattice points on a line, less one. Finite collinear subsets
give the same maximum and also include lines with just one lattice point. -/
def lineLengths (C : Set Plane) : Set ℕ :=
  {k | ∃ s : Finset Lattice, k = s.card-1 ∧ (∀ z∈s, pt z∈C) ∧ Collinear ℝ (pt '' (s : Set Lattice))}

noncomputable def diameter (C : Set Plane) := sSup (lineLengths C)

def Covers (C : Set Plane) (r : ℝ) : Prop :=
  ∀ x : Plane, ∃ z : Lattice, ∃ y ∈ C, x = pt z + r • y

noncomputable def radius (C : Set Plane) : ℝ := sInf {r : ℝ | 0 < r ∧ Covers C r}

noncomputable def area (C : Set Plane) : ℝ := (MeasureTheory.volume C).toReal

/-- The comparison in Section 3, restricted to convex lattice polygons. -/
def PolygonConjecture : Prop :=
  ∀ C : Set Plane, LatticePolygon C → (interior C).Nonempty →
    area C * radius C ≤ (1 + Real.sqrt 2) / 2 * diameter C


/-- The proposed bound for planar convex bodies, after (6) in Section 3. -/
def Conjecture : Prop :=
  ∀ C : Set Plane, IsCompact C → Convex ℝ C → (interior C).Nonempty →
    area C * radius C ≤ (1 + Real.sqrt 2) / 2 * diameter C

end BaranyFurediCover
