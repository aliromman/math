module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section
namespace StrausBoundaryPolygon
noncomputable section
open Finset Set MeasureTheory
open scoped BigOperators

abbrev Plane := ℝ × ℝ

/-- The oriented area of the parallelogram spanned by two vectors. -/
def det (p q : Plane) : ℝ := p.1*q.2-p.2*q.1

def orient (a b c : Plane) : ℝ := det (b-a) (c-a)

/-- The shoelace area of a polygon in boundary order. -/
def polygonArea {n : ℕ} (p : Fin n → Plane) : ℝ :=
  |∑ i, det (p i) (p (finRotate n i))|/2

/-- The vertices lie on the boundary, in counterclockwise order.
    A side may include collinear boundary points. -/
def Inscribed {n : ℕ} (K : Set Plane) (p : Fin n → Plane) : Prop :=
  Function.Injective p ∧ (∀ i, p i ∈ frontier K) ∧
    (∀ i j k, i < j → j < k → 0 ≤ orient (p i) (p j) (p k)) ∧ 0 < polygonArea p

def MaximalInscribed {n : ℕ} (K : Set Plane) (p : Fin n → Plane) : Prop :=
  Inscribed K p ∧ ∀ q : Fin n → Plane, Inscribed K q → polygonArea q ≤ polygonArea p

def SharesEdge {n : ℕ} (K : Set Plane) (p : Fin n → Plane) : Prop :=
  ∃ i, segment ℝ (p i) (p (finRotate n i)) ⊆ frontier K

def regularVertex (m : ℕ) (i : Fin m) : Plane :=
  (Real.cos (2*Real.pi*i.val/m),Real.sin (2*Real.pi*i.val/m))

def regularBody (m : ℕ) : Set Plane := convexHull ℝ (range (regularVertex m))

/-- The regular (2n−1)-gon attains the least area ratio when a largest
    inscribed n-gon shares a side with the boundary. -/
def RegularPolygonMinimizes (n : ℕ) : Prop :=
  ∃ r : Fin n → Plane, MaximalInscribed (regularBody (2*n-1)) r ∧
    SharesEdge (regularBody (2*n-1)) r ∧
    ∀ (K : Set Plane), Convex ℝ K → IsCompact K → (interior K).Nonempty →
    ∀ p : Fin n → Plane, MaximalInscribed K p → SharesEdge K p →
      polygonArea r / volume.real (regularBody (2*n-1)) ≤ polygonArea p / volume.real K

/-- Straus's Conjecture 1 (1978, p. 309). -/
def Conjecture : Prop := ∀ n : ℕ, 3 ≤ n → RegularPolygonMinimizes n

end
end StrausBoundaryPolygon
