module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public noncomputable section
namespace KolblSimplexRoots

abbrev Space (d : ℕ) := Fin d → ℝ

def LatticePolytope {d : ℕ} (P : Set (Space d)) : Prop :=
  ∃ V : Finset (Fin d → ℤ), P = convexHull ℝ ((fun v i => (v i : ℝ)) '' (V : Set (Fin d → ℤ)))

def Reflexive {d : ℕ} (P : Set (Space d)) : Prop :=
  LatticePolytope P ∧ 0 ∈ interior P ∧ LatticePolytope {x | ∀ y ∈ P, ∑ i, x i * y i ≤ 1}

/-- The zero dilation of a nonempty polytope consists of the origin. -/
def latticeCount {d : ℕ} (P : Set (Space d)) (n : ℕ) : ℕ :=
  if n = 0 then 1 else {v : Fin d → ℤ | (fun i => (v i : ℝ)) ∈ (fun x => n • x) '' P}.ncard

/-- The numerator of the Ehrhart series is determined by the counts in all dilations. -/
def HasHStar {d : ℕ} (P : Set (Space d)) (h : ℕ → ℕ) : Prop :=
  ∀ n, latticeCount P n = ∑ j ∈ Finset.range (d+1), h j * (n+d-j).choose d

def Unimodal (d : ℕ) (h : ℕ → ℕ) : Prop :=
  (∀ j, j < d/2 → h j ≤ h (j+1)) ∧ (∀ j, d/2 ≤ j → j < d → h (j+1) ≤ h j)

/-- The common numerator of the degree-`d` binomial basis element. -/
def basis (d j : ℕ) (z : ℂ) : ℂ := ∏ i ∈ Finset.range d, (z+i+1-j)

def ehrhart (d : ℕ) (h : ℕ → ℕ) (z : ℂ) : ℂ :=
  (∑ j ∈ Finset.range (d+1), (h j : ℂ) * basis d j z) / d.factorial

def clSpan (p : ℂ → ℂ) : Set ℂ := convexHull ℝ {z | z.re = -1/2 ∧ p z = 0}

/-- Kölbl, Conjecture 3. The standard reflexive simplex has all `d+1` numerator coefficients one. -/
def Conjecture : Prop := ∀ (d : ℕ) (P : Set (Space d)), Reflexive P →
  ∀ h, HasHStar P h → Unimodal d h → clSpan (ehrhart d h) ⊆ clSpan (ehrhart d (fun _ => 1))

end KolblSimplexRoots
