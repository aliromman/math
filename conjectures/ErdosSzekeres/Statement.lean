module

public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace ErdosSzekeres

/-- Every three distinct points of the set are noncollinear. -/
def GeneralPosition (s : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
    (b.1 - a.1) * (c.2 - a.2) ≠ (b.2 - a.2) * (c.1 - a.1)

/-- Every set of this size in general position contains the vertices of a convex polygon. -/
def ForcesPolygon (size vertices : ℕ) : Prop :=
  ∀ s : Finset (ℝ × ℝ), s.card = size → GeneralPosition s →
    ∃ t : Finset (ℝ × ℝ), t ⊆ s ∧ t.card = vertices ∧
      ConvexIndependent ℝ (fun p : t => (p : ℝ × ℝ))

/-- The exact threshold conjectured by Erdős and Szekeres for each polygon size. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 3 ≤ k → IsLeast {n : ℕ | ForcesPolygon n k} (2 ^ (k - 2) + 1)

/-- The upper bound in the first open case. -/
def HeptagonUpperBound : Prop := ForcesPolygon 33 7

end ErdosSzekeres
