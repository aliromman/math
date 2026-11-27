module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace RestrictedUMinimum

/-- A presentation of a finite tree with a chosen root. -/
inductive Tree where
  | point
  | plant (t : Tree)
  | merge (a b : Tree)

namespace Tree

/-- Count vertices other than the root. -/
def branchesSize : Tree → ℕ
  | .point => 0
  | .plant t => t.branchesSize + 1
  | .merge a b => a.branchesSize + b.branchesSize

def order (t : Tree) : ℕ := t.branchesSize + 1

/-- Join the two roots by an edge. Keep the root of the first tree. -/
abbrev link (a b : Tree) : Tree := a.merge b.plant

def shift (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => k + i + 1

/-- Vertex zero is the root. Each pair gives one edge of the unrooted graph. -/
def edges : Tree → List (ℕ × ℕ)
  | .point => []
  | .plant t => (0, 1) :: t.edges.map (Prod.map (· + 1) (· + 1))
  | .merge a b => a.edges ++ b.edges.map (Prod.map (shift a.branchesSize) (shift a.branchesSize))

def graph (t : Tree) : SimpleGraph (Fin t.order) where
  Adj i j := i ≠ j ∧ ((i.val, j.val) ∈ t.edges ∨ (j.val, i.val) ∈ t.edges)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (t : Tree) : DecidableRel t.graph.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧
    ((i.val, j.val) ∈ t.edges ∨ (j.val, i.val) ∈ t.edges)))

def iso (a b : Tree) : Prop := Nonempty (a.graph ≃g b.graph)

end Tree

/-- Each variable records a component order. The outer variable records the cut count. -/
abbrev CutRing := Polynomial (MvPolynomial ℕ ℤ)

/-- The extra variable records the order of the root component minus one. -/
abbrev RootRing := Polynomial CutRing

noncomputable section

/-- Record the root component as a part of the partition. -/
def closeRoot : RootRing →ₗ[CutRing] CutRing :=
  Polynomial.lsum fun i => LinearMap.mulRight CutRing (Polynomial.C (MvPolynomial.X (i + 1)))

/-- The two terms keep or cut the new edge at the root. -/
def Tree.rootedU : Tree → RootRing
  | .point => 1
  | .plant t => Polynomial.X * t.rootedU +
      Polynomial.C (Polynomial.X * closeRoot t.rootedU)
  | .merge a b => a.rootedU * b.rootedU

def Tree.cutPolynomial (t : Tree) : CutRing := closeRoot t.rootedU

/-- Equality of the partition counts after each number of cuts from zero to m. -/
def SameRestrictedU (m : ℕ) (a b : Tree) : Prop :=
  ∀ j ≤ m, a.cutPolynomial.coeff j = b.cutPolynomial.coeff j

def predictedOrder (m : ℕ) : ℕ :=
  if Even m then 6 * 2 ^ (m / 2) - 2 else 18 * 2 ^ (m / 2 - 1) - 2

/-- Conjecture 15 of Aliste-Prieto, de Mier, and Zamora. -/
def Conjecture : Prop :=
  ∀ m ≥ 2, IsLeast {n : ℕ | ∃ a b : Tree,
    a.order = n ∧ b.order = n ∧ ¬ a.iso b ∧ SameRestrictedU m a b} (predictedOrder m)

end
end RestrictedUMinimum
