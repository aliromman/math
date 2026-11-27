module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace PolygonEhrhart
open Finset Polynomial

/-- The next vertex in cyclic order. Edge i joins i to this vertex. -/
def next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Choose integer heights for the empty face, full face, vertices and edges.
The inequalities are the inclusions in the face lattice of an n-gon. -/
def Valid {n t : ℕ} (lo hi : Fin (t+1)) (v e : Fin n → Fin (t+1)) : Prop :=
  lo≤hi ∧ ∀ i, lo≤v i ∧ v i≤hi ∧ lo≤e i ∧ e i≤hi ∧ v i≤e i ∧ v (next i)≤e i

noncomputable def pointCount (n t : ℕ) : ℕ := by
  classical
  exact ∑ lo : Fin (t+1),∑ hi : Fin (t+1),
    ∑ v : Fin n → Fin (t+1),∑ e : Fin n → Fin (t+1),if Valid lo hi v e then 1 else 0

/-- Question 6.4 of Lundström and Saud Maia Leite. The Ehrhart polynomial
counts the lattice points in every nonnegative integer dilate. -/
def Conjecture : Prop := ∀ n≥3, ∃ P : ℚ[X],
  (∀ t : ℕ, P.eval (t:ℚ) = pointCount n t) ∧ ∀ k,0≤P.coeff k

end PolygonEhrhart
