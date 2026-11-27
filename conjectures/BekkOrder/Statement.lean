module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace BekkOrder
open Finset Polynomial

/-- A dual-feasible basis for even independence order 2m. Each start supplies two adjacent nodes. -/
structure Basis (n m : ℕ) where
  start : Fin m → ℕ
  separated : ∀ i j, i < j → start i+1 < start j
  below : ∀ i, start i+1 < n

variable {n m : ℕ}

def Basis.nodes (B : Basis n m) : Finset ℕ :=
  insert n (univ.biUnion fun i ↦ {B.start i,B.start i+1})

theorem Basis.mem_nodes (B : Basis n m) (x : ℕ) :
    x∈B.nodes ↔ x=n ∨ ∃ i, x=B.start i ∨ x=B.start i+1 := by simp [Basis.nodes]

theorem Basis.nodes_card (B : Basis n m) : B.nodes.card=2*m+1 := by
  have dis : ∀ i, i∈(univ : Finset (Fin m)) → ∀ j, j∈(univ : Finset (Fin m)) → i≠j →
      Disjoint ({B.start i,B.start i+1} : Finset ℕ) {B.start j,B.start j+1} := by
    intro i _ j _ h
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [mem_insert,mem_singleton] at hx hy
    rcases lt_or_gt_of_ne h with ij|ji
    · have s := B.separated i j ij; omega
    · have s := B.separated j i ji; omega
  have top : n∉univ.biUnion (fun i ↦ ({B.start i,B.start i+1} : Finset ℕ)) := by
    simp only [mem_biUnion,mem_univ,true_and,mem_insert,mem_singleton,not_exists]
    intro i; have h := B.below i; omega
  rw [Basis.nodes,card_insert_of_notMem top,card_biUnion dis]
  simp [Nat.mul_comm]

/-- Two sorted bases first differ at the indicated left endpoint. -/
def Before (A B : Basis n m) : Prop :=
  ∃ j, (∀ i, i<j → A.start i=B.start i) ∧ A.start j<B.start j

/-- A basic count law is supported on the basis and matches the first 2m binomial moments.
The count at x equals the source's mass per word times the number of words of weight x. -/
def Feasible (B : Basis n m) (p : ℝ) : Prop :=
  ∃ w : ℕ→ℝ, (∀ x∈B.nodes, 0≤w x) ∧ ∀ P : ℝ[X], P.natDegree≤2*m →
    (∑ x∈B.nodes, w x*P.eval (x:ℝ)) =
      ∑ x∈range (n+1), ((n.choose x:ℝ)*p^x*(1-p)^(n-x))*P.eval (x:ℝ)

def ClosedFeasible (B : Basis n m) : Set ℝ := {p | p∈Set.Icc 0 1 ∧ Feasible B p}

def InteriorFeasible (B : Basis n m) : Set ℝ := {p | p∈Set.Ioo 0 1 ∧ Feasible B p}

/-- Realizable bases have a parameter interval of positive length. -/
def Realizable (B : Basis n m) : Prop :=
  ∃ a b : ℝ, a<b ∧ Set.Icc a b⊆ClosedFeasible B

def LeftOf (S T : Set ℝ) : Prop := S=T ∨ ∀ p∈S, ∀ q∈T, p≤q

/-- The order-preserving map into the nondegenerate closed intervals in Conjecture 5.2. -/
def Published : Prop := ∀ n m, 0<m → 2*m<n →
  (∀ B : Basis n m, Realizable B → ∃ a b, a<b ∧ ClosedFeasible B=Set.Icc a b) ∧
  (∀ A B : Basis n m, Realizable A → Realizable B → Before A B → LeftOf (ClosedFeasible A) (ClosedFeasible B))

/-- The convention used by the numerical tables takes the closure after removing deterministic endpoints. -/
def OrderedIntervals : Prop := ∀ n m, 0<m → 2*m<n →
  (∀ B : Basis n m, Realizable B → ∃ a b, a<b ∧ closure (InteriorFeasible B)=Set.Icc a b) ∧
  (∀ A B : Basis n m, Realizable A → Realizable B → Before A B →
    ∀ p∈closure (InteriorFeasible A), ∀ q∈closure (InteriorFeasible B), p≤q)

/-- The closed intervals of the realizable bases cover all biases, including zero and one. -/
def Covers : Prop := ∀ n m, 0<m → 2*m<n → ∀ p∈Set.Icc (0:ℝ) 1,
  ∃ B : Basis n m, Realizable B ∧ p∈closure (InteriorFeasible B)

end BekkOrder
end
