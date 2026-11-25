module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
namespace SidonSetSystems
open Finset Filter
open scoped Pointwise Topology Classical

/-- Distinct unordered pairs from the family have distinct sumsets. -/
def IsSidon (F : Finset (Finset ℕ)) : Prop :=
  ∀ A∈F, ∀ B∈F, ∀ C∈F, ∀ D∈F, A+B=C+D → (A=C ∧ B=D) ∨ (A=D ∧ B=C)

/-- Maximum size of a Sidon family of k-element subsets of the first n positive integers. -/
noncomputable def extremal (k n : ℕ) : ℕ :=
  ((((Icc 1 n).powersetCard k).powerset).filter IsSidon).sup Finset.card

/-- The upper bound of Cilleruelo, Serra and Wötzel, Theorem 1.3. -/
def upperBound (k n : ℕ) : ℕ := (n-1).choose (k-1)+(n-k)

/-- Asymptotic sharpness for every fixed set size in the conjecture following Theorem 1.3. -/
def Conjecture : Prop := ∀ k : ℕ, 2≤k →
  Tendsto (fun n : ℕ => (extremal k n : ℝ)/(upperBound k n : ℝ)) atTop (𝓝 1)

end SidonSetSystems
