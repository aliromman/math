module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basic


@[expose] public section
namespace SavchenkoSix
open Finset Matrix

structure Tournament (V : Type*) where
  arc : V→V→Bool
  loopless : ∀ x, arc x x=false
  orientation : ∀ {x y}, x≠y → arc x y= !(arc y x)

variable {V : Type*} [Fintype V] [DecidableEq V]

def Tournament.adj (T : Tournament V) : Matrix V V ℤ := fun i j ↦ if T.arc i j then 1 else 0
def Tournament.sign (T : Tournament V) : Matrix V V ℤ :=
  fun i j ↦ if i=j then 0 else if T.arc i j then 1 else -1

def Regular (r : ℕ) (T : Tournament V) : Prop :=
  ∀ x, (univ.filter fun y ↦ T.arc x y).card=r

/-- Each simple directed six-cycle has six choices of its initial vertex. -/
noncomputable def orderedSix (T : Tournament V) : ℕ :=
  ∑ f : Fin 6 ↪ V, if ∀ i : Fin 6,T.arc (f i) (f (i+1))=true then 1 else 0

/-- In the regular locally transitive tournament, each vertex beats the next r clockwise vertices. -/
def carousel (r : ℕ) : Tournament (Fin (2*r+1)) where
  arc x y := decide ((x.val<y.val ∧ y.val≤x.val+r) ∨ (y.val<x.val ∧ x.val>y.val+r))
  loopless := by simp
  orientation := by
    intro x y ne
    have neq : x.val≠y.val := fun e ↦ ne (Fin.ext e)
    by_cases e : (x.val<y.val ∧ y.val≤x.val+r) ∨ (y.val<x.val ∧ x.val>y.val+r)
    · have h : ¬((y.val<x.val ∧ x.val≤y.val+r) ∨ (x.val<y.val ∧ y.val>x.val+r)) := by omega
      rw [decide_eq_true e,decide_eq_false h]
      rfl
    · have h : (y.val<x.val ∧ x.val≤y.val+r) ∨ (x.val<y.val ∧ y.val>x.val+r) := by omega
      rw [decide_eq_false e,decide_eq_true h]
      rfl

/-- Savchenko's minimum six-cycle conjecture for regular tournaments of every odd order. -/
def Conjecture : Prop := ∀ r : ℕ, ∀ T : Tournament (Fin (2*r+1)),
  Regular r T → orderedSix (carousel r) ≤ orderedSix T

end SavchenkoSix
