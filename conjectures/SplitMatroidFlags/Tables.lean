module

public import conjectures.SplitMatroidFlags.Examples
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace SplitMatroidFlags

open Finset

/-- Rows of the basis-exchange graph, indexed by the three elements of the basis. -/
def rows (H : Lines) (a : Three G) : Three (Finset G) :=
  a.map fun i => univ.filter (permittedSwap H a.coords i)

def trim (n m l : ℕ) (u v w : Fin 3) : ℕ :=
  exceptMask (exceptMask n (if v < u then m else 0)) (if w < u then l else 0)

def fullCode (N : Three ℕ) (h : Three (Fin 3)) : Three ℕ :=
  ⟨trim N.x N.y N.z h.x h.y h.z,trim N.y N.x N.z h.y h.x h.z,trim N.z N.x N.y h.z h.x h.y⟩

def codes (H : Lines) (a : Three G) : Finset (Three ℕ) :=
  (tuples : Finset (Three (Fin 3))).image (fullCode (rows H a).masks)

def lowRows (a : Three G) := a.map fun i => mask (univ.filter (· < i))

def ascending (low R : Three ℕ) : Bool :=
  (low.x &&& R.x) == 0 && (low.y &&& R.y) == 0 && (low.z &&& R.z) == 0

def overlapCount (R : Three ℕ) := min 2
  (((R.x &&& R.y) != 0).toNat + ((R.x &&& R.z) != 0).toNat + ((R.y &&& R.z) != 0).toNat)

def localTable (H : Lines) (a : Three G) (first : Bool) (d : ℕ) : ℕ :=
  let C := codes H a
  let low := lowRows a
  ∑ T ∈ (univ \ a.coords).powerset,
    if T.card ≤ d ∧ d ≤ T.card + 2 then
      ((C.image (fun r => r.restrict (mask T))).filter fun r =>
        T.card + overlapCount r = d ∧ (first = true → ascending low r = true)).card
    else 0

def table (H : Lines) (first : Bool) (d : ℕ) := ∑ a ∈ charts H, localTable H a first d

end SplitMatroidFlags
