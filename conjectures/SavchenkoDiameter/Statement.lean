module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace SavchenkoDiameter
open Finset

structure Tournament (n : ℕ) where
  arc : Fin n → Fin n → Bool
  loopless : ∀ x, arc x x = false
  orientation : ∀ {x y}, x ≠ y → arc x y = !(arc y x)

variable {n : ℕ}

def converse (T : Tournament n) : Tournament n where
  arc x y := T.arc y x
  loopless := T.loopless
  orientation h := T.orientation (Ne.symm h)

def Isomorphic (T U : Tournament n) : Prop :=
  ∃ e : Equiv.Perm (Fin n), ∀ x y, T.arc x y = U.arc (e x) (e y)

/-- The vertices reachable from `x` in at most `d` arcs. -/
def reachable (T : Tournament n) (x : Fin n) : ℕ → Finset (Fin n)
  | 0 => {x}
  | d+1 =>
    let seen := reachable T x d
    seen ∪ univ.filter (fun y ↦ ∃ z ∈ seen, T.arc z y = true)

/-- Finiteness of all directed distances also requires strong connectivity. -/
def DiameterAtMost (T : Tournament n) (d : ℕ) : Prop :=
  ∀ x, reachable T x d = univ

/-- Each step chooses an unused vertex. After the last step the arc must return to the start. -/
def completions (T : Tournament n) (start last : Fin n) (available : Finset (Fin n)) : ℕ → ℕ
  | 0 => if T.arc last start then 1 else 0
  | k+1 => ∑ y ∈ available.filter (fun y ↦ T.arc last y = true),
      completions T start y (available.erase y) k

/-- Count simple directed cycles up to cyclic rotation by starting each at its least vertex. -/
def cycles (T : Tournament n) : ℕ → ℕ
  | 0 => 0
  | k+1 => ∑ x, completions T x x (univ.filter (fun y ↦ x < y)) k

/-- Replace each vertex of the tournament on a shortest path by a transitive block.
The only increasing arcs between blocks go from a block to its successor. -/
def blowup (block : Fin n → ℕ) : Tournament n where
  arc x y := decide ((block x = block y ∧ x.val < y.val) ∨
    block x + 1 = block y ∨ block y + 1 < block x)
  loopless x := by simp
  orientation := by
    intro x y h
    have ne : x.val ≠ y.val := fun e ↦ h (Fin.ext e)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    omega

/-- Savchenko's model has two end blocks, of sizes floor and ceiling of (n-d+1)/2.
Each of the remaining d-1 blocks has one vertex. -/
def model (n d : ℕ) : Tournament n :=
  blowup (fun x ↦ min d (x.val + 1 - (n-d+1)/2))

/-- Savchenko's Conjecture 1, including the proposed equality classification in its stated range. -/
def Conjecture : Prop :=
  ∀ n ≥ 4, ∀ d ≥ 3, d < n → ∀ T : Tournament n, DiameterAtMost T d →
    ∀ k ≥ 3, k ≤ n →
      cycles (model n d) k ≤ cycles T k ∧
      (n + 3 ≤ 2*d → n-d+3 ≤ k → k ≤ d → cycles T k = cycles (model n d) k →
        Isomorphic T (model n d) ∨ Isomorphic T (converse (model n d)))

end SavchenkoDiameter
