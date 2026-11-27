module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
namespace LayeredWordPacking

open Filter Topology

/-- If a pair of adjacent letters rises, all later letters must exceed `x`. -/
def aboveCuts (x : ℕ) : List ℕ → Bool
  | a :: b :: t => (decide (b ≤ a) || (b :: t).all (x < ·)) && aboveCuts x (b :: t)
  | _ => true

/-- Cut at the strict rises. These cuts give nonincreasing layers exactly when each
letter to the left of a cut is smaller than every letter to its right. -/
def layered : List ℕ → Bool
  | [] => true
  | x :: t => aboveCuts x (x :: t) && layered t

def IsWord (k n : ℕ) (w : List ℕ) : Prop := w.length = n ∧ ∀ x ∈ w, x < k

/-- Replace letters by their ranks among the distinct letters of the word. -/
def ranks (w : List ℕ) : List ℕ := w.map fun x => (w.eraseDups.filter (· < x)).length

/-- Count positions of subsequences whose order type is in the pattern set. -/
def score (m : ℕ) (P : Finset (List ℕ)) (w : List ℕ) : ℕ :=
  (w.sublistsLen m).countP fun u => decide (ranks u ∈ P)

def Patterns (l m : ℕ) (P : Finset (List ℕ)) : Prop :=
  ∀ p ∈ P, IsWord l m p ∧ ranks p = p ∧ layered p

def LayeredMaximizer (P : Finset (List ℕ)) (m k n : ℕ) : Prop :=
  ∃ w, IsWord k n w ∧ layered w ∧ ∀ u, IsWord k n u → score m P u ≤ score m P w

/-- Barton, Conjecture 5. Patterns are represented by their ranks, starting at zero. -/
def Conjecture : Prop := ∀ l m k n : ℕ, 0 < l → 0 < m → 0 < k → 0 < n →
  ∀ P, Patterns l m P → LayeredMaximizer P m k n

noncomputable def density (P : Finset (List ℕ)) (m k n : ℕ) : ℝ :=
  ((Finset.univ.sup fun w : Fin n → Fin k => score m P ((List.ofFn w).map Fin.val) : ℕ) : ℝ) /
    n.choose m

def IteratedLimit (f : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  ∃ g : ℕ → ℝ, (∀ i > 0, Tendsto (f i) atTop (𝓝 (g i))) ∧ Tendsto g atTop (𝓝 v)

/-- Burstein–Hästö–Mansour, Conjecture 2.8. The two limit orders give the same density,
and a layered maximizing word exists for each alphabet size and word length. -/
def OriginalConjecture : Prop := ∀ l m : ℕ, 0 < l → 0 < m → ∀ P, Patterns l m P →
  (∃ v, IteratedLimit (density P m) v ∧ IteratedLimit (fun n k => density P m k n) v) ∧
    ∀ k n : ℕ, 0 < k → 0 < n → LayeredMaximizer P m k n

end LayeredWordPacking
