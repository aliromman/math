module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace WheelMatchings

abbrev Point := ℝ × ℝ
abbrev Edge (α : Type) := α × α

def orient (a b c : Point) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def General {n : ℕ} (p : Fin n → Point) : Prop := Function.Injective p ∧
  ∀ i j k, i < j → j < k → orient (p i) (p j) (p k) ≠ 0

/-- Proper crossing of two straight-line segments, by strict separation of their endpoints. -/
def crosses {α : Type} (p : α → Point) (e f : Edge α) : Prop :=
  orient (p e.1) (p e.2) (p f.1) * orient (p e.1) (p e.2) (p f.2) < 0 ∧
  orient (p f.1) (p f.2) (p e.1) * orient (p f.1) (p f.2) (p e.2) < 0

/-- Pair the first available vertex with each possible partner, then remove the pair. -/
def matchings {α : Type} [DecidableEq α] : ℕ → List α → List (List (Edge α))
  | 0, [] => [[]]
  | 0, _ :: _ | _ + 1, [] => []
  | m + 1, a :: rest => rest.flatMap fun b ↦
      (matchings m (rest.erase b)).map ((a, b) :: ·)

def crossingNumber {α : Type} (c : Edge α → Edge α → Bool) : List (Edge α) → ℕ
  | [] => 0
  | e :: rest => rest.countP (c e) + crossingNumber c rest

noncomputable def count {m : ℕ} (p : Fin (2*m) → Point) (k : ℕ) : ℕ := by
  classical
  exact (matchings m (List.finRange (2*m))).countP fun M ↦
    crossingNumber (fun e f ↦ decide (crosses p e f)) M == k

/-- The first point is the center. The remaining points form a regular odd polygon. -/
noncomputable def wheel (m : ℕ) (i : Fin (2*m)) : Point :=
  if i.val = 0 then (0, 0) else
    let t := 2 * Real.pi * (i.val : ℝ) / (2*(m : ℝ)-1)
    (Real.cos t, Real.sin t)

/-- The regular wheel maximizes the number of matchings at this crossing count, with the proposed value. -/
def Conjecture : Prop := ∀ m ≥ 2,
  let k := (m-1).choose 2
  count (wheel m) k = (2*m-1) * 2^(m-2) ∧
    ∀ p : Fin (2*m) → Point, General p → count p k ≤ count (wheel m) k

/-- The upper bound asserted by the proposed maximum, independent of the meaning of wheel. -/
def ProposedUpperBound : Prop := ∀ m ≥ 2, ∀ p : Fin (2*m) → Point, General p →
  count p ((m-1).choose 2) ≤ (2*m-1) * 2^(m-2)

end WheelMatchings
