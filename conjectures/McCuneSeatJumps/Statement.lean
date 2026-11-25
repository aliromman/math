module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

@[expose] public section
open Finset MeasureTheory Set
namespace McCuneSeatJumps

abbrev Shares := Fin 3 → ℝ
abbrev Seats := Fin 3 → ℕ

/-- The open population simplex in the coordinates of the first two states. -/
def shares (x : ℝ × ℝ) : Shares := ![x.1,x.2,1-x.1-x.2]

/-- The largest-remainder rule, allowing any choice among tied remainders. -/
def Hamilton (p : Shares) (h : ℕ) (a : Seats) : Prop :=
  ∑ i, a i = h ∧ ∃ w : Finset (Fin 3),
    (∀ i, (a i : ℤ) = ⌊(h:ℝ)*p i⌋ + if i ∈ w then 1 else 0) ∧
    ∀ i ∈ w, ∀ j ∉ w, Int.fract ((h:ℝ)*p j) ≤ Int.fract ((h:ℝ)*p i)

def loss (h k : ℕ) : Set (ℝ × ℝ) := {x | (∀ i, 0 < shares x i) ∧
  ∃ a b, Hamilton (shares x) h a ∧ Hamilton (shares x) (h+k) b ∧ ∃ i, b i < a i}

/-- The unit population triangle has area one half. Twice the area of
the loss event is its probability under the uniform distribution. -/
noncomputable def probability (h k : ℕ) : ENNReal := 2 * volume (loss h k)

noncomputable def maxJump (h : ℕ) := sSup {k : ℕ | 0 < k ∧ 0 < probability h k}

/-- McCune, Conjecture 1 on the probability of a loss when the house
grows by k seats. The positive probabilities end at maxJump. -/
def Conjecture : Prop := ∀ h : ℕ, 3 ≤ h →
  (Odd h → AntitoneOn (probability h) (Set.Ici 1)) ∧
  (Even h → probability h (h/2) = 0 ∧ 0 < probability h (h/2+1) ∧
    StrictAntiOn (probability h) (Set.Icc 1 (h/2)) ∧
    StrictAntiOn (probability h) (Set.Icc (h/2+1) (maxJump h)))

end McCuneSeatJumps
