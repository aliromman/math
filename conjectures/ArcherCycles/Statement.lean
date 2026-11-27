module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Finset.Image

@[expose] public section
namespace ArcherCycles

/-- The word after the initial 1 in the standard cycle, relabeled from 0. -/
abbrev Word := List ℕ
abbrev Edge := ℕ × ℕ

/-- Join the successive entries from `start` through `middle` to `finish`. -/
def path (start : ℕ) (middle : Word) (finish : ℕ) : Finset Edge :=
  match middle with
  | [] => {(start, finish)}
  | h :: t => insert (start, h) (path h t finish)

/-- The directed permutation edges, with the distinguished initial vertex labeled 0. -/
def edges (w : Word) := path 0 (w.map Nat.succ) 0

/-- Three entries in the cycle word form a 213 pattern. -/
def Has213 (w : Word) : Prop := ∃ a b c : ℕ, [a,b,c].Sublist w ∧ b < a ∧ a < c

/-- Four edges, sorted by their source labels, form 3412 in one-line notation. -/
def Four (a b c d : Edge) : Prop :=
  a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < d.1 ∧ c.2 < d.2 ∧ d.2 < a.2 ∧ a.2 < b.2

def Has3412 (w : Word) : Prop :=
  ∃ a ∈ edges w, ∃ b ∈ edges w, ∃ c ∈ edges w, ∃ d ∈ edges w, Four a b c d

noncomputable def valid (m : ℕ) : Finset Word := by
  classical
  exact (List.range m).permutations.toFinset.filter fun w ↦ ¬ Has213 w ∧ ¬ Has3412 w

/-- The coefficient of degree m counts cycles on m+1 labels, starting with degree one. -/
noncomputable def series : PowerSeries ℚ :=
  PowerSeries.mk fun m ↦ if m = 0 then 0 else (valid m).card

/-- The ordinary generating function by the total number of labels. -/
noncomputable def ordinary : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦ match n with
    | 0 => 0
    | m+1 => (valid m).card

/-- The generating function proposed in Archer et al., expressed with the square root
whose constant coefficient is one. -/
def Conjecture : Prop := ∃ s : PowerSeries ℚ, PowerSeries.constantCoeff s = 1 ∧
  s^2 = 1 - 4 * PowerSeries.X + 4 * PowerSeries.X^3 ∧
  (1 - 2 * PowerSeries.X + s) * series = 2 * PowerSeries.X

end ArcherCycles
