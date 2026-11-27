module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Card

@[expose] public section
noncomputable section
namespace ChipShadow
open Finset

/-- Chip i is in room w(i)+2i. There are n+1 chips. -/
abbrev State (n : ℕ) := Fin (n+1) → ℕ
abbrev Block (n : ℕ) := Fin (n+1) × Fin (n+1)

def room {n : ℕ} (w : State n) (i : Fin (n+1)) := w i + 2*i.val

/-- Consecutive occupied rooms have the same suite value. -/
def suite {n : ℕ} (w : State n) (i : Fin (n+1)) := w i+i.val

def initial (n : ℕ) : State n := fun i ↦ n-i.val

def span {n : ℕ} (B : Block n) : ℕ := B.2.val-B.1.val

def IsBlock {n : ℕ} (w : State n) (B : Block n) : Prop :=
  B.1<B.2 ∧ ∀ j, suite w j=suite w B.1 ↔ B.1≤j ∧ j≤B.2

def blocks {n : ℕ} (w : State n) : Finset (Block n) := by
  classical exact univ.filter (IsBlock w)

/-- Cut i places the two displaced chips in the vacant rooms just outside the run. -/
def push {n : ℕ} (w : State n) (B : Block n) (i : ℕ) : State n := fun j ↦
  if B.1≤j ∧ j≤B.2 then if w j ≤ w B.2+i then w j+1 else w j-1 else w j

def choices {n : ℕ} (w : State n) : ℕ := ∑ B ∈ blocks w, span B

/-- Expected payoff after t moves. The process holds at an absorbing state. -/
def expect {n : ℕ} (f : State n → ℚ) : ℕ → State n → ℚ
  | 0,w => f w
  | t+1,w => if choices w=0 then f w else
    (∑ B ∈ blocks w,∑ i ∈ range (span B),expect f t (push w B i))/(choices w:ℚ)

/-- All gaps contain one empty room, except for two empty rooms after chip r. -/
def shadow {n : ℕ} (r : Fin n) (w : State n) : Prop :=
  ∀ j, w j = if j.val≤r.val then w 0 else w 0+1

def indicator {n : ℕ} (r : Fin n) (w : State n) : ℚ := by
  classical exact if shadow r w then 1 else 0

/-- Khovanova and Wang, Conjecture 7.1. -/
def Conjecture : Prop := ∀ n,0<n → ∀ r : Fin n, ∃ t₀,∀ t≥t₀,
  expect (indicator r) t (initial n) = 1/(n:ℚ)

end ChipShadow
end
