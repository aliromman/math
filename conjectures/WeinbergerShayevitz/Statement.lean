module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.LiminfLimsup

@[expose] public section
namespace WeinbergerShayevitz
open Finset Filter
open scoped BigOperators

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Observation (n : ℕ) := Fin n → Option Bool

/-- One means that the helper sends true and minus one means that it sends false. -/
def signBit (b : Bool) : ℝ := if b then 1 else -1

/-- Independently erase each input coordinate with probability `e`. -/
noncomputable def channel (e : ℝ) :
    (n : ℕ) → (Observation n → ℝ) → Word n → ℝ
  | 0,f,_ => f Fin.elim0
  | n+1,f,x =>
    (1-e)*channel e n (fun y ↦ f (Fin.cons (some (x 0)) y)) (Fin.tail x) +
    e*channel e n (fun y ↦ f (Fin.cons none y)) (Fin.tail x)

/-- The first received bit is sent. If the entire word is erased, the helper
uses a fair coin, whose expected sign is zero. -/
noncomputable def greedy : (n : ℕ) → Observation n → ℝ
  | 0,_ => 0
  | n+1,y => match y 0 with
    | some b => signBit b
    | none => greedy n (Fin.tail y)

/-- Average the powers of the consecutive guessing ranks in one tie class.
All words in this class have the same posterior probability. -/
noncomputable def rankCost (s : ℝ) (before tied : ℕ) : ℝ :=
  (∑ i ∈ range tied, ((before : ℝ) + i + 1)^s) / tied

/-- Conditional on the helper's bit, guess in decreasing order of its likelihood.
`z` is the expected sign of the bit for each possible input word. -/
noncomputable def guessingRatio {n : ℕ} (s : ℝ) (z : Word n → ℝ) : ℝ := by
  classical exact (𝔼 x : Word n,
    let above := (univ.filter (fun y ↦ z x < z y)).card
    let below := (univ.filter (fun y ↦ z y < z x)).card
    let tied := (univ.filter (fun y ↦ z y = z x)).card
    (1+z x)/2*rankCost s above tied + (1-z x)/2*rankCost s below tied) /
    rankCost s 0 (2^n)

/-- The per-length optimization in equation (5) ranges over all deterministic
one-bit functions of the erased observation. -/
noncomputable def best (n : ℕ) (e s : ℝ) : ℝ := by
  classical
  exact (univ : Finset (Observation n → Bool)).inf' univ_nonempty
    (fun f : Observation n → Bool ↦ guessingRatio s (channel e n (signBit ∘ f)))

/-- Conjecture 1 for the binary erasure channel and every positive moment. -/
def Conjecture : Prop :=
  ∀ e ∈ Set.Icc (0:ℝ) 1, ∀ s : ℝ, 0 < s →
    limsup (fun n ↦ guessingRatio s (channel e n (greedy n))) atTop =
    limsup (fun n ↦ best n e s) atTop

end WeinbergerShayevitz
