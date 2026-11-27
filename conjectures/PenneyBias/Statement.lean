module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section
namespace PenneyBias
open Finset Filter

abbrev Word := List Bool

/-- All binary words with length at most the given cap. -/
def words : ℕ → Finset Word
  | 0 => {[]}
  | n+1 => insert [] (((words n).image (false :: ·)) ∪ ((words n).image (true :: ·)))

/-- Check the most recent bits first. In a tie the first word does not win. -/
def terminal (v w reversedHistory : Word) : Option Bool :=
  if w.reverse.isPrefixOf reversedHistory then some false
  else if v.reverse.isPrefixOf reversedHistory then some true else none

/-- Probability that the first word wins with at most this many additional tosses. -/
def byTime (v w : Word) (p : ℝ) : ℕ → Word → ℝ
  | 0, h => if terminal v w h = some true then 1 else 0
  | n+1, h => match terminal v w h with
    | some true => 1
    | some false => 0
    | none => (1-p)*byTime v w p n (false::h) + p*byTime v w p n (true::h)

/-- The probability of winning at some finite time in independent Bernoulli trials. -/
noncomputable def win (v w : Word) (p : ℝ) := ⨆ n : ℕ, byTime v w p n []

noncomputable def favored (n : ℕ) (p : ℝ) : Finset (Word × Word) := by
  classical
  exact ((words n) ×ˢ (words n)).filter
    fun z ↦ z.2.length < z.1.length ∧ 1/2 < win z.1 z.2 p

/-- Drexel, Peng and Richey's Conjecture 1 on the number of favorable longer words. -/
def Conjecture : Prop := ∀ᶠ n : ℕ in atTop,
  AntitoneOn (fun p ↦ (favored n p).card) (Set.Ioo 0 (1/2 : ℝ))

end PenneyBias
