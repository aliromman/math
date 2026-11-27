module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Basic

@[expose] public section
namespace BraunerBalancedWords

abbrev Word (n : ℕ) := ℤ → Fin n

def count {n : ℕ} (w : Word n) (a : Fin n) (start : ℤ) (len : ℕ) : ℤ :=
  ∑ i ∈ Finset.range len, if w (start+i)=a then 1 else 0

def Balanced {n : ℕ} (w : Word n) : Prop :=
  ∀ a : Fin n, ∀ x y : ℤ, ∀ len : ℕ, count w a x len ≤ count w a y len+1

def Periodic {n : ℕ} (w : Word n) (D : ℕ) : Prop := ∀ x : ℤ, w (x+D)=w x

/-- An occurrence at position x has index equal to the signed number of earlier occurrences
measured from zero. The recurrence also determines indices at negative positions. -/
def OccurrenceIndex {m : ℕ} (w : Word m) (a : Fin m) (I : ℤ → ℤ) : Prop :=
  I 0=0 ∧ ∀ x : ℤ, I (x+1)=I x+(if w x=a then 1 else 0)

/-- Replace one letter by a congruence word, up to a change of alphabet labels.
The positive stride and phase give one arithmetic progression for each replacement letter. -/
structure Substitution {m n : ℕ} (v : Word m) (w : Word n) where
  letter : Fin m
  parent : Fin n → Fin m
  onto : Function.Surjective parent
  unchanged : ∀ a≠letter, ∃! b, parent b=a
  stride : Fin n → ℕ
  positive : ∀ b, 0<stride b
  phase : Fin n → ℤ
  single : ∀ b, parent b≠letter → stride b=1
  partition : ∀ k : ℤ, ∃! b, parent b=letter ∧
    (k+phase b)%(stride b)=(stride b:ℤ)-1
  index : Fin m → ℤ → ℤ
  numbering : ∀ a, OccurrenceIndex v a (index a)
  occurs : ∀ x b, w x=b ↔ v x=parent b ∧
    (index (parent b) x+phase b)%(stride b)=(stride b:ℤ)-1

/-- A finite sequence of the substitutions from Definitions 2.7 and 2.8. -/
inductive Expansion {m : ℕ} (v : Word m) : {n : ℕ} → Word n → Prop where
  | refl : Expansion v v
  | step {n l : ℕ} {w : Word n} {z : Word l} (old : Expansion v w)
      (next : Substitution w z) : Expansion v z

/-- Brauner, Crama, Delaporte, Jost and Libralesso, Conjecture 4.1. -/
def ShortPeriod : Prop := ∀ n : ℕ, ∀ w : Word n, Balanced w →
  (∃ v : Word 2, Balanced v ∧ Expansion v w) ∨
    ∃ D : ℕ, 0<D ∧ D≤2^n-1 ∧ Periodic w D

/-- The source identifies words that differ by a common shift of all positions. -/
def Translate {n : ℕ} (u v : Word n) : Prop := ∃ s : ℤ, ∀ x, u x=v (x+s)

/-- Finiteness prediction in the abstract, for a fixed alphabet size. -/
def FiniteExceptions (n : ℕ) : Prop := ∃ L : List (Word n), ∀ w : Word n,
  Balanced w → (¬ ∃ v : Word 2, Balanced v ∧ Expansion v w) → ∃ v∈L, Translate w v

end BraunerBalancedWords
