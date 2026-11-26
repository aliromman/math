module

public import Mathlib.Data.Nat.EvenOddRec
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace UlasStern

/-- The values of two successive Stern polynomials at a common argument. -/
def pair {R : Type*} [CommRing R] (t : R) : ℕ → R × R :=
  Nat.evenOddRec (P := fun _ => R × R) (0, 1)
    (fun _ v => (t * v.1, v.1 + v.2))
    (fun _ v => (v.1 + v.2, t * v.2))

def stern {R : Type*} [CommRing R] (n : ℕ) (t : R) := (pair t n).1

def index (n : ℕ) := 2 * (2 ^ (2 * n) - 1) * (2 ^ (2 * n + 1) + 1) / 3 + 1

/-- Conjecture 4.4 in Ulas, Strong arithmetic property of certain Stern polynomials. -/
def Conjecture : Prop := ∀ (n : ℕ) (t : ℝ), stern (index n) t ≠ 0

end UlasStern
