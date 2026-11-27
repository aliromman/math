module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section
namespace BajnokRestrictedInverse

/-- Sums of exactly `h` distinct elements of `A`. -/
def restricted {G : Type*} [AddCommMonoid G] [DecidableEq G] (h : ℕ) (A : Finset G) :
    Finset G := (A.powersetCard h).image (fun S => ∑ x ∈ S, x)

/-- An arithmetic progression whose length is the size of the set. -/
def IsProgression {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) : Prop :=
  ∃ a d : G, A = (Finset.range A.card).image (fun i => a + i • d)

/-- Bajnok, *Open problems about sumsets in finite abelian groups*, Conjecture 7. -/
def Conjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h : ℕ) (A : Finset G),
    1 < Fintype.card G → 2 ≤ h → h ≤ A.card - 2 →
    h * (A.card - h) + 1 < (Fintype.card G).minFac →
    ((restricted h A).card = h * (A.card - h) + 1 ↔
      (h = 2 ∧ A.card = 4 ∧ ∃ a x y : G, A = {a, a + x, a + y, a + x + y}) ∨ IsProgression A)

end BajnokRestrictedInverse
