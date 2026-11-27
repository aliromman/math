module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

namespace SunCircularDifferences

/-- List each element of the set once and apply the operation along the circle. -/
def HasCircle {G : Type} (A : Finset G) (op : G → G → G) : Prop :=
  ∃ f : Fin A.card → G, (∀ i, f i ∈ A) ∧ Function.Injective f ∧
    Function.Injective (fun i => op (f i) (f (finRotate A.card i)))

/-- Sun, *Some new problems in additive combinatorics*, Conjecture 3.3 (2019). -/
def Conjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G], Odd (Fintype.card G) →
    ∀ A : Finset G, 2 < A.card →
      HasCircle A (· + ·) ∧ (¬ A.card ∣ Fintype.card G → HasCircle A (· - ·))

end SunCircularDifferences
