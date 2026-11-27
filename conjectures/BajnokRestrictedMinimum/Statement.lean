module

public import conjectures.BajnokRestrictedInverse.Statement
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section
namespace BajnokRestrictedMinimum
open scoped Pointwise Classical

/-- The minimum size of an ordinary double sumset of an `m`-element subset of `ZMod n`. -/
noncomputable def ordinaryMinimum (n m : ℕ) : ℕ :=
  sInf {r | ∃ A : Finset (ZMod n), A.card = m ∧ (A + A).card = r}

/-- The minimum size when the two summands must be distinct. -/
noncomputable def restrictedMinimum (n m : ℕ) : ℕ :=
  sInf {r | ∃ A : Finset (ZMod n), A.card = m ∧
    (BajnokRestrictedInverse.restricted 2 A).card = r}

/-- Conjecture 9 of Bajnok, *On the minimum size of restricted sumsets in cyclic groups*. -/
def Conjecture : Prop :=
  ∀ n m : ℕ, 0 < n → 3 ≤ m → m ≤ n →
    restrictedMinimum n m =
      if (2 ∣ n ∧ 2 ∣ m) ∨ (2 * m - 2 ∣ n ∧ ¬ ∃ k : ℕ, m = 2 ^ k + 1) then
        min (ordinaryMinimum n m) (2 * m - 4)
      else min (ordinaryMinimum n m) (2 * m - 3)

end BajnokRestrictedMinimum
