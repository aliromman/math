module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace CampbellCoupons
open Finset

/-- The number of draws of each coupon type in a word of length T. -/
def counts {k T : ℕ} (w : Fin T → Fin k) (i : Fin k) : ℕ :=
  (univ.filter fun j => w j = i).card

/-- The number of words that contain at least m copies of every type. -/
def winning (m k T : ℕ) : ℕ :=
  (univ.filter fun w : Fin T → Fin k => ∀ i, m ≤ counts w i).card

/-- Each word has the same probability under independent uniform draws. -/
noncomputable def success (m k T : ℕ) : ℝ := winning m k T / (k : ℝ) ^ T

/-- Campbell's conjecture in Section 6, in its stated range of trial counts. -/
def Conjecture : Prop := ∀ m k T : ℕ, 0 < m → 0 < k → k - 1 ≤ m → k * m ≤ T →
  success (m - 1) (k + 1) T ≤ success m k T

end CampbellCoupons
