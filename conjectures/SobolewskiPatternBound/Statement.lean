module

public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Size
public import Mathlib.Order.LiminfLimsup

@[expose] public section

namespace SobolewskiPatternBound

/-- Count the occurrences of an `m`-bit pattern of value `v` in a word of width `w` and value `a`.
Each starting position is counted, including positions where occurrences overlap. -/
def count (m v w a : ℕ) : ℕ :=
  ((Finset.range (w + 1 - m)).filter fun p => a / 2^p % 2^m = v).card

/-- Prefix the binary expansion with the same number of leading zeros as the pattern. -/
def occurrences (m v a : ℕ) : ℕ := count m v (a.size + (m - v.size)) a

def Prefix (m v d l : ℕ) : Prop :=
  ∀ t : Fin l, occurrences m v (t.val*d) % 2 = occurrences m v 0 % 2

/-- Maximal length of a progression of step `d` starting at zero. -/
noncomputable def lengthAtZero (m v d : ℕ) : EReal :=
  ⨆ l : ℕ, ⨆ _ : Prefix m v d l, (l : EReal)

/-- The parity condition on two words of width `m-1` in Sobolewski's definition of the constants. -/
def parity (m v j x y : ℕ) : ℕ :=
  let w := m - 1
  (count m v ((m - v.size) + w) x + count m v (w+w) (y*2^w+x) +
    count m v (w+j) (y*2^j)) % 2

/-- Lexicographic minimality of the fixed-width pair satisfying the parity condition. -/
def FirstPair (m v j x y : ℕ) : Prop :=
  let b := 2^(m-1)
  x < b ∧ y < b ∧ parity m v j x y = 1 ∧
    ∀ i : Fin b, ∀ h : Fin b, (i.val < x ∨ i.val = x ∧ h.val < y) → parity m v j i h = 0

noncomputable def slope (m j x : ℕ) : ℝ := x / (2:ℝ)^(j + m - 1)
noncomputable def intercept (m j x y : ℕ) : ℝ := y - (2:ℝ)^j * slope m j x
noncomputable def envelope (m j x y d : ℕ) : ℝ := slope m j x * d + intercept m j x y

/-- Problem 2 defines the intercept by an eventual bound at the limiting upper slope,
with equality for infinitely many steps. -/
noncomputable def SharpIntercept (m v : ℕ) (b : ℝ) : Prop :=
  let a := lengthAtZero m v
  let L := Filter.limsup (fun d : ℕ => a d / (d : EReal)) Filter.atTop
  (∀ᶠ d in Filter.atTop, a d ≤ L * d + b) ∧ Set.Infinite {d : ℕ | a d = L * d + b}

/-- Sobolewski, Conjecture 2. The width distinguishes binary patterns with leading zeros. -/
def Conjecture : Prop := ∀ m v : ℕ, 2 ≤ m → 0 < v → v < 2^m → (m, v) ≠ (2, 3) →
  let j := v.factorization 2
  ∀ x y, FirstPair m v j x y →
    SharpIntercept m v (intercept m j x y) ∧
    ∀ d, 2^(2*m+1) ≤ d →
      lengthAtZero m v d ≤ (envelope m j x y d : EReal) ∧
      (lengthAtZero m v d = (envelope m j x y d : EReal) ↔
        ∃ k : ℕ, 2*m-2 ≤ k ∧ d = 2^j*(2^k+1))

end SobolewskiPatternBound
