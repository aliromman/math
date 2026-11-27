module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace AscoliDihedral

/-- Independent sets in one circular chain. A one-element chain has a loop. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n+1)

private theorem lucas_shift_four (n : ℕ) :
    lucas (n+8) ≤ 7 * lucas (n+4) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih₀ ih₁ =>
    have ha : lucas (n+10) = lucas (n+8) + lucas (n+9) := rfl
    have hb : lucas (n+6) = lucas (n+4) + lucas (n+5) := rfl
    change lucas (n+9) ≤ 7 * lucas (n+5) at ih₁
    change lucas (n+10) ≤ 7 * lucas (n+6)
    omega

theorem lucas_fourth_le (n : ℕ) (hn : 3 ≤ n) : lucas n ^ 4 ≤ 7^n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hsmall : n < 8
    · interval_cases n <;> decide
    · obtain ⟨k,rfl⟩ : ∃ k, n = k + 8 := ⟨n-8,by omega⟩
      calc
        lucas (k+8) ^ 4 ≤ (7 * lucas (k+4))^4 := Nat.pow_le_pow_left (lucas_shift_four k) _
        _ = 7^4 * lucas (k+4)^4 := mul_pow _ _ _
        _ ≤ 7^4 * 7^(k+4) := Nat.mul_le_mul_left _ (ih _ (by omega) (by omega))
        _ = 7^(k+8) := by rw [←pow_add]; congr 1; omega

/-- The two factors from the circular chains decrease uniformly after order 32. -/
theorem large_ratio_bounds (n : ℕ) (hn : 32 ≤ n) :
    (7/9:ℚ)^n < (17/125:ℚ)^4 ∧
    (3*(n:ℚ)/2)^2 * (7/9:ℚ)^n < (9/10:ℚ)^2 := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hpow : 0 < (7/9:ℚ)^n := by positivity
    have hlin : (n+1:ℚ)^2 * (7/9:ℚ) ≤ n^2 := by
      have hh : (32:ℚ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n:ℚ)-32)]
    constructor
    · rw [pow_succ]
      nlinarith [ih.1]
    · push_cast
      rw [pow_succ (7/9:ℚ)]
      nlinarith only [mul_le_mul_of_nonneg_right hlin hpow.le, ih.2]

/-- The numerical separation implied by the two moment bounds. -/
theorem large_gap (n j : ℚ) (hn : 32 ≤ n) (hj' : 2*j ≤ n) :
    (j + (2*n-j)*(17/125))*(1+9/10) < n+j-1 := by linarith

end AscoliDihedral
