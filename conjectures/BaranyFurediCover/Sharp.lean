module

public import conjectures.BaranyFurediCover.Lines
public import conjectures.BaranyFurediCover.Metrics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace BaranyFurediCover

/-- A horizontal line realizes the largest possible lattice diameter. -/
theorem square_diameter {a b : ℕ} (ha : 0<a) (hba : b≤a) :
    diameter (square a b) = a + b^2/a := by
  rw [diameter_eq_string (square_convex _ _) (lengths_bounded ha)]
  let m := b^2/a
  have low : m*a ≤ b^2 := Nat.div_mul_le_self _ _
  have hi : b^2 < (m+1)*a := by
    have rem := Nat.mod_lt (b^2) ha
    have eq := Nat.mod_add_div (b^2) a
    dsimp [m]
    nlinarith
  apply le_antisymm
  · apply csSup_le'
    intro k hk
    have le := length_bound ha hk
    unfold D at le
    have eq : k*a≤a^2+b^2 := by exact_mod_cast le
    change k≤a+m
    by_contra! big
    have v := Nat.mul_le_mul_right a (show a+(m+1)≤k by omega)
    nlinarith
  · apply le_csSup (lengths_bounded ha)
    refine ⟨![-(m:ℤ),(b:ℤ)],![1,0],?_,?_,?_⟩
    · intro e
      have := congrFun e 0
      norm_num at this
    · apply (mem_square_iff ha _).mpr
      have v : (m:ℝ)*a ≤ (b:ℝ)^2 := by exact_mod_cast low
      have ma : m≤b := by
        by_contra! ne
        have le := Nat.mul_le_mul_right a (show b+1≤m by omega)
        nlinarith [Nat.mul_le_mul_left b hba]
      have ab : (b:ℝ)≤a := by exact_mod_cast hba
      have mb : (m:ℝ)≤b := by exact_mod_cast ma
      have am := mul_nonneg (show (0:ℝ)≤a by positivity) (show (0:ℝ)≤m by positivity)
      have bm := mul_nonneg (show (0:ℝ)≤b by positivity) (show (0:ℝ)≤m by positivity)
      have ba := mul_nonneg (show (0:ℝ)≤b by positivity) (show (0:ℝ)≤a by positivity)
      have bm' := mul_le_mul_of_nonneg_right mb (show (0:ℝ)≤b by positivity)
      have ab' := mul_le_mul_of_nonneg_left ab (show (0:ℝ)≤a by positivity)
      simp [first,second,pt,D,Set.mem_Icc]
      refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> nlinarith [sq_nonneg (a:ℝ),sq_nonneg (b:ℝ)]
    · have e : ![-(m:ℤ),(b:ℤ)] + (a+b^2/a) • (![1,0] : Lattice) = ![(a:ℤ),(b:ℤ)] := by
        ext i
        fin_cases i <;> simp [m]
      rw [e]
      apply (mem_square_iff ha _).mpr
      simp [first,second,pt,D,Set.mem_Icc,pow_two,mul_comm]
      positivity

/-- Three halves is sharp for lattice squares. -/
theorem sharp_squares {a b : ℕ} (ha : 0<a) (hb : b≤a) :
    2*(a+b) ≤ 3*diameter (square a b) := by
  rw [square_diameter ha hb]
  let m := b^2/a
  have hi : b^2 < (m+1)*a := by
    have rem := Nat.mod_lt (b^2) ha
    have eq := Nat.mod_add_div (b^2) a
    dsimp [m]
    nlinarith
  change 2*(a+b)≤3*(a+m)
  by_cases small : a≤3
  · dsimp [m]
    interval_cases a <;> interval_cases b <;> decide
  by_contra! bad
  have big : 4≤a := by omega
  have contradiction₁ := Nat.mul_le_mul_right a (show 3*(a+m)+1≤2*(a+b) by omega)
  have s : 0≤((a:ℤ)-b)^2 := sq_nonneg _
  have v : 0≤((a:ℤ)-3*b)^2 := sq_nonneg _
  have g : 0≤((a:ℤ)-4)*a := by
    apply mul_nonneg <;> omega
  zify at hi contradiction₁ big
  nlinarith

end BaranyFurediCover
