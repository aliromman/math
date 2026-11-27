module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace PoissonApproximation
open Set Real

private theorem log_bound {z : ℝ} (hz : 0 ≤ z) (hlt : z < 1) :
    3*z^2/(6-4*z) ≤ -log (1-z)-z := by
  let f (x : ℝ) := -log (1-x)-x-3*x^2/(6-4*x)
  have D (x : ℝ) (hx : x ∈ Iio (1:ℝ)) :
      HasDerivAt f (4*x^3/((1-x)*(6-4*x)^2)) x := by
    have h₁ : 0 < 1-x := by exact sub_pos.mpr hx
    have h₂ : 0 < 6-4*x := by linarith
    have t := (((((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).log h₁.ne').neg.sub
      (hasDerivAt_id x)).sub (((hasDerivAt_const x (3:ℝ)).mul ((hasDerivAt_id x).pow 2)).div
      ((hasDerivAt_const x (6:ℝ)).sub ((hasDerivAt_const x (4:ℝ)).mul (hasDerivAt_id x))) h₂.ne'))
    convert t using 1
    · dsimp [f]; rfl
    · dsimp; field_simp; ring
  have M : MonotoneOn f (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x ↦ 4*x^3/((1-x)*(6-4*x)^2))
      (convex_Ico ..)
    · exact fun x hx ↦ (D x hx.2).continuousAt.continuousWithinAt
    · exact fun x hx ↦ (D x (interior_subset hx).2).hasDerivWithinAt
    · intro x hx
      have pos := (interior_subset hx).1
      have h : 0 < 1-x := sub_pos.mpr (interior_subset hx).2
      positivity
  have H := M (show (0:ℝ) ∈ Ico 0 1 by simp) ⟨hz,hlt⟩ hz
  simpa [f] using H

/-- A common lower bound for the exponential correction to the zero mass. -/
theorem correction (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    let y := 3*r^2/(6*n-4*r)
    (1-r/n)^n * (1+y+y^2/2) ≤ exp (-r) := by
  dsimp only
  have N : (2:ℝ) ≤ n := by exact_mod_cast hn
  have npos : (0:ℝ)<n := by linarith
  have dpos : 0<6*(n:ℝ)-4*r := by linarith
  have z0 : 0≤r/n := div_nonneg h₀ npos.le
  have z1 : r/n<1 := (div_lt_one npos).mpr (by linarith)
  have qpos : 0<1-r/n := sub_pos.mpr z1
  have c : 0<6-4*(r/n) := by linarith
  have L := mul_le_mul_of_nonneg_left (log_bound z0 z1) npos.le
  have id : (n:ℝ)*(3*(r/n)^2/(6-4*(r/n)))=3*r^2/(6*n-4*r) := by
    field_simp
  rw [id] at L
  have ny : 0≤3*r^2/(6*n-4*r) := by positivity
  have h := Real.quadratic_le_exp_of_nonneg ny
  apply (mul_le_mul_of_nonneg_left h (pow_nonneg qpos.le n)).trans
  rw [← Real.exp_log qpos,←Real.exp_nat_mul,←Real.exp_add,Real.exp_le_exp]
  have e : (n:ℝ)*(r/n)=r := by field_simp
  linarith

end PoissonApproximation
