module

public import conjectures.PoissonApproximation.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace PoissonApproximation
open Real

private theorem polynomials {n r : ℝ} (hn : 2 ≤ n) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    let q := 1-r/n
    let y := 3*r^2/(6*n-4*r)
    let v := 1+y+y^2/2
    2*q^2+r*q ≤ q^2*(2+r)*v ∧
      4*q^2+2*r*q+(1-1/n)*r^2 ≤ q^2*(4+2*r+r^2)*v := by
  dsimp only
  rcases hr₀.eq_or_lt with e | pos
  · subst r; simp
  let a := 1/r-1
  let b := n-2
  have ha : 0≤a := sub_nonneg.mpr ((le_div_iff₀ pos).mpr (by simpa using hr₁))
  have hb : 0≤b := sub_nonneg.mpr hn
  have ar : r=1/(1+a) := by dsimp [a]; field_simp; ring
  have bn : n=2+b := by dsimp [b]; ring
  rw [ar,bn]
  have adr : 0<1+a := by positivity
  have ndr : 0<2+b := by positivity
  have posc : 0 < 6*(2+b)-4*(1/(1+a)) := by
    have t : 1/(1+a) ≤ 1 := (div_le_one adr).mpr (by linarith)
    linarith
  have y : 3*(1/(1+a))^2/(6*(2+b)-4*(1/(1+a))) =
      3/((1+a)*(8+12*a+6*b+6*a*b)) := by
    apply (div_eq_div_iff posc.ne' (by positivity)).mpr
    field_simp
    ring
  rw [y]
  constructor <;> rw [←sub_nonneg] <;> field_simp (disch := positivity) <;> ring_nf <;> positivity

/-- The possible positive CDF peaks at 1 and 2 do not exceed the zero-mass deficit. -/
theorem endpoint_bounds (n : ℕ) (hn : 2≤n) {r : ℝ} (h₀ : 0≤r) (h₁ : r≤1) :
    let q := 1-r/n
    (2*q^2+r*q)*q^(n-2) ≤ (2+r)*exp (-r) ∧
      (4*q^2+2*r*q+(1-1/n)*r^2)*q^(n-2) ≤ (4+2*r+r^2)*exp (-r) := by
  dsimp only
  have N : (2:ℝ)≤n := by exact_mod_cast hn
  have np : (0:ℝ)<n := by linarith
  let q := 1-r/n
  let y := 3*r^2/(6*n-4*r)
  let v := 1+y+y^2/2
  have qp : 0<q := sub_pos.mpr ((div_lt_one np).mpr (by linarith))
  have h := correction n hn h₀ h₁
  have P := polynomials N h₀ h₁
  have proof {L R : ℝ} (hr : 0≤R) (p : L ≤ q^2*R*v) :
      L*q^(n-2) ≤ R*exp (-r) := calc
    _ ≤ q^2*R*v*q^(n-2) := mul_le_mul_of_nonneg_right p (pow_nonneg qp.le _)
    _ = R*(q^n*v) := by
      rw [show n=(2+(n-2)) by omega] at ⊢
      rw [pow_add]
      simp only [Nat.add_sub_cancel_left]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hr
  exact ⟨proof (by positivity) P.1,proof (by positivity) P.2⟩

end PoissonApproximation
