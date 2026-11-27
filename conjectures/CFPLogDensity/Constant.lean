module

public import conjectures.CFPLogDensity.Statement
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace CFPLogDensity
open Finset

private theorem root_order {r : ℕ} (hr : 0 < r) {a b : ℝ}
    (ha : Root r a) (hb : Root r b) : ¬ a < b := by
  rintro hab
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have ratio (x : ℝ) (hx : Root r x) :
      (∑ j ∈ range r, x^j) = 2*r + (r:ℝ)/(x-1) := by
    have := geom_sum_mul x r
    have hp := hx.1
    field_simp
    nlinarith [hx.2]
  have order : (∑ j ∈ range r, a^j) ≤ ∑ j ∈ range r, b^j :=
    sum_le_sum fun j _ => pow_le_pow_left₀ (by linarith [ha.1]) hab.le j
  rw [ratio a ha,ratio b hb] at order
  have := div_lt_div_of_pos_left hr' (sub_pos.mpr ha.1) (sub_lt_sub_right hab 1)
  linarith

theorem unique_root (r : ℕ) (hr : 3 ≤ r) : ∃! b : ℝ, Root r b := by
  have hr' : (3:ℝ) ≤ r := by exact_mod_cast hr
  let f (x : ℝ) := x^r + r - 1 - 2*r*x
  let R := 2*(r:ℝ)+1
  have hR : 1 ≤ R := by dsimp [R]; linarith
  have hpow : R^2 ≤ R^r := pow_le_pow_right₀ hR (by omega)
  have cont : Continuous f := by dsimp [f]; fun_prop
  have low : f 1 < 0 := by simp [f]; linarith
  have high : 0 ≤ f R := by dsimp [f,R] at *; nlinarith
  obtain ⟨b,hb,he⟩ := intermediate_value_Icc hR cont.continuousOn (show 0 ∈ Set.Icc (f 1) (f R) from ⟨low.le,high⟩)
  have root : Root r b := by
    refine ⟨lt_of_le_of_ne hb.1 ?_,?_⟩
    · rintro rfl
      linarith
    · dsimp [f] at he
      linarith
  exact ⟨b,root,fun y hy => le_antisymm (le_of_not_gt (root_order (by omega) root hy))
    (le_of_not_gt (root_order (by omega) hy root))⟩

theorem printed_value {r : ℕ} (hr : 3 ≤ r) {b : ℝ} (hb : Root r b) :
    value r b = (1-1/(2*b))*(1+1/(2*(r:ℝ)*b-r)) := by
  have bp := hb.1
  have gt : 1 < b^r := one_lt_pow₀ bp (by omega)
  have den : b^r-1 = 2*(r:ℝ)*b-r := by linarith [hb.2]
  rw [←den]
  unfold value
  field_simp
  ring

/-- At the positive root the optimum and its complement have simple products with 2rb. -/
theorem value_products {r : ℕ} (hr : 3 ≤ r) {b : ℝ} (hb : Root r b) :
    (2*(r:ℝ)*b) * value r b = b^r ∧
    (2*(r:ℝ)*b) * (1-value r b) = r-1 := by
  have hp := hb.1
  have hbp : 1 < b^r := one_lt_pow₀ hp (by omega)
  have hmul : (2*(r:ℝ)*b) * value r b = b^r := by
    unfold value
    field_simp
    nlinarith [hb.2]
  exact ⟨hmul,by linarith [hb.2,hmul]⟩

theorem value_bounds {r : ℕ} (hr : 3 ≤ r) {b : ℝ} (hb : Root r b) :
    0 < value r b ∧ value r b < 1 := by
  have hr' : (3:ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨h₁,h₂⟩ := value_products hr hb
  have hpos : 0 < 2*(r:ℝ)*b := by have := hb.1; positivity
  have hbp : 0 < b^r := pow_pos (by linarith [hb.1]) _
  constructor
  · exact pos_of_mul_pos_right (h₁.trans_gt hbp) hpos.le
  · have : 0 < 1-value r b := pos_of_mul_pos_right (h₂.trans_gt (by linarith)) hpos.le
    linarith

/-- Bernoulli's inequality gives the tangent lower bound at z = 1/b. -/
theorem tangent_bound {r : ℕ} (hr : 3 ≤ r) {b : ℝ} (hb : Root r b) (z : ℝ) (hz : 0 ≤ z) :
    z/2 ≤ 1-value r b + value r b*z^r := by
  obtain ⟨h₁,h₂⟩ := value_products hr hb
  have bp : 0 < b := by linarith [hb.1]
  have rp : 0 < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have h := one_add_mul_sub_le_pow (show -1 ≤ b*z by nlinarith [mul_nonneg bp.le hz]) r
  rw [mul_pow] at h
  apply le_of_mul_le_mul_left (a := 2*(r:ℝ)*b) _ (by positivity)
  calc
    2*(r:ℝ)*b*(z/2) ≤ (r-1)+b^r*z^r := by nlinarith
    _ = 2*(r:ℝ)*b*(1-value r b) + (2*(r:ℝ)*b*value r b)*z^r := by rw [h₁,h₂]
    _ = _ := by ring

/-- A strict deficit in density gives a uniform margin for every consecutive time ratio. -/
theorem schedule_constants {r : ℕ} (hr : 3 ≤ r) {b C : ℝ} (hb : Root r b)
    (hC : 0 ≤ C) (ltC : C < value r b) :
    ∃ K : ℕ, 5 ≤ K ∧ ∃ g : ℝ, 1 < g ∧ ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      (((K+1:ℕ):ℝ)/(2*K-1:ℕ))*z < 1-C+C*z^r/g := by
  let F (z : ℝ) := 1-C+C*z^r-z/2
  have positive (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) 1) : 0 < F z := by
    rcases lt_or_eq_of_le hz.2 with h|rfl
    · have hpow : z^r < 1 := pow_lt_one₀ hz.1 h (by omega)
      have := tangent_bound hr hb z hz.1
      dsimp [F]
      nlinarith [mul_pos (sub_pos.mpr ltC) (sub_pos.mpr hpow)]
    · norm_num [F]
  have cont : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨w,hw,hle⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) cont.continuousOn
  let d := F w / 4
  have hd : 0 < d := by dsimp [d]; linarith [positive w hw]
  obtain ⟨K,hK⟩ := exists_nat_gt (5 + 3/d)
  have hKn : 5 ≤ K := by
    have : (5:ℝ) < K := by linarith [div_pos (by norm_num : (0:ℝ)<3) hd]
    exact_mod_cast this.le
  have hKr : (5:ℝ) ≤ K := by exact_mod_cast hKn
  have hq : 0 < 2*(K:ℝ)-1 := by linarith
  have hcast : ((2*K-1:ℕ):ℝ) = 2*(K:ℝ)-1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ 2*K)]; rfl
  have hpq : ((K+1:ℕ):ℝ)/(2*K-1:ℕ) ≤ 1/2+d := by
    rw [hcast,Nat.cast_add,Nat.cast_one,div_le_iff₀ hq]
    have hk : 3/d < (K:ℝ)-5 := by linarith
    have := (div_lt_iff₀ hd).mp hk
    nlinarith
  refine ⟨K,hKn,1+d,by linarith,?_⟩
  intro z hz hz'
  have hmin : 4*d ≤ F z := by
    calc
      4*d = F w := by dsimp only [d]; ring
      _ ≤ F z := hle (show z ∈ Set.Icc (0:ℝ) 1 from ⟨hz,hz'⟩)
  have hC' : C ≤ 1 := ltC.le.trans (value_bounds hr hb).2.le
  have hpow : z^r ≤ 1 := pow_le_one₀ hz hz'
  have hcap : C*z^r ≤ 1 := (mul_le_mul_of_nonneg_left hpow hC).trans (by simpa using hC')
  have drop : C*z^r - d ≤ C*z^r/(1+d) := by
    apply (le_div_iff₀ (by linarith : 0<1+d)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcap hd.le,sq_nonneg d]
  dsimp [F] at hmin
  have := mul_le_mul_of_nonneg_right hpq hz
  nlinarith [mul_le_mul_of_nonneg_left hz' hd.le]
end CFPLogDensity
