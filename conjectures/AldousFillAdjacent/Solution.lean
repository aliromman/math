module

public import conjectures.AldousFillAdjacent.Correction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

@[expose] public section
namespace AldousFillAdjacent
open Filter
open scoped Topology Asymptotics

private theorem factorial_bound {m : ℕ} (hm : 5≤m) : 16*m≤m.factorial := by
  cases m with
  | zero => omega
  | succ k =>
    rw [Nat.factorial_succ,mul_comm 16]
    exact Nat.mul_le_mul_left _ ((by decide : 16≤Nat.factorial 4).trans (Nat.factorial_le (by omega)))

theorem gap {m : ℕ} (hm : 5≤m) {τ : ℝ} (ht : Tendsto (mean m) atTop (𝓝 τ)) :
    1/(4*(m:ℝ)) ≤ τ/m.factorial-(1+1/(m:ℝ)) := by
  have mp : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have mf : (0:ℝ)<m.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have fac : (16:ℝ)*m≤m.factorial := by exact_mod_cast factorial_bound hm
  have small : (4:ℝ)/m.factorial ≤ 1/(4*m) := by
    apply (div_le_div_iff₀ mf (by positivity)).mpr
    linarith
  have add : 1/(2*(m:ℝ))+1/(m:ℝ) ≤ 2/(m+1) := by
    field_simp
    nlinarith [show (5:ℝ)≤m by exact_mod_cast hm]
  have h := finite_lower ht
  rw [show (1:ℝ)/(2*(m:ℝ))=1/(4*m)+1/(4*m) by ring] at add
  linarith

theorem resolution : ¬Prediction := by
  rintro ⟨τ,conv,big⟩
  obtain ⟨C,hu⟩ := big.bound
  obtain ⟨k,hk⟩ := exists_nat_gt (4*C)
  obtain ⟨m,hm,hm5,hl,hc⟩ := ((eventually_ge_atTop k).and
    ((eventually_ge_atTop 5).and (conv.and hu))).exists
  have mp : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hC : 4*C<(m:ℝ) := hk.trans_le (by exact_mod_cast hm)
  have hg := gap hm5 hl
  have hpos : 0≤τ m/m.factorial-(1+1/(m:ℝ)) := (by positivity : 0≤1/(4*(m:ℝ))).trans hg
  simp only [Real.norm_eq_abs,abs_of_nonneg hpos,abs_of_nonneg (by positivity : 0≤(1:ℝ)/m^2)] at hc
  have bound := hg.trans hc
  field_simp at bound
  nlinarith

/-- info: 'AldousFillAdjacent.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end AldousFillAdjacent
