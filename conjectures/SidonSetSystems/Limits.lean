module
public import conjectures.SidonSetSystems.Statement
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace SidonSetSystems
open Filter Asymptotics
open scoped Topology

private theorem shift_ratio (s : ℕ) : Tendsto (fun n : ℕ => ((n:ℝ)+s)/n) atTop (𝓝 1) := by
  simpa only [inv_div,inv_one] using (tendsto_natCast_div_add_atTop (s:ℝ)).inv₀ one_ne_zero

theorem choose_ratio (r s : ℕ) : Tendsto (fun n : ℕ => ((n+s).choose r : ℝ)/(n:ℝ)^r) atTop
    (𝓝 (1/(r.factorial:ℝ))) := by
  have fp : 0<(r.factorial:ℝ) := by exact_mod_cast r.factorial_pos
  have nz : ∀ᶠ n : ℕ in atTop, (n:ℝ)^r/(r.factorial:ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have p : 0<(n:ℝ) := by exact_mod_cast hn
    positivity
  have h := ((isEquivalent_iff_tendsto_one nz).mp (isEquivalent_choose r)).div_const (r.factorial:ℝ)
  have nat : Tendsto (fun n : ℕ => (n.choose r:ℝ)/(n:ℝ)^r) atTop (𝓝 (1/(r.factorial:ℝ))) := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    change ((n.choose r:ℝ)/((n:ℝ)^r/r.factorial))/r.factorial = _
    have p : 0<(n:ℝ) := by exact_mod_cast hn
    field_simp
  have first := nat.comp (tendsto_add_atTop_nat s)
  have second := (shift_ratio s).pow r
  have hlim := first.mul second
  simp only [one_pow,mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  change ((n+s).choose r:ℝ)/((n+s:ℕ):ℝ)^r * (((n:ℝ)+s)/n)^r = _
  have p : 0<(n:ℝ) := by exact_mod_cast hn
  have pp : 0<(n:ℝ)+s := by positivity
  push_cast
  rw [div_pow]
  field_simp

theorem lower_order (d s : ℕ) : Tendsto (fun n : ℕ => ((n:ℝ)+s)^d/(n:ℝ)^(d+1)) atTop (𝓝 0) := by
  have h := ((shift_ratio s).pow d).mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ))
  simp only [one_pow,mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have p : 0<(n:ℝ) := by exact_mod_cast hn
  change (((n:ℝ)+s)/n)^d*(1/n)=_
  rw [div_pow,pow_succ]
  field_simp


theorem bound_ratio (k s : ℕ) (hk : 3≤k) (hs : 0<s) :
    Tendsto (fun n : ℕ => (upperBound k (n+s):ℝ)/(n:ℝ)^(k-1)) atTop (𝓝 (1/((k-1).factorial:ℝ))) := by
  have rem : Tendsto (fun n : ℕ => ((n+s-k:ℕ):ℝ)/(n:ℝ)^(k-1)) atTop (𝓝 0) := by
    apply (tendsto_const_nhds (x:=(0:ℝ))).squeeze' (by simpa only [pow_one] using lower_order 1 s)
    · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      have p : 0<(n:ℝ) := by exact_mod_cast hn
      have one : 1≤(n:ℝ) := by exact_mod_cast hn
      have num : ((n+s-k:ℕ):ℝ) ≤ (n:ℝ)+s := by exact_mod_cast (Nat.sub_le (n+s) k)
      exact (div_le_div_of_nonneg_right num (pow_nonneg p.le _)).trans
        (div_le_div_of_nonneg_left (by positivity) (pow_pos p _) (pow_le_pow_right₀ one (by omega)))
  have h := (choose_ratio (k-1) (s-1)).add rem
  rw [add_zero] at h
  apply h.congr'
  filter_upwards with n
  have e : n+s-1=n+(s-1) := by omega
  simp only [upperBound,Nat.cast_add,e,add_div]

end SidonSetSystems
