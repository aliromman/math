module
public import conjectures.SidonSetSystems.Pairs
public import conjectures.SidonSetSystems.Limits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section
namespace SidonSetSystems
open Filter
open scoped Topology

theorem resolution_of_sparse (sparse : ∀ k : ℕ, 3≤k → SparseShapes k) : Conjecture := by
  intro k hk
  by_cases small : k=2
  · subst k
    apply (tendsto_const_nhds (x:=(1:ℝ))).congr'
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    rw [pairs_exact hn]
    have pos : 0<upperBound 2 n := by simp [upperBound]; omega
    exact (div_self (Nat.cast_ne_zero.mpr pos.ne')).symm
  have hk : 3≤k := by omega
  obtain ⟨D,lo⟩ := lower_estimate hk (sparse k hk)
  let s := 1+3^D
  have sp : 0<s := by dsimp [s]; positivity
  let r := k-1
  let u := 1/((r.factorial:ℕ):ℝ)
  have up : 0<u := by dsimp [u]; positivity
  have standard : Tendsto (fun n : ℕ => (n.choose r:ℝ)/(n:ℝ)^r) atTop (𝓝 u) := by simpa [u] using choose_ratio r 0
  have remainder : Tendsto (fun n : ℕ => (D:ℝ)*((n:ℝ)+2)^(k-2)/(n:ℝ)^r) atTop (𝓝 0) := by
    have er := (lower_order (k-2) 2).const_mul (D:ℝ)
    simpa only [r,show k-2+1=k-1 by omega,Nat.cast_ofNat,mul_zero,mul_div_assoc] using er
  have lower := standard.sub remainder
  rw [sub_zero] at lower
  have upper := bound_ratio k s hk sp
  have mid : Tendsto (fun n : ℕ => (extremal k (n+s):ℝ)/(n:ℝ)^r) atTop (𝓝 u) := by
    apply lower.squeeze' upper
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      have np : 0<(n:ℝ) := by exact_mod_cast hn
      have l := lo n
      change n.choose r ≤ extremal k (n+s)+D*(n+2)^(k-2) at l
      have lr : (n.choose r:ℝ) ≤ (extremal k (n+s):ℝ)+(D:ℝ)*((n:ℝ)+2)^(k-2) := by exact_mod_cast l
      change _ / (n:ℝ)^r - _ / (n:ℝ)^r ≤ _ / (n:ℝ)^r
      rw [←sub_div]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg np.le _)
    · filter_upwards with n
      have h := extremal_upper (k:=k) (n:=n+s) (by omega) (by omega)
      apply div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
  apply (tendsto_add_atTop_iff_nat s).mp
  have quotient := mid.div upper up.ne'
  have lim : u/(1/((k-1).factorial:ℝ))=1 := div_self up.ne'
  rw [lim] at quotient
  apply quotient.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have p : 0<(n:ℝ) := by exact_mod_cast hn
  change (_/(n:ℝ)^r)/(_/(n:ℝ)^(k-1))=_
  simp [r,div_div_div_cancel_right₀, (pow_ne_zero r p.ne')]

end SidonSetSystems
