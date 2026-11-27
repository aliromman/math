module

public import conjectures.MatrixWidth.TailBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace MatrixWidth
open Finset Filter Real
open scoped Topology

private theorem factorial_log (n : ℕ) (hn : 0<n) :
    (n:ℝ)*log n-n ≤ log (n.factorial:ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n=0
    · simp [h]
    · have npos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero h
      have n1 : 0<(n:ℝ)+1 := by positivity
      have one : (n:ℝ)*(((n:ℝ)+1)/n-1)=1 := by field_simp; ring
      have est := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos n1 npos)) npos.le
      rw [one,Real.log_div n1.ne' npos.ne'] at est
      rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_succ]
      linarith only [ih (Nat.pos_of_ne_zero h),est]

private theorem lower_log {k d : ℕ} (hd : 2≤d) (hk : d<k) {β : ℝ}
    (hb : 1<β) (hc : β*((k:ℝ)-d)<(d:ℝ)*((k:ℝ)-1))
    {ρ : ℕ→ℝ} (hρ : Stationary (transition k d) ρ) :
    ∃ C : ℝ, ∀ m : ℕ, 2≤m →
      β-β/(log m)-C/((m:ℝ)*log m) ≤ -log (tail ρ m)/((m:ℝ)*log m) := by
  obtain ⟨C,hC,hM⟩ := tail_upper hd hk hb hc hρ
  refine ⟨log C,fun m hm => ?_⟩
  have tp := (stationary_positive hd hk hρ m).trans_le (tail_term hρ (le_refl m))
  have mp : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have ml : 0<log (m:ℝ) := log_pos (by exact_mod_cast (by omega : 1<m))
  have ff : log ((m+1).factorial:ℝ) ≥ (m:ℝ)*log m-m := by
    apply (factorial_log m (by omega)).trans
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_succ m))
  have eq := Real.log_le_log (mul_pos tp (weight_pos β m)) (hM m)
  rw [Real.log_mul tp.ne' (weight_pos β m).ne',weight,Real.log_rpow (by positivity)] at eq
  have g := mul_le_mul_of_nonneg_left ff (by linarith : 0≤β)
  apply (le_div_iff₀ (mul_pos mp ml)).mpr
  calc
    _ = β*((m:ℝ)*log m-m)-log C := by field_simp
    _ ≤ _ := by linarith

private theorem upper_log {k d : ℕ} (hd : 2≤d) (hk : d<k)
    {ρ : ℕ→ℝ} (hρ : Stationary (transition k d) ρ) :
    ∀ m : ℕ, 2≤m →
      -log (tail ρ m)/((m:ℝ)*log m) ≤
        (((d*(k-1):ℕ):ℝ)/(k-d:ℕ)+((d*(k-1):ℕ):ℝ)/m)*
        (1+log ((k+(k-d)+1:ℕ):ℝ)/log m)-log (ρ 0)/((m:ℝ)*log m) := by
  intro m hm
  let a := d*(k-1)
  let h := k-d
  have hp : 0<h := by dsimp [h]; omega
  have hpr : (0:ℝ)<h := by exact_mod_cast hp
  have mp : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have ml : 0<log (m:ℝ) := log_pos (by exact_mod_cast (by omega : 1<m))
  have tp := (stationary_positive hd hk hρ m).trans_le (tail_term hρ (le_refl m))
  have divle : ((m/h:ℕ):ℝ)≤(m:ℝ)/h := by
    rw [le_div_iff₀ hpr]
    exact_mod_cast Nat.div_mul_le_self m h
  have large : k+h+m≤(k+h+1)*m := by nlinarith
  have kc : (0:ℝ)<((k+h+1:ℕ):ℝ) := by positivity
  have U : (0:ℝ)<((k+h+m:ℕ):ℝ) := by positivity
  have logU := Real.log_le_log U (show ((k+h+m:ℕ):ℝ)≤((k+h+1:ℕ):ℝ)*(m:ℝ) by exact_mod_cast large)
  rw [Real.log_mul kc.ne' mp.ne'] at logU
  have lp : 0≤log ((k+h+m:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤k+h+m))
  have ex : (a:ℝ)*((m/h:ℕ)+1) ≤ (a:ℝ)*((m:ℝ)/h+1) :=
    mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
  have up := Real.log_le_log (stationary_positive hd hk hρ 0) (tail_lower hd hk hρ m)
  change log (ρ 0) ≤ log (tail ρ m*((k+h+m:ℕ):ℝ)^(a*(m/h+1))) at up
  rw [Real.log_mul tp.ne' (pow_pos U _).ne',Real.log_pow] at up
  push_cast at up
  have cmp := mul_le_mul ex logU lp (show 0≤(a:ℝ)*((m:ℝ)/h+1) by positivity)
  change _ ≤ (((a:ℝ)/h+(a:ℝ)/m)*(1+log ((k+h+1:ℕ):ℝ)/log m)-log (ρ 0)/((m:ℝ)*log m))
  calc
    _ ≤ (((a:ℝ)*((m:ℝ)/h+1))*(log ((k+h+1:ℕ):ℝ)+log m)-log (ρ 0))/((m:ℝ)*log m) := by
      apply div_le_div_of_nonneg_right _ (mul_pos mp ml).le
      push_cast at cmp ⊢
      linarith only [up,cmp]
    _ = _ := by field_simp; ring

/-- The exact stationary tail exponent, for every stationary distribution of the fixed-batch urn. -/
theorem tail_rate {k d : ℕ} (hd : 2≤d) (hk : d<k)
    {ρ : ℕ→ℝ} (hρ : Stationary (transition k d) ρ) :
    Tendsto (fun m : ℕ => -log (tail ρ m)/((m:ℝ)*log m)) atTop
      (𝓝 (((d:ℝ)*((k:ℝ)-1))/((k:ℝ)-d))) := by
  let a : ℝ := d*((k:ℝ)-1)
  let h : ℝ := (k:ℝ)-d
  have hpos : 0<h := sub_pos.mpr (by exact_mod_cast hk)
  have kd : (d:ℝ)≥2 := by exact_mod_cast hd
  have kpos : (0:ℝ)≤k := by positivity
  have hγ : 1<a/h := by
    rw [lt_div_iff₀ hpos]
    dsimp [a,h]
    nlinarith only [kd,kpos,hpos, mul_nonneg (sub_nonneg.mpr kd) kpos, (by exact_mod_cast (show 0<k by omega) : (0:ℝ)<k)]
  have van (c : ℝ) : Tendsto (fun n : ℕ => c/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul c
  have vanL (c : ℝ) : Tendsto (fun n : ℕ => c/log (n:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply,Function.comp_apply] using
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).inv_tendsto_atTop.const_mul c
  have vanML (c : ℝ) : Tendsto (fun n : ℕ => c/((n:ℝ)*log n)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,mul_assoc, mul_comm, mul_left_comm] using (van c).mul (vanL 1)
  apply tendsto_order.mpr
  constructor
  · intro z hz
    obtain ⟨β,hββ,hβ⟩ := exists_between (max_lt (show z<a/h from hz) hγ)
    have hb := (le_max_right _ _).trans_lt hββ
    have hc := (lt_div_iff₀ hpos).mp hβ
    obtain ⟨C,lower⟩ := lower_log hd hk hb hc hρ
    have lim : Tendsto (fun m : ℕ => β-β/log (m:ℝ)-C/((m:ℝ)*log m)) atTop (𝓝 β) := by
      simpa only [sub_zero] using ((vanL β).const_sub β).sub (vanML C)
    filter_upwards [eventually_ge_atTop 2,lim.eventually_const_lt ((le_max_left _ _).trans_lt hββ)] with m hm hm'
    exact hm'.trans_le (lower m hm)
  · intro z hz
    let c := log ((k+(k-d)+1:ℕ):ℝ)
    have lim : Tendsto (fun m : ℕ => (a/h+a/m)*(1+c/log m)-log (ρ 0)/((m:ℝ)*log m)) atTop (𝓝 (a/h)) := by
      simpa using (((van a).const_add (a/h)).mul ((vanL c).const_add 1)).sub (vanML (log (ρ 0)))
    have aa : ((d*(k-1):ℕ):ℝ)=a := by dsimp [a]; rw [Nat.cast_mul,Nat.cast_sub (by omega : 1≤k),Nat.cast_one]
    have hh : ((k-d:ℕ):ℝ)=h := Nat.cast_sub hk.le
    filter_upwards [eventually_ge_atTop 2,lim.eventually_lt_const (show a/h<z from hz)] with m hm bound
    have le := upper_log hd hk hρ m hm
    rw [aa,hh] at le
    exact le.trans_lt bound

/-- The probability that a stationary physical width is at least u. -/
noncomputable def widthTail (k : ℕ) (ρ : ℕ→ℝ) (u : ℕ) : ℝ :=
  ∑' x, if u≤k+x then ρ x else 0

theorem width_tail_rate {k d : ℕ} (hd : 2≤d) (hk : d<k)
    {ρ : ℕ→ℝ} (hρ : Stationary (transition k d) ρ) :
    Tendsto (fun u : ℕ => -log (widthTail k ρ u)/((u:ℝ)*log u)) atTop
      (𝓝 (((d:ℝ)*((k:ℝ)-1))/((k:ℝ)-d))) := by
  have equal (n : ℕ) : widthTail k ρ (n+k)=tail ρ n := by
    simp only [widthTail,tail,show ∀ x : ℕ,n+k≤k+x ↔ n≤x by omega]
  have logs : Tendsto (fun n : ℕ => log ((n:ℝ)+k)/log (n:ℝ)) atTop (𝓝 1) := by
    let c := log ((k:ℝ)+1)
    have z : Tendsto (fun n : ℕ => c/log (n:ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply,Function.comp_apply] using
        (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).inv_tendsto_atTop.const_mul c
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa only [add_zero] using z.const_add 1)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have np : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
      exact (one_le_div₀ (log_pos np)).mpr (Real.log_le_log (by linarith) (le_add_of_nonneg_right (Nat.cast_nonneg _)))
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have np : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
      have le : (n:ℝ)+k≤((k:ℝ)+1)*n := by nlinarith [mul_nonneg (sub_nonneg.mpr np.le) (Nat.cast_nonneg (α:=ℝ) k)]
      have bnd := Real.log_le_log (by positivity : 0<(n:ℝ)+k) le
      rw [Real.log_mul (by positivity) (by linarith)] at bnd
      change _ ≤ 1+c/log (n:ℝ)
      apply (div_le_iff₀ (log_pos np)).mpr
      calc
        _ ≤ c+log n := bnd
        _ = (1+c/log n)*log n := by field_simp [(log_pos np).ne']; ring
  have h := ((tail_rate hd hk hρ).mul (tendsto_natCast_div_add_atTop (k:ℝ))).div logs one_ne_zero
  apply (tendsto_add_atTop_iff_nat k).mp
  simp only [mul_one,div_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have np : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
  have kp : (1:ℝ)<(n:ℝ)+k := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  rw [equal,Nat.cast_add]
  simp only [Pi.div_apply]
  field_simp [(log_pos np).ne',(log_pos kp).ne',(by linarith : (n:ℝ)≠0)]

end MatrixWidth
