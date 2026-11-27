module

public import conjectures.MatrixWidth.Transitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace MatrixWidth
open Finset Filter
open scoped Topology

noncomputable def weight (β : ℝ) (x : ℕ) : ℝ := ((x+1).factorial:ℝ)^β
private def base (x : ℕ) : ℝ := x+1

theorem weight_pos (β : ℝ) (x : ℕ) : 0<weight β x :=
  Real.rpow_pos_of_pos (by exact_mod_cast (x+1).factorial_pos) _

private theorem base_pos (x : ℕ) : 0<base x := by unfold base; positivity

theorem weight_mono {β : ℝ} (hβ : 0≤β) : Monotone (weight β) := by
  intro x y hxy
  apply Real.rpow_le_rpow (by positivity) _ hβ
  exact_mod_cast Nat.factorial_le (by omega : x+1≤y+1)

private theorem denom_lower {k d : ℕ} (hd : d≤k) (x : ℕ) :
    (base x)^d / (d.factorial:ℝ) ≤ (k+x).choose d := by
  apply le_trans _ (Nat.pow_le_choose d (k+x))
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (base_pos x).le
  unfold base
  exact_mod_cast (show x+1≤k+x+1-d by omega)

private def constant (k d r : ℕ) : ℝ := ((k+1:ℕ):ℝ)^r*(2^r:ℝ)^k*(d.factorial:ℝ)^k

private theorem fiber_probability {k d : ℕ} (hd : d≤k) (x r : ℕ) :
    unionProb k d x r ≤ constant k d r * (base x)^((r:ℝ)-d*k) := by
  have hu : d≤k+x := by omega
  have hc : 0<((k+x).choose d:ℝ) := by exact_mod_cast Nat.choose_pos hu
  have hb := base_pos x
  have hdpos : 0<(d.factorial:ℝ) := by exact_mod_cast d.factorial_pos
  have b : (base x)^d ≤ (k+x).choose d * (d.factorial:ℝ) :=
    (div_le_iff₀ hdpos).mp (denom_lower hd x)
  have p := pow_le_pow_left₀ (by positivity) b k
  rw [mul_pow,←pow_mul] at p
  have bnd : (k+x:ℕ) ≤ (k+1)*(x+1) := by nlinarith
  have ub : ((k+x).choose r:ℝ) ≤ ((k+1:ℕ):ℝ)^r * (base x)^r := by
    rw [←mul_pow]
    unfold base
    exact_mod_cast (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left bnd r)
  have cnt : (Fintype.card (Fiber k d x r):ℝ)≤((k+1:ℕ):ℝ)^r*(base x)^r*(2^r:ℝ)^k := by
    calc
      _ ≤ ((k+x).choose r:ℝ)*(2^r:ℝ)^k := by exact_mod_cast fiber_bound k d x r
      _ ≤ _ := by gcongr
  unfold unionProb
  have hcard : Fintype.card (Outcome k d x) = (k+x).choose d ^ k := (card_outcome k d x).trans (by rw [Nat.min_eq_left hu])
  rw [hcard,Nat.cast_pow,Real.rpow_sub hb,Real.rpow_natCast,
    ←Nat.cast_mul,Real.rpow_natCast]
  apply (div_le_iff₀ (pow_pos hc k)).mpr
  unfold constant
  rw [mul_div_assoc',div_mul_eq_mul_div,le_div_iff₀ (pow_pos hb _)]
  calc
    _ ≤ (((k+1:ℕ):ℝ)^r*(base x)^r*(2^r:ℝ)^k) *
        (((k+x).choose d:ℝ)^k * (d.factorial:ℝ)^k) := mul_le_mul cnt p (by positivity) (by positivity)
    _ = _ := by ring

private theorem rising_ratio {β : ℝ} (hβ : 0≤β) (x j k : ℕ) (hj : j≤k) :
    weight β (x+j) / weight β x ≤
      (((k+1:ℕ):ℝ) ^ ((j:ℝ)*β)) * (base x)^((j:ℝ)*β) := by
  have fact : (x+j+1).factorial ≤ (x+1).factorial*((k+1)*(x+1))^j := by
    rw [show x+j+1=x+1+j by omega,←Nat.factorial_mul_ascFactorial]
    apply Nat.mul_le_mul_left
    exact (Nat.ascFactorial_le_pow_add _ _).trans (Nat.pow_le_pow_left (by nlinarith) _)
  have bound : ((x+j+1).factorial:ℝ) ≤ ((x+1).factorial:ℝ)*
      (((k+1:ℕ):ℝ)*(base x))^j := by unfold base; exact_mod_cast fact
  have hbp := base_pos x
  have r := Real.rpow_le_rpow (by positivity) bound hβ
  rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by positivity),
    Real.mul_rpow (by positivity) (base_pos x).le] at r
  apply (div_le_iff₀ (weight_pos β x)).mpr
  exact r.trans_eq (by unfold weight; ring)

private theorem falling_ratio {β : ℝ} (hβ : 0≤β) {x y : ℕ} (hy : y<x) :
    weight β y / weight β x ≤ (base x)^(-β) := by
  obtain ⟨z,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x≠0)
  have hm := weight_mono hβ (show y≤z by omega)
  have hb := base_pos (z+1)
  have he : weight β (z+1)= (base (z+1))^β*weight β z := by
    unfold weight base
    rw [Nat.factorial_succ,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
    push_cast
    rfl
  rw [div_le_iff₀ (weight_pos _ _),he,Real.rpow_neg hb.le,←mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos hb _).ne',one_mul]
  exact hm

private theorem base_pow_to_zero {e : ℝ} (he : e<0) :
    Tendsto (fun x : ℕ => (base x)^e) atTop (𝓝 0) := by
  have h : Tendsto base atTop atTop := by
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  simpa only [neg_neg,Function.comp_def] using (tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp h

theorem drift_ratio {k d : ℕ} (hd : 2≤d) (hk : d<k) {β : ℝ}
    (hb : 1<β) (hc : β*((k:ℝ)-d)<(d:ℝ)*((k:ℝ)-1)) :
    Tendsto (fun x => (∑ y ∈ range (x+k+1), transition k d x y * weight β y) / weight β x)
      atTop (𝓝 0) := by
  have hb0 : 0≤β := by linarith
  have hterm (r : ℕ) : Tendsto (fun x => unionProb k d x r*(weight β (k+x-r)/weight β x))
      atTop (𝓝 0) := by
    rcases lt_or_ge r d with hr|hr
    · have hz (x : ℕ) := unionProb_zero (x:=x) (by omega : 0<k) (by omega : r<min d (k+x))
      simpa only [hz,zero_mul] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    · by_cases hrk : r≤k
      · let j := k-r
        let e : ℝ := (r:ℝ)-d*k+(j:ℝ)*β
        have jcast : (j:ℝ)=(k:ℝ)-r := Nat.cast_sub hrk
        have de : 0 ≤ (β-1)*((r:ℝ)-d) := mul_nonneg (by linarith) (sub_nonneg.mpr (by exact_mod_cast hr))
        have ee : e<0 := by dsimp [e]; rw [jcast]; nlinarith
        have lim := (base_pow_to_zero ee).const_mul (constant k d r*((k+1:ℕ):ℝ)^((j:ℝ)*β))
        apply squeeze_zero (fun x => mul_nonneg (unionProb_nonneg ..) (div_nonneg (weight_pos ..).le (weight_pos ..).le)) _ (by simpa using lim)
        intro x
        have hp := base_pos x
        have hw := weight_pos β (k+x-r)
        have hxw := weight_pos β x
        have hnew := weight_pos β (x+j)
        have h := rising_ratio hb0 x j k (Nat.sub_le ..)
        rw [show k+x-r=x+j by dsimp [j]; omega]
        calc
          _ ≤ (constant k d r * (base x)^((r:ℝ)-d*k))*
            ((((k+1:ℕ):ℝ)^((j:ℝ)*β)) * (base x)^((j:ℝ)*β)) :=
              mul_le_mul (fiber_probability hk.le x r) h (by positivity) (by unfold constant; positivity)
          _ = _ := by dsimp only [e]; rw [Real.rpow_add (base_pos x)]; push_cast; ring
      · apply squeeze_zero' (Eventually.of_forall fun x => mul_nonneg (unionProb_nonneg ..) (div_nonneg (weight_pos ..).le (weight_pos ..).le)) _ (base_pow_to_zero (by linarith : -β<0))
        filter_upwards [eventually_ge_atTop (r+1)] with x hx
        have hle : unionProb k d x r ≤ 1 := by rw [←transition_union (by omega)]; apply transition_le_one
        have hf := falling_ratio hb0 (show k+x-r<x by omega)
        exact (mul_le_mul hle hf (div_nonneg (weight_pos ..).le (weight_pos ..).le) (by norm_num)).trans_eq (one_mul _)
  have lim := tendsto_finsetSum (range (k*d+1)) (fun r _ => hterm r)
  simpa only [expected_unions, Finset.sum_div, mul_div_assoc, sum_const_zero] using lim

end MatrixWidth
