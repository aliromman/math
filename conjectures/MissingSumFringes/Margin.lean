module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Topology

/-- The number and the probability weight of pairs of initial gaps with sum a. -/
noncomputable def marginWeight (a : ℕ) : ℝ := ((a:ℝ)+1)/(2:ℝ)^a

noncomputable def marginMass (D : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ a∈range (k/2+1),marginWeight a*D (k-2*a)

noncomputable def marginMoment (D H : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ a∈range (k/2+1),marginWeight a*((a:ℝ)*D (k-2*a)+H (k-2*a))

noncomputable def tilt (j : ℕ) : ℝ := (2:ℝ)^((j:ℝ)/2)

private noncomputable def common (k : ℕ) : ℝ := (((k/2:ℕ):ℝ)+1)*(2:ℝ)^(-(k:ℝ)/2)

private theorem common_pos (k : ℕ) : 0<common k := by unfold common; positivity
theorem marginWeight_pos (a : ℕ) : 0<marginWeight a := by unfold marginWeight; positivity
theorem tilt_pos (j : ℕ) : 0<tilt j := Real.rpow_pos_of_pos (by norm_num) _

private theorem weight_le {a k : ℕ} (ha : a≤k/2) :
    marginWeight a≤common k*tilt (k-2*a) := by
  have doubled : 2*a≤k := by omega
  have iden : (2:ℝ)^(-(k:ℝ)/2)*tilt (k-2*a) = (2^a:ℝ)⁻¹ := by
    rw [tilt,←Real.rpow_add (by norm_num),Nat.cast_sub doubled,Nat.cast_mul,Nat.cast_ofNat]
    rw [show -(k:ℝ)/2+((k:ℝ)-2*a)/2=-(a:ℝ) by ring,
      Real.rpow_neg (by norm_num),Real.rpow_natCast]
  unfold common marginWeight
  rw [mul_assoc,iden,div_eq_mul_inv]
  gcongr

private theorem mass_lower (D : ℕ → ℝ) (nd : ∀ j,0≤D j) (k : ℕ) :
    common k*min (D 0) (D 1)≤marginMass D k := by
  let n := k/2
  have term := single_le_sum (s:=range (k/2+1)) (f:=fun a => marginWeight a*D (k-2*a))
    (fun a _ => mul_nonneg (marginWeight_pos a).le (nd _)) (show n∈_ from mem_range.mpr (Nat.lt_succ_self _))
  apply le_trans _ term
  have frac : (n:ℝ)≤(k:ℝ)/2 := by
    have : 2*n≤k := by dsimp [n]; omega
    exact (le_div_iff₀ (by norm_num)).mpr (by exact_mod_cast (by omega : n*2≤k))
  have power : (2:ℝ)^(-(k:ℝ)/2)≤(2^n:ℝ)⁻¹ := by
    rw [←Real.rpow_natCast (2:ℝ) n,←Real.rpow_neg (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have bound : common k≤marginWeight n := by
    unfold common marginWeight
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left power (by positivity)
  have par : k-2*n=0 ∨ k-2*n=1 := by dsimp [n]; omega
  have low : min (D 0) (D 1)≤D (k-2*n) := par.elim (fun e => e ▸ min_le_left ..) (fun e => e ▸ min_le_right ..)
  exact mul_le_mul bound low (le_min (nd _) (nd _)) (marginWeight_pos _).le

theorem marginMass_pos (D : ℕ → ℝ) (nd : ∀ j,0≤D j) (p0 : 0<D 0) (p1 : 0<D 1)
    (k : ℕ) : 0<marginMass D k :=
  (mul_pos (common_pos _) (lt_min p0 p1)).trans_le (mass_lower D nd k)

private theorem margin_error {D H : ℕ → ℝ} (nd : ∀ j,0≤D j) (nh : ∀ j,0≤H j)
    (sD : Summable fun j : ℕ => tilt j*((j:ℝ)+1)*D j)
    (sH : Summable fun j : ℕ => tilt j*H j) (k : ℕ) :
    |marginMoment D H k-(k:ℝ)/2*marginMass D k|≤
      common k*(∑' j : ℕ,tilt j*(((j:ℝ)+1)*D j+H j)) := by
  let I := range (k/2+1)
  let j := fun a : ℕ => k-2*a
  let g := fun u : ℕ => tilt u*(((u:ℝ)+1)*D u+H u)
  have ng (u : ℕ) : 0≤g u := mul_nonneg (tilt_pos _).le (add_nonneg (mul_nonneg (by positivity) (nd _)) (nh _))
  have sg : Summable g := (sD.add sH).congr fun u => by dsimp [g]; ring
  have inject : Set.InjOn j I := by
    intro a ha b hb e
    have aa := mem_range.mp ha
    have bb := mem_range.mp hb
    dsimp [j] at e
    omega
  have selected : ∑ a∈I,g (j a)≤∑' u,g u := by
    rw [←sum_image inject]
    exact sg.sum_le_tsum _ (fun u _ => ng u)
  have iden : marginMoment D H k-(k:ℝ)/2*marginMass D k =
      ∑ a∈I,marginWeight a*(H (j a)-(j a:ℝ)/2*D (j a)) := by
    unfold marginMoment marginMass
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    have h := mem_range.mp ha
    have dbl : 2*a≤k := by omega
    have ar : (j a:ℝ)=(k:ℝ)-2*a := by dsimp [j]; push_cast [Nat.cast_sub dbl]; rfl
    rw [show k-2*a=j a from rfl,ar]
    ring
  rw [iden]
  refine (abs_sum_le_sum_abs ..).trans ?_
  calc
    _ ≤ ∑ a∈I,common k*g (j a) := by
      apply sum_le_sum
      intro a ha
      have small : a≤k/2 := by have := mem_range.mp ha; omega
      have base : |H (j a)-(j a:ℝ)/2*D (j a)| ≤ ((j a:ℝ)+1)*D (j a)+H (j a) := by
        rw [abs_le]
        constructor <;> nlinarith only [nh (j a),nd (j a),mul_nonneg (Nat.cast_nonneg (j a): (0:ℝ)≤j a) (nd (j a))]
      rw [abs_mul,abs_of_nonneg (marginWeight_pos _).le]
      dsimp only [g]
      rw [← mul_assoc]
      exact mul_le_mul (weight_le small) base (abs_nonneg _) (mul_nonneg (common_pos _).le (tilt_pos _).le)
    _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left selected (common_pos _).le

/-- The conditional mean differs from k/2 by a bounded amount for either endpoint. -/
theorem margin_limit {D H : ℕ → ℝ} (nd : ∀ j,0≤D j) (nh : ∀ j,0≤H j)
    (p0 : 0<D 0) (p1 : 0<D 1)
    (sD : Summable fun j : ℕ => tilt j*((j:ℝ)+1)*D j)
    (sH : Summable fun j : ℕ => tilt j*H j) :
    (∃ C : ℝ, ∀ k : ℕ, |marginMoment D H k/marginMass D k-(k:ℝ)/2|≤C) ∧
    Tendsto (fun k : ℕ => (marginMoment D H k/marginMass D k)/k) atTop (𝓝 (1/2:ℝ)) := by
  let d := min (D 0) (D 1)
  let S := ∑' j : ℕ,tilt j*(((j:ℝ)+1)*D j+H j)
  have ds : 0<d := lt_min p0 p1
  have ns : 0≤S := tsum_nonneg (fun j => mul_nonneg (tilt_pos _).le
    (add_nonneg (mul_nonneg (by positivity) (nd _)) (nh _)))
  have uniform (k : ℕ) : |marginMoment D H k/marginMass D k-(k:ℝ)/2|≤S/d := by
    have mm := marginMass_pos D nd p0 p1 k
    have base := margin_error nd nh sD sH k
    have lower := mass_lower D nd k
    rw [show marginMoment D H k/marginMass D k-(k:ℝ)/2 =
        (marginMoment D H k-(k:ℝ)/2*marginMass D k)/marginMass D k by field_simp,
      abs_div,abs_of_pos mm]
    apply (div_le_div_iff₀ mm ds).mpr
    change |marginMoment D H k-(k:ℝ)/2*marginMass D k|≤common k*S at base
    change common k*d≤marginMass D k at lower
    nlinarith only [mul_le_mul_of_nonneg_right base ds.le,mul_le_mul_of_nonneg_right lower ns]
  refine ⟨⟨S/d,uniform⟩,?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have zero : Tendsto (fun k : ℕ => (S/d)/(k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ zero
  filter_upwards [eventually_gt_atTop 0] with k hk
  have kr : 0<(k:ℝ) := by exact_mod_cast hk
  rw [Real.norm_eq_abs,show (marginMoment D H k/marginMass D k)/k-(1/2:ℝ)=
    (marginMoment D H k/marginMass D k-(k:ℝ)/2)/k by field_simp]
  rw [abs_div,abs_of_pos kr]
  exact div_le_div_of_nonneg_right (uniform _) kr.le

end MissingSumFringes
