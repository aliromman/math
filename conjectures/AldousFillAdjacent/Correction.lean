module

public import conjectures.AldousFillAdjacent.Returns
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
namespace AldousFillAdjacent
open Finset Filter
open scoped BigOperators Asymptotics Topology

private theorem fixed_return_bound (j k : ℕ) (deg : j/2+k≤j) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ m : ℕ in atTop, returnProb m j*((m:ℝ)+1)^k≤C := by
  obtain ⟨C,h⟩ := closed_count j
  refine ⟨C,Nat.cast_nonneg C,?_⟩
  filter_upwards [h] with m hm
  let cnt := (univ.filter (fun w : Fin j → Option (Fin m) ↦ wordProduct w=1)).card
  have count : (cnt:ℝ)≤(C:ℝ)*((m:ℝ)+1)^(j/2) := by exact_mod_cast hm
  have one : 1≤(m:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) m]
  rw [return_count]
  change cnt/((m:ℝ)+1)^j*((m:ℝ)+1)^k≤C
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  calc
    _ ≤ ((C:ℝ)*((m:ℝ)+1)^(j/2))*((m:ℝ)+1)^k :=
      mul_le_mul_of_nonneg_right count (by positivity)
    _ = (C:ℝ)*((m:ℝ)+1)^(j/2+k) := by rw [pow_add,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one deg) (Nat.cast_nonneg _)

private theorem tail_bound : ∃ C : ℝ, 0≤C ∧ ∀ᶠ m : ℕ in atTop,
    (∑ i ∈ range 11, returnProb m (3+i))*((m:ℝ)+1)^2≤C := by
  have bound (i : ℕ) := fixed_return_bound (3+i) 2 (by omega)
  choose C N H using bound
  refine ⟨∑ i ∈ range 11, C i,sum_nonneg (fun i _ ↦ N i),?_⟩
  filter_upwards [(eventually_all_finset (range 11)).2 (fun i _ ↦ H i)] with m hm
  rw [sum_mul]
  exact sum_le_sum hm

private theorem error_upper : ∃ C : ℝ, 0≤C ∧ ∀ᶠ m : ℕ in atTop,
    stationaryTime m / m.factorial - (1+2/((m:ℝ)+1)) ≤ C/((m:ℝ)+1)^2 := by
  obtain ⟨C,Cpos,ht⟩ := tail_bound
  obtain ⟨D,Dpos,hu⟩ := fixed_return_bound 14 7 (by decide)
  refine ⟨C+4*D,by positivity,?_⟩
  filter_upwards [ht,hu,eventually_ge_atTop 3] with m t u hm
  obtain ⟨r0,r1,r2⟩ := first_returns hm
  have first : (∑ i∈range 3, returnProb m i)=1+2/((m:ℝ)+1) := by
    rw [show 3=2+1 by rfl,sum_range_succ,show 2=1+1 by rfl,sum_range_succ]
    simp [r0,r1,r2];ring
  have split : (∑ i∈range 14, returnProb m i) =
      1+2/((m:ℝ)+1)+(∑ i∈range 11, returnProb m (3+i)) := by
    rw [show 14=3+11 by rfl,sum_range_add,first]
  have sums := sum_le_sum (s:=range 14) (fun i _ ↦ sub_le_self (returnProb m i)
    (by positivity : 0≤(1:ℝ)/m.factorial))
  have rem := (return_expansion m 7).2
  change stationaryTime m/m.factorial-(∑ i∈range 14, (returnProb m i-1/m.factorial))≤_ at rem
  rw [split] at sums
  have bound : stationaryTime m/m.factorial-(1+2/((m:ℝ)+1)) ≤
      (∑ i∈range 11, returnProb m (3+i))+(2*(m:ℝ)^2)^2*(m+1)*returnProb m 14 := by
    linarith only [rem,sums]
  have cap : ((2*(m:ℝ)^2)^2*(m+1))*((m:ℝ)+1)^2 ≤ 4*((m:ℝ)+1)^7 := by
    calc
      _ = 4*(m:ℝ)^4*(m+1)^3 := by ring
      _ ≤ 4*((m:ℝ)+1)^4*(m+1)^3 := by gcongr;linarith
      _ = _ := by ring
  have last : ((2*(m:ℝ)^2)^2*(m+1)*returnProb m 14)*((m:ℝ)+1)^2 ≤ 4*D := by
    calc
      _ = (((2*(m:ℝ)^2)^2*(m+1))*((m:ℝ)+1)^2)*returnProb m 14 := by ring
      _ ≤ (4*((m:ℝ)+1)^7)*returnProb m 14 := mul_le_mul_of_nonneg_right cap (return_nonneg _ _)
      _ = 4*(returnProb m 14*((m:ℝ)+1)^7) := by ring
      _ ≤ _ := by linarith only [u]
  apply (le_div_iff₀ (by positivity)).2
  exact (mul_le_mul_of_nonneg_right bound (by positivity)).trans (by rw [add_mul];exact add_le_add t last)

private theorem square_le_factorial {m : ℕ} (hm : 4≤m) : m^2≤m.factorial := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  rw [Nat.factorial_succ,pow_two]
  exact Nat.mul_le_mul_left _ (Nat.lt_factorial_self (by omega))

/-- For the cyclic adjacent-transposition shuffle, the coefficient of 1/m in
the stationary mean hitting time, after division by m!, is two. -/
theorem corrected_expansion :
    (fun m : ℕ ↦ stationaryTime m/m.factorial-(1+2/(m:ℝ))) =O[atTop]
      (fun m : ℕ ↦ (1:ℝ)/m^2) := by
  obtain ⟨C,Cpos,h⟩ := error_upper
  apply Asymptotics.IsBigO.of_bound (C+6)
  filter_upwards [h,eventually_ge_atTop 4] with m hu hm
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  have fp : (0:ℝ)<m.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have sq : (m:ℝ)^2≤m.factorial := by exact_mod_cast square_le_factorial hm
  have p : (4:ℝ)/m.factorial≤4/(m:ℝ)^2 := by gcongr
  have d : 2/(m:ℝ)-2/((m:ℝ)+1)≤2/(m:ℝ)^2 := by field_simp;nlinarith
  have u : 2/((m:ℝ)+1)≤2/(m:ℝ) := by gcongr;linarith
  have c : C/((m:ℝ)+1)^2≤C/(m:ℝ)^2 := by gcongr;linarith
  have low := finite_lower (mean_tendsto m)
  simp only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(1:ℝ)/m^2)]
  apply abs_le.2
  constructor
  · have nonneg : 0≤C/(m:ℝ)^2 := by positivity
    have add : (C+6)*(1/(m:ℝ)^2)=C/(m:ℝ)^2+2/(m:ℝ)^2+4/(m:ℝ)^2 := by ring
    linarith only [add,nonneg,low,p,d]
  · have nonneg : 0≤6/(m:ℝ)^2 := by positivity
    have add : (C+6)*(1/(m:ℝ)^2)=C/(m:ℝ)^2+6/(m:ℝ)^2 := by ring
    linarith only [add,nonneg,hu,u,c]

/-- info: 'AldousFillAdjacent.corrected_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corrected_expansion

end AldousFillAdjacent
