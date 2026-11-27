module

public import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace ChipShadow
open Finset HahnSeries
open scoped LaurentSeries PowerSeries

def denom (h a : ℕ) : LaurentSeries ℚ :=
  single 1 1 + HahnSeries.C ((h:ℚ)-a)

private theorem denom_ne (h a : ℕ) : denom h a≠0 := by
  intro eq
  have := congrArg (fun x : LaurentSeries ℚ ↦ x.coeff 1) eq
  simp only [denom,coeff_add,HahnSeries.C_apply,coeff_single,
    ite_eq_right (show (1:ℤ)≠0 by decide),coeff_zero] at this
  norm_num at this

/-- Sum the indicated negative Laurent coefficient at all possible integer knots. -/
def observable (N k : ℕ) (s : Multiset ℕ) : ℚ :=
  ∑ h ∈ range N, ((s.map (fun a ↦ (denom h a)⁻¹)).prod).coeff (-(k+1:ℤ))

theorem two_knots (N k a b : ℕ) (s : Multiset ℕ) :
    ((b:ℚ)-a)*observable N k (a ::ₘ b ::ₘ s)=
      observable N k (b ::ₘ s)-observable N k (a ::ₘ s) := by
  unfold observable
  rw [mul_sum,←sum_sub_distrib]
  apply sum_congr rfl;intro h _
  simp only [Multiset.map_cons,Multiset.prod_cons]
  let u := (s.map (fun a ↦ (denom h a)⁻¹)).prod
  have diff : HahnSeries.C ((b:ℚ)-a)=denom h a-denom h b := by
    unfold denom
    rw [show (b:ℚ)-a=((h:ℚ)-a)-(h-b) by ring,map_sub]
    abel
  have eq : ((b:ℚ)-a) • ((denom h a)⁻¹*((denom h b)⁻¹*u)) =
      (denom h b)⁻¹*u-(denom h a)⁻¹*u := by
    rw [←C_mul_eq_smul,diff]
    field_simp [denom_ne]
  simpa only [coeff_smul,coeff_sub,smul_eq_mul,u] using
    congrArg (fun x : LaurentSeries ℚ ↦ x.coeff (-(k+1:ℤ))) eq

/-- A run of length d+1 admits d cuts. The sum over cuts telescopes. -/
theorem split_sum (N k lo d : ℕ) (s : Multiset ℕ) :
    (∑ i ∈ range d, observable N k ((lo+i) ::ₘ (lo+i+1) ::ₘ s)) =
      d*observable N k (lo ::ₘ (lo+d) ::ₘ s) := by
  have step (i : ℕ) : observable N k ((lo+i) ::ₘ (lo+i+1) ::ₘ s)=
      observable N k ((lo+(i+1)) ::ₘ s)-observable N k ((lo+i) ::ₘ s) := by
    simpa [Nat.add_assoc] using two_knots N k (lo+i) (lo+i+1) s
  simp_rw [step]
  rw [sum_range_sub (fun i ↦ observable N k ((lo+i) ::ₘ s)) d, Nat.add_zero,←two_knots]
  simp

private theorem coeff_power (h a m k : ℕ) :
    ((denom h a)⁻¹^m).coeff (-(k+1:ℤ)) = if h=a ∧ k+1=m then 1 else 0 := by
  by_cases ha : h=a
  · subst h
    simp only [denom,sub_self,map_zero,add_zero,inv_single,inv_one,single_pow,
      one_pow,coeff_single, true_and, nsmul_eq_mul]
    split_ifs <;> first | rfl | omega
  · have ne : (h:ℚ)-a≠0 := sub_ne_zero.mpr (by exact_mod_cast ha)
    let f : ℚ⟦X⟧ := PowerSeries.X + PowerSeries.C ((h:ℚ)-a)
    have unit : IsUnit f := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [f,ne])
    obtain ⟨u,hu⟩ := unit
    let coe := ofPowerSeries ℤ ℚ
    have hf : coe f=denom h a := by
      simp only [coe,f,denom,map_add,ofPowerSeries_X,ofPowerSeries_C]
    have inv : (denom h a)⁻¹=coe (↑u⁻¹) := by
      apply inv_eq_of_mul_eq_one_right
      rw [←hf,←map_mul,←hu,Units.mul_inv,map_one]
    rw [inv,←map_pow]
    change ((↑((↑u⁻¹ : ℚ⟦X⟧)^m) : LaurentSeries ℚ)).coeff (-(k+1:ℤ))=_
    rw [PowerSeries.coeff_coe]
    simp only [ite_eq_left (show -(k+1:ℤ)<0 by omega),ha,false_and,ite_false]

theorem observable_constant {N : ℕ} (a : ℕ) (ha : a<N) (m k : ℕ) :
    observable N k (Multiset.replicate m a)=if k+1=m then 1 else 0 := by
  unfold observable
  simp only [Multiset.map_replicate,Multiset.prod_replicate,coeff_power]
  by_cases h : k+1=m <;> simp [h,ha]

end ChipShadow
end
