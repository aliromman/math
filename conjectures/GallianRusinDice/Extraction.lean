module

public import conjectures.GallianRusinDice.Factors
public import conjectures.GallianRusinDice.Multiplicity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace GallianRusinDice
open Polynomial Finset

private theorem peel {p : ℤ[X]} (prime : Prime p) (k : ℕ) {A B T : ℤ[X]}
    (h : A*B=p^k*T) : ∃ n U V, A=p^n*U ∧ U*V=T := by
  induction k generalizing A B with
  | zero => exact ⟨0,A,B,by simp,by simpa using h⟩
  | succ k ih =>
    rw [pow_succ',mul_assoc] at h
    obtain ⟨Y,e⟩|⟨Y,e⟩ := prime.dvd_or_dvd (h ▸ dvd_mul_right p _)
    · rw [e,mul_assoc] at h
      obtain ⟨n,U,V,nu,uv⟩ := ih (mul_left_cancel₀ prime.ne_zero h)
      exact ⟨n+1,U,V,by rw [e,nu,pow_succ',mul_assoc],uv⟩
    · rw [e,mul_left_comm] at h
      exact ih (mul_left_cancel₀ prime.ne_zero h)

private theorem faces {x y z : ℕ} {s : ℤ} (unit : IsUnit s) (sum : (3:ℤ)^x*(5^y*(7^z*s))=105) :
    x=1 ∧ y=1 ∧ z=1 ∧ s=1 := by
  rcases Int.isUnit_iff.mp unit with rfl|rfl
  · have pos3 : (1:ℤ)≤3^x := one_le_pow₀ (by decide)
    have pos5 : (1:ℤ)≤5^y := one_le_pow₀ (by decide)
    have pos7 : (1:ℤ)≤7^z := one_le_pow₀ (by decide)
    have xb : x≤4 := by
      by_contra! bad
      have high : (3:ℤ)^5≤3^x := pow_le_pow_right₀ (by decide) bad
      norm_num at high
      nlinarith [mul_nonneg (sub_nonneg.mpr pos5) (sub_nonneg.mpr pos7),
        mul_nonneg (sub_nonneg.mpr high) (show (0:ℤ)≤5^y*7^z by positivity)]
    have yb : y≤2 := by
      by_contra! bad
      have high : (5:ℤ)^3≤5^y := pow_le_pow_right₀ (by decide) bad
      norm_num at high
      nlinarith [mul_le_mul_of_nonneg_left high (show (0:ℤ)≤3^x*7^z by positivity),
        one_le_mul_of_one_le_of_one_le pos3 pos7]
    have zb : z≤2 := by
      by_contra! bad
      have high : (7:ℤ)^3≤7^z := pow_le_pow_right₀ (by decide) bad
      norm_num at high
      nlinarith [mul_le_mul_of_nonneg_left high (show (0:ℤ)≤3^x*5^y by positivity),
        one_le_mul_of_one_le_of_one_le pos3 pos5]
    interval_cases x <;> interval_cases y <;> interval_cases z <;> norm_num at *
  · have pos : 0<(3:ℤ)^x*(5^y*7^z) := by positivity
    linarith

theorem extraction {P : ℤ[X]} (game : SolutionDie 105 P) :
    ∃ c : Code, c.a<7 ∧ c.b<7 ∧ c.c<7 ∧ c.d<7 ∧ P=assemble c := by
  obtain ⟨others,_,_,h⟩ := game.2
  let k := others.length+1
  rw [standard_eq,assemble_eq] at h
  simp only [pow_one,mul_pow] at h
  change P*others.prod=cyclotomic 3 ℤ^k*(cyclotomic 5 ℤ^k*(cyclotomic 7 ℤ^k*
    (cyclotomic 15 ℤ^k*(cyclotomic 21 ℤ^k*(cyclotomic 35 ℤ^k*cyclotomic 105 ℤ^k))))) at h
  obtain ⟨x,A,B,Px,h⟩ := peel (cyclotomic.irreducible (n := 3) (by decide)).prime k h
  obtain ⟨y,A,B,Py,h⟩ := peel (cyclotomic.irreducible (n := 5) (by decide)).prime k h
  obtain ⟨z,A,B,Pz,h⟩ := peel (cyclotomic.irreducible (n := 7) (by decide)).prime k h
  obtain ⟨a,A,B,Pa,h⟩ := peel (cyclotomic.irreducible (n := 15) (by decide)).prime k h
  obtain ⟨b,A,B,Pb,h⟩ := peel (cyclotomic.irreducible (n := 21) (by decide)).prime k h
  obtain ⟨c,A,B,Pc,h⟩ := peel (cyclotomic.irreducible (n := 35) (by decide)).prime k h
  rw [←mul_one (cyclotomic 105 ℤ ^ k)] at h
  obtain ⟨d,A,B,Pd,h⟩ := peel (cyclotomic.irreducible (n := 105) (by decide)).prime k h
  obtain ⟨s,su,eq⟩ := Polynomial.isUnit_iff.mp (isUnit_iff_dvd_one.mpr ⟨B,h.symm⟩)
  rw [←eq] at Pd
  rw [Py,Pz,Pa,Pb,Pc,Pd] at Px
  have eval := game.1.2
  rw [Px] at eval
  simp only [eval_mul,eval_pow,eval_C] at eval
  have values (j : ℕ) (hj : j∈([3,5,7,15,21,35,105] : List ℕ)) :
      (cyclotomic j ℤ).eval 1=if j∈([3,5,7] : List ℕ) then (j:ℤ) else 1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [←table3,←table5,←table7,←table15,←table21,←table35,←table105,table,polynomial]
  rw [values 3 (by decide),values 5 (by decide),values 7 (by decide),values 15 (by decide),
    values 21 (by decide),values 35 (by decide),values 105 (by decide)] at eval
  norm_num at eval
  obtain ⟨rfl,rfl,rfl,rfl⟩ := faces su eval
  simp only [pow_one,map_one,mul_one] at Px
  have code : P=assemble ⟨a,b,c,d⟩ := by rw [assemble_eq]; exact Px
  have bound (j t : ℕ) (jpos : 0<j) (jm : j∣105) (dvd : cyclotomic j ℤ ^ t∣P) : t<7 := by
    have low := odd_multiplicity_bound (by decide : Odd 105) jpos jm game dvd
    by_contra! high
    have := Nat.pow_le_pow_right (by decide : 0<2) high
    omega
  refine ⟨⟨a,b,c,d⟩,bound 15 a (by decide) (by decide) ?_,
    bound 21 b (by decide) (by decide) ?_,bound 35 c (by decide) (by decide) ?_,
    bound 105 d (by decide) (by decide) ?_,code⟩ <;> rw [Px]
  · exact ⟨cyclotomic 3 ℤ * cyclotomic 5 ℤ * cyclotomic 7 ℤ * cyclotomic 21 ℤ^b * cyclotomic 35 ℤ^c * cyclotomic 105 ℤ^d,by ac_rfl⟩
  · exact ⟨cyclotomic 3 ℤ * cyclotomic 5 ℤ * cyclotomic 7 ℤ * cyclotomic 15 ℤ^a * cyclotomic 35 ℤ^c * cyclotomic 105 ℤ^d,by ac_rfl⟩
  · exact ⟨cyclotomic 3 ℤ * cyclotomic 5 ℤ * cyclotomic 7 ℤ * cyclotomic 15 ℤ^a * cyclotomic 21 ℤ^b * cyclotomic 105 ℤ^d,by ac_rfl⟩
  · exact ⟨cyclotomic 3 ℤ * cyclotomic 5 ℤ * cyclotomic 7 ℤ * cyclotomic 15 ℤ^a * cyclotomic 21 ℤ^b * cyclotomic 35 ℤ^c,by ac_rfl⟩

end GallianRusinDice
