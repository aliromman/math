module

public import conjectures.GallianRusinGame.Factors
public import conjectures.GallianRusinGame.Multiplicity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace GallianRusinGame
open GallianRusin Polynomial Finset

private theorem faces {x y z : ℕ} {s : ℤ} (unit : IsUnit s) (sum : (2:ℤ)^x*(3^y*(5^z*s))=30) :
    x=1 ∧ y=1 ∧ z=1 ∧ s=1 := by
  rcases Int.isUnit_iff.mp unit with rfl|rfl
  · have p2 : (1:ℤ)≤2^x := one_le_pow₀ (by decide)
    have p3 : (1:ℤ)≤3^y := one_le_pow₀ (by decide)
    have p5 : (1:ℤ)≤5^z := one_le_pow₀ (by decide)
    have xb : x≤4 := by
      by_contra! bad
      have high : (2:ℤ)^5≤2^x := pow_le_pow_right₀ (by decide) bad
      norm_num at high
      nlinarith [mul_le_mul_of_nonneg_left high (show (0:ℤ)≤3^y*5^z by positivity),
        one_le_mul_of_one_le_of_one_le p3 p5]
    have yb : y≤3 := by
      by_contra! bad
      have high : (3:ℤ)^4≤3^y := pow_le_pow_right₀ (by decide) bad
      norm_num at high
      nlinarith [mul_le_mul_of_nonneg_left high (show (0:ℤ)≤2^x*5^z by positivity),
        one_le_mul_of_one_le_of_one_le p2 p5]
    have zb : z≤2 := by
      by_contra! bad
      have high : (5:ℤ)^3≤5^z := pow_le_pow_right₀ (by decide) bad
      norm_num at high
      nlinarith [mul_le_mul_of_nonneg_left high (show (0:ℤ)≤2^x*3^y by positivity),
        one_le_mul_of_one_le_of_one_le p2 p3]
    interval_cases x <;> interval_cases y <;> interval_cases z <;> norm_num at *
  · have pos : 0<(2:ℤ)^x*(3^y*5^z) := by positivity
    linarith

theorem extraction {P : ℤ[X]} (game : SolutionDie 30 P) :
    ∃ c : Code, c.a<11 ∧ c.b<11 ∧ c.c<11 ∧ c.d<11 ∧ P=assemble c := by
  obtain ⟨k,_,play⟩ := solutionDie_iff_plays.mp game
  obtain ⟨die,others,_,_,h⟩ := play
  rw [standard_eq,assemble_eq] at h
  simp only [pow_one,mul_pow] at h
  change P*others.prod=cyclotomic 2 ℤ^k*(cyclotomic 3 ℤ^k*(cyclotomic 5 ℤ^k*
    (cyclotomic 6 ℤ^k*(cyclotomic 10 ℤ^k*(cyclotomic 15 ℤ^k*cyclotomic 30 ℤ^k))))) at h
  obtain ⟨x,A,B,Px,h⟩ := peel (cyclotomic.irreducible (n := 2) (by decide)).prime k h
  obtain ⟨y,A,B,Py,h⟩ := peel (cyclotomic.irreducible (n := 3) (by decide)).prime k h
  obtain ⟨z,A,B,Pz,h⟩ := peel (cyclotomic.irreducible (n := 5) (by decide)).prime k h
  obtain ⟨a,A,B,Pa,h⟩ := peel (cyclotomic.irreducible (n := 6) (by decide)).prime k h
  obtain ⟨b,A,B,Pb,h⟩ := peel (cyclotomic.irreducible (n := 10) (by decide)).prime k h
  obtain ⟨c,A,B,Pc,h⟩ := peel (cyclotomic.irreducible (n := 15) (by decide)).prime k h
  rw [←mul_one (cyclotomic 30 ℤ ^ k)] at h
  obtain ⟨d,A,B,Pd,h⟩ := peel (cyclotomic.irreducible (n := 30) (by decide)).prime k h
  obtain ⟨s,su,eq⟩ := Polynomial.isUnit_iff.mp (isUnit_iff_dvd_one.mpr ⟨B,h.symm⟩)
  rw [←eq] at Pd
  rw [Py,Pz,Pa,Pb,Pc,Pd] at Px
  have eval := die.2
  rw [Px] at eval
  simp only [eval_mul,eval_pow,eval_C] at eval
  have values (j : ℕ) (hj : j∈([2,3,5,6,10,15,30] : List ℕ)) :
      (cyclotomic j ℤ).eval 1=if j∈([2,3,5] : List ℕ) then (j:ℤ) else 1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [←table2,←table3,←table5,←table6,←table10,←table15,←table30,table,commonFactor,polynomial]
  rw [values 2 (by decide),values 3 (by decide),values 5 (by decide),values 6 (by decide),
    values 10 (by decide),values 15 (by decide),values 30 (by decide)] at eval
  norm_num at eval
  obtain ⟨rfl,rfl,rfl,rfl⟩ := faces su eval
  simp only [pow_one,map_one,mul_one] at Px
  have code : P=assemble ⟨a,b,c,d⟩ := by rw [assemble_eq]; exact Px
  have bound (j t : ℕ) (jpos : 0<j) (jm : j∣30) (dvd : cyclotomic j ℤ ^ t∣P) : t<11 := by
    have low := multiplicity_bound (p := 7) (by decide) (by decide) jpos jm game dvd
    by_contra! high
    have bound := Nat.pow_le_pow_right (by decide : 0<7) high
    omega
  refine ⟨⟨a,b,c,d⟩,bound 6 a (by decide) (by decide) ?_,
    bound 10 b (by decide) (by decide) ?_,bound 15 c (by decide) (by decide) ?_,
    bound 30 d (by decide) (by decide) ?_,code⟩ <;> rw [Px]
  · exact ⟨cyclotomic 2 ℤ * cyclotomic 3 ℤ * cyclotomic 5 ℤ * cyclotomic 10 ℤ^b * cyclotomic 15 ℤ^c * cyclotomic 30 ℤ^d,by ac_rfl⟩
  · exact ⟨cyclotomic 2 ℤ * cyclotomic 3 ℤ * cyclotomic 5 ℤ * cyclotomic 6 ℤ^a * cyclotomic 15 ℤ^c * cyclotomic 30 ℤ^d,by ac_rfl⟩
  · exact ⟨cyclotomic 2 ℤ * cyclotomic 3 ℤ * cyclotomic 5 ℤ * cyclotomic 6 ℤ^a * cyclotomic 10 ℤ^b * cyclotomic 30 ℤ^d,by ac_rfl⟩
  · exact ⟨cyclotomic 2 ℤ * cyclotomic 3 ℤ * cyclotomic 5 ℤ * cyclotomic 6 ℤ^a * cyclotomic 10 ℤ^b * cyclotomic 15 ℤ^c,by ac_rfl⟩

end GallianRusinGame
