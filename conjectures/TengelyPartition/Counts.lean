module

public import conjectures.TengelyPartition.Statement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section
namespace TengelyPartition
open Finset

private theorem slice {a n z : ℕ} (h : a*z≤n) :
    ((range (n+1)).filter fun y ↦ 2*y+a*z≤n) = range ((n-a*z)/2+1) := by
  ext y;simp only [mem_filter,mem_range];omega

/-- Sum over the number of copies of the largest part in reverse order. -/
private theorem block (a q r : ℕ) (hr : r<a) :
    parts a (a*q+r)=∑ j∈range (q+1), ((a*j+r)/2+1) := by
  have ha : 0<a := by omega
  have div : (a*q+r)/a=q := by rw [Nat.mul_add_div ha,Nat.div_eq_of_lt hr,Nat.add_zero]
  unfold parts
  rw [div,←sum_range_reflect (fun j ↦ (a*j+r)/2+1) (q+1)]
  apply sum_congr rfl
  intro j hj
  have le : j≤q := by have h := mem_range.mp hj;omega
  have diff := Nat.mul_sub_left_distrib a q j
  have aj := Nat.mul_le_mul_left a le
  rw [slice (by omega),card_range]
  congr 2
  simp only [Nat.add_sub_cancel]
  omega

/-- Each pair of consecutive summands gives a linear progression. -/
private theorem pair_sum (a r t : ℕ) :
    (∑ j∈range (2*t), ((a*j+r)/2+1)) + a*t =
      a*t^2 + (r/2+(a+r)/2+2)*t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2*(t+1)=2*t+1+1 by omega,sum_range_succ,sum_range_succ]
    have e : (a*(2*t)+r)/2=a*t+r/2 := by
      rw [show a*(2*t)+r=2*(a*t)+r by ring,Nat.mul_add_div (by decide : 0<2)]
    have f : (a*(2*t+1)+r)/2=a*t+(a+r)/2 := by
      rw [show a*(2*t+1)+r=2*(a*t)+(a+r) by ring,Nat.mul_add_div (by decide : 0<2)]
    rw [e,f]
    nlinarith only [ih]

/-- On a suitable residue class the count is exactly a quadratic with zero constant term. -/
theorem block_value {a r c t : ℕ} (hr : r<a) (hc : r/2+(a+r)/2+2=a+c) (ht : 0<t) :
    parts a (a*(2*t-1)+r)=a*t^2+c*t := by
  have h := pair_sum a r t
  rw [hc] at h
  rw [block a (2*t-1) r hr,show 2*t-1+1=2*t by omega]
  nlinarith only [h]

/-- For every third part, a positive linear coefficient is available. -/
theorem top_residue {a : ℕ} (ha : 3≤a) :
    ∃ r<a, ∃ c, 0<c ∧ r/2+(a+r)/2+2=a+c := by
  refine ⟨a-1,by omega,(a+1)/2,by omega,?_⟩
  omega

end TengelyPartition
