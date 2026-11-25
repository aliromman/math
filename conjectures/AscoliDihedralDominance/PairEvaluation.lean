module

public import conjectures.AscoliDihedralDominance.WeightedEvents
public import conjectures.AscoliDihedralDominance.Generalized

@[expose] public section
open Finset Equiv Function
namespace AscoliDihedral

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Group G] in
theorem uniform_weight (B k : ℕ) (p : Perm G) (hp : ∀x, period p x=k) (hk : 0<k) :
    weightPerm B p = (weightedPair B k).1^(Fintype.card G/k) := by
  classical
  have total := sum_period p
  simp only [hp,Finset.sum_const,Finset.card_univ,smul_eq_mul] at total
  rw [←total,Nat.mul_div_cancel _ hk,weightedPair_eq,weighted_cycle_factors]
  simp [hp]

namespace TwoMatchings
variable {g h : G} (M : TwoMatchings g h)

omit [Fintype G] [DecidableEq G] in
private theorem side_perm (x : G) : M.side (M.perm x) = !(M.side x) := by
  cases he : M.side x <;> simp [perm,alternating,he,M.leftFlip,M.rightFlip]

omit [Fintype G] [DecidableEq G] in
private theorem even_walk (k : ℕ) (x : G) :
    M.side ((⇑M.perm)^[2*k] x)=M.side x ∧
    (⇑M.perm)^[2*k] x = (if M.side x then h*g else g*h)^k*x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,iterate_add_apply]
    let y := M.perm (M.perm x)
    change M.side ((⇑M.perm)^[2*k] y)=_ ∧ (⇑M.perm)^[2*k] y=_
    have hy : M.side y = M.side x := by simp [y,M.side_perm]
    have hy' : y = (if M.side x then h*g else g*h)*x := by
      cases hc : M.side x <;> simp [y,perm,alternating,hc,M.leftFlip,M.rightFlip,mul_assoc]
    exact ⟨(ih y).1.trans hy,(ih y).2.trans (by rw [hy,hy',pow_succ,mul_assoc])⟩

omit [Fintype G] [DecidableEq G] in
theorem period_eq (x : G) : period M.perm x = 2*orderOf (g*h) := by
  have swap : orderOf (h*g)=orderOf (g*h) := SemiconjBy.orderOf_eq g (by
    show g*(h*g)=(g*h)*g
    rw [mul_assoc])
  let r := if M.side x then h*g else g*h
  have hr : orderOf r=orderOf (g*h) := by dsimp [r]; split <;> simp_all
  have hh : (⇑M.perm)^[2*orderOf (g*h)] x = x := by
    rw [(M.even_walk _ x).2,←hr]
    change r^orderOf r*x=x
    rw [pow_orderOf_eq_one,one_mul]
  have periodDvd : period M.perm x ∣ 2*orderOf (g*h) := IsPeriodicPt.minimalPeriod_dvd hh
  have periodic : (⇑M.perm)^[period M.perm x] x=x := isPeriodicPt_minimalPeriod _ _
  obtain ⟨t,ht⟩ : ∃t, period M.perm x=2*t := by
    rcases Nat.even_or_odd (period M.perm x) with he|ho
    · obtain ⟨t,ht⟩ := he; exact ⟨t,by omega⟩
    · obtain ⟨t,ht⟩ := ho
      rw [ht] at periodic
      change ((⇑M.perm)^[(2*t).succ]) x=x at periodic
      rw [iterate_succ_apply'] at periodic
      have hs := congrArg M.side periodic
      rw [M.side_perm,(M.even_walk t x).1] at hs
      cases M.side x <;> simp_all
  have he := (M.even_walk t x).2
  rw [ht] at periodic
  have hp : r^t=1 := mul_right_cancel (he.symm.trans (periodic.trans (one_mul x).symm))
  apply Nat.dvd_antisymm periodDvd
  rw [ht,←hr]
  exact Nat.mul_dvd_mul_left 2 (orderOf_dvd_of_pow_eq_one hp)

include M in
theorem pair_formula (B : ℕ) :
    familyWeight B (missingQuotients g∩missingQuotients h) =
      (weightedPair B (2*orderOf (g*h))).1^(Fintype.card G/(2*orderOf (g*h))) := by
  rw [M.weight,evaluatePerm_eq]
  exact uniform_weight B _ M.perm M.period_eq (by have := orderOf_pos (g*h); omega)

end TwoMatchings
end AscoliDihedral
