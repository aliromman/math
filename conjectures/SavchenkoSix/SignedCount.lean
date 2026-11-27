module

public import conjectures.SavchenkoSix.RegularCount
public import conjectures.SavchenkoSix.Moments
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

@[expose] public section
namespace SavchenkoSix
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

private def ones : Matrix V V ℤ := fun _ _ ↦ 1

omit [Fintype V] in
private theorem sign_entry (T : Tournament V) (i j : V) :
    T.sign i j = 2*T.adj i j+(if i=j then 1 else 0)-1 := by
  by_cases h : i=j
  · subst j;simp [Tournament.sign,Tournament.adj,T.loopless]
  · simp only [Tournament.sign,Tournament.adj,h,ite_false]
    cases T.arc i j <;> decide

omit [Fintype V] in
private theorem shifted (T : Tournament V) : 2 • T.adj+1 = T.sign+ones := by
  ext i j
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,ones,sign_entry]
  change (2:ℕ) • (T.adj i j)+(if i=j then 1 else 0) = _+1
  simp only [nsmul_eq_mul,Nat.cast_ofNat]
  ring

private theorem two_products {r : ℕ} (T : Tournament (Fin (2*r+1))) (hr : Regular r T) :
    T.sign*ones=0 ∧ ones*T.sign=0 := by
  have zero (i : Fin (2*r+1)) : ∑ j,T.sign i j=0 := by
    simp only [sign_entry,sum_sub_distrib,sum_add_distrib,←mul_sum,regular_row hr,sum_ite_eq,
      mem_univ,ite_true,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul]
    norm_num
  constructor
  · ext i j
    simpa [Matrix.mul_apply,ones] using zero i
  · ext i j
    simpa only [Matrix.mul_apply,ones,of_apply,one_mul,Matrix.zero_apply,sign_flip T _ j,sum_neg_distrib,neg_eq_zero] using zero j

private theorem split_power {S J : Matrix V V ℤ} (sj : S*J=0) (js : J*S=0) (k : ℕ) :
    (S+J)^(k+1)=S^(k+1)+J^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (S+J),ih,add_mul,mul_add,mul_add]
    have s := congrArg (fun X : Matrix V V ℤ ↦ S^k*X) sj
    have j := congrArg (fun X : Matrix V V ℤ ↦ J^k*X) js
    simp only [mul_zero,←mul_assoc,←pow_succ] at s j
    rw [s,j,zero_add,add_zero,←pow_succ,←pow_succ]

private theorem square_independent (T U : Tournament V) : (T.sign^2).trace=(U.sign^2).trace := by
  have prod (R : Tournament V) (i j : V) : R.sign i j*R.sign j i = if i=j then 0 else -1 := by
    rw [sign_flip R i j]
    by_cases e : i=j
    · simp [Tournament.sign,e]
    · simp only [Tournament.sign,e,ite_false]
      cases R.arc i j <;> decide
  change ∑ i,(T.sign^2) i i = ∑ i,(U.sign^2) i i
  simp only [pow_two,Matrix.mul_apply,prod]

/-- The terms depending only on the common all-ones matrix. -/
private def baseline (J : Matrix V V ℤ) : ℤ :=
  (J^6).trace-6*(J^5).trace+21*(J^4).trace-44*(J^3).trace+51*(J^2).trace-
    30*J.trace+7*(1 : Matrix V V ℤ).trace

private theorem adjacency_moments {r : ℕ} (T : Tournament (Fin (2*r+1))) (hr : Regular r T) :
    64*(T.adj^6).trace+96*(T.adj^4).trace =
    (T.sign^6).trace+21*(T.sign^4).trace+51*(T.sign^2).trace+
      baseline (ones : Matrix (Fin (2*r+1)) (Fin (2*r+1)) ℤ) := by
  let D := 2 • T.adj+1
  have poly : 64 • T.adj^6+96 • T.adj^4 = D^6-6•D^5+21•D^4-44•D^3+51•D^2-30•D+7•1 := by
    dsimp [D];noncomm_ring
  have both := two_products T hr
  have d (k : ℕ) : D^(k+1)=T.sign^(k+1)+ones^(k+1) := by
    change (2 • T.adj+1)^_=_
    rw [shifted]
    exact split_power both.1 both.2 k
  have tr := congrArg Matrix.trace poly
  rw [show D^6=_ from d 5,show D^5=_ from d 4,show D^4=_ from d 3,show D^3=_ from d 2,
      show D^2=_ from d 1,show D=T.sign+ones from shifted T] at tr
  simp only [trace_add,trace_sub,trace_smul] at tr
  simp only [nsmul_eq_mul,trace_odd T 5 (by decide),
    trace_odd T 3 (by decide),show T.sign.trace=0 by simpa using trace_odd T 1 (by decide)] at tr
  unfold baseline
  norm_num at tr ⊢
  linarith only [tr]

/-- Only the fourth and sixth moments of the sign matrix survive in the difference. -/
theorem cycle_identity {r : ℕ} (T U : Tournament (Fin (2*r+1))) (hT : Regular r T) (hU : Regular r U) :
    64*((orderedSix T : ℤ)-orderedSix U)=(T.sign^6).trace-(U.sign^6).trace+
      21*((T.sign^4).trace-(U.sign^4).trace) := by
  linarith only [ordinary_difference T U hT hU, adjacency_moments T hT, adjacency_moments U hU,
    square_independent T U]

end SavchenkoSix
