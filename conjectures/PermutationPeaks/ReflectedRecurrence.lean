module

public import conjectures.PermutationPeaks.NewtonDifferences

/-! Definitions and lemmas from Alex Chengyu Li’s proof of coefficient concavity.
Adapted from the MIT-licensed archive, DOI 10.5281/zenodo.22661864. -/

@[expose] public section
namespace PermutationPeaks

namespace ReflectedNewton
open Finset Polynomial

theorem reflectedLift_degree (P : Polynomial ℝ) (m : ℕ) :
    (reflectedLift P m).natDegree ≤ m-1 := by
  unfold reflectedLift
  apply natDegree_sum_le_of_forall_le
  intro k hk
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  have hk' : k+1 ≤ m-1 := by have := mem_range.mp hk; omega
  simpa only [risingPolynomial_natDegree,natDegree_X_sub_C,mul_one] using hk'

noncomputable def choosePolynomial (m : ℕ) : Polynomial ℝ :=
  (risingPolynomial (m-1)).comp (X+C (2-(m : ℝ)))

theorem choosePolynomial_eval (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (choosePolynomial m).eval x=Ring.choose x (m-1) := by
  simp only [choosePolynomial,eval_comp,eval_add,eval_X,eval_C,risingPolynomial_eval]
  rw [rising_literal]
  congr 1
  rw [Nat.cast_sub hm]
  push_cast
  ring

theorem choosePolynomial_degree (m : ℕ) : (choosePolynomial m).natDegree ≤ m-1 := by
  unfold choosePolynomial
  apply natDegree_comp_le.trans
  simp only [risingPolynomial_natDegree,natDegree_X_add_C,mul_one,le_refl]

theorem backward_choosePolynomial (m j : ℕ) (hm : 2 ≤ m) (hj : j < m) :
    backward (choosePolynomial m).eval j (m : ℝ)=((m-j : ℕ) : ℝ) := by
  have heval : (choosePolynomial m).eval=fun x => Ring.choose x (m-1) := by
    funext x
    exact choosePolynomial_eval m (by omega) x
  rw [heval]
  exact constant_two_rising_coefficient m j hm hj

theorem reflected_lift_recurrence (P : Polynomial ℝ) (m : ℕ)
    (hm : 3 ≤ m) (hP : P.natDegree ≤ m-3) :
    reflectedLift P m+reflectedLift P (m-1)=
      C (P.eval ((m : ℝ)-1))*choosePolynomial m-C 2*P := by
  apply polynomial_eq_of_backward _ _ (m : ℝ)
  intro j
  have hleft : (reflectedLift P m+reflectedLift P (m-1)).eval=
      fun x => (reflectedLift P m).eval x+(reflectedLift P (m-1)).eval x := by funext x; simp
  have hright : (C (P.eval ((m : ℝ)-1))*choosePolynomial m-C 2*P).eval=
      fun x => P.eval ((m : ℝ)-1)*(choosePolynomial m).eval x-2*P.eval x := by funext x; simp
  rw [hleft,hright,backward_add,backward_sub,backward_const_mul,backward_const_mul]
  have hvalue : P.eval (m : ℝ)-backward P.eval 1 (m : ℝ)=P.eval ((m : ℝ)-1) := by
    simp only [backward]
    ring
  by_cases hj : j < m
  · rw [backward_choosePolynomial m j (by omega) hj]
    cases j with
    | zero =>
      simp only [backward_zero,Nat.sub_zero]
      rw [reflectedLift_at_center,backward_previous_lift_zero P m hm hP]
      have hcast : ((m-2 : ℕ) : ℝ)=(m : ℝ)-2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ m)]
        norm_num
      rw [hcast]
      nlinarith
    | succ j =>
      rw [reflectedLift_coefficient P m j (by omega),backward_previous_lift_positive P m (j+1) hm (by omega) hP]
      have hidx : m-(j+1)=m-1-j := by omega
      have hcast : ((m-1-(j+1) : ℕ) : ℝ)=((m-(j+1) : ℕ) : ℝ)-1 := by
        have heq : m-1-(j+1)+1=m-(j+1) := by omega
        have heqR := congrArg (fun n : ℕ => (n : ℝ)) heq
        push_cast at heqR
        linarith
      simp only [reflectedCoefficient]
      rw [hcast,hidx]
      nlinarith
  · have hd1 := reflectedLift_degree P m
    have hd2 := reflectedLift_degree P (m-1)
    have hdc := choosePolynomial_degree m
    rw [backward_polynomial_vanish _ (by omega : (reflectedLift P m).natDegree < j),
      backward_polynomial_vanish _ (by omega : (reflectedLift P (m-1)).natDegree < j),
      backward_polynomial_vanish _ (by omega : (choosePolynomial m).natDegree < j),
      backward_polynomial_vanish P (by omega : P.natDegree < j)]
    ring

end ReflectedNewton

end PermutationPeaks
