module

public import conjectures.PermutationPeaks.Counting

/-! Definitions and lemmas from Alex Chengyu Li’s proof of coefficient concavity.
Adapted from the MIT-licensed archive, DOI 10.5281/zenodo.22661864. -/

@[expose] public section
namespace PermutationPeaks

namespace ReflectedNewton
open Finset
variable {R : Type*} [CommRing R]

def backward (f : R → R) : ℕ → R → R
  | 0 => f
  | n + 1 => fun x => backward f n x - backward f n (x - 1)

@[simp] theorem backward_zero (f : R → R) (x : R) : backward f 0 x = f x := rfl

theorem backward_step (f : R → R) (n : ℕ) (u : R) :
    backward f n u = backward f n (u + 1) - backward f (n + 1) (u + 1) := by
  simp only [backward, add_sub_cancel_right]
  ring

theorem backward_forward (f : R → R) (n : ℕ) (x : R) :
    backward f n x = ((fwdDiff (1 : R))^[n] f) (x - n) := by
  induction n generalizing x with
  | zero => simp [backward]
  | succ n ih =>
    change backward f n x - backward f n (x - 1) = _
    rw [ih, ih, Function.iterate_succ_apply']
    simp only [fwdDiff, Nat.cast_add, Nat.cast_one]
    congr 1 <;> ring

theorem backward_polynomial_vanish (P : Polynomial R) {n : ℕ}
    (hn : P.natDegree < n) (x : R) : backward P.eval n x = 0 := by
  rw [backward_forward, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hn]
  rfl

theorem backward_tail_finite (f : R → R) (u : R) (j N : ℕ) :
    (∑ i ∈ range (N + 1), backward f (j + i) u) =
      backward f j (u + 1) - backward f (j + N + 1) (u + 1) := by
  induction N with
  | zero => simp [backward_step f j u]
  | succ N ih =>
    rw [sum_range_succ, ih, backward_step f (j + (N + 1)) u]
    simp only [Nat.add_assoc]
    ring

theorem backward_tail_shift (P : Polynomial R) (u : R) (j : ℕ) :
    backward P.eval j (u + 1) =
      ∑ i ∈ range (P.natDegree + 1), backward P.eval (j + i) u := by
  rw [backward_tail_finite]
  rw [backward_polynomial_vanish P (n := j + P.natDegree + 1) (by omega) (u+1)]
  simp

theorem backward_nonneg_shift (P : Polynomial ℝ) (u : ℝ)
    (hu : ∀ j, 0 ≤ backward P.eval j u) (h : ℕ) :
    ∀ j, 0 ≤ backward P.eval j (u + h) := by
  induction h with
  | zero => simpa using hu
  | succ h ih =>
    intro j
    rw [Nat.cast_succ, ← add_assoc, backward_tail_shift]
    exact sum_nonneg fun i _ => ih (j + i)

end ReflectedNewton
namespace ReflectedNewton
open Finset
variable {R : Type*} [CommRing R]

theorem backward_tail_bound (P : Polynomial R) (D : ℕ) (hD : P.natDegree ≤ D)
    (u : R) (j : ℕ) :
    backward P.eval j (u+1) = ∑ i ∈ range (D+1), backward P.eval (j+i) u := by
  rw [backward_tail_finite]
  rw [backward_polynomial_vanish P (n := j+D+1) (by omega) (u+1)]
  simp

theorem backward_weighted_telescope (f : R → R) (u : R) (j N : ℕ) :
    (∑ i ∈ range (N+1), (i+1 : R) * backward f (j+i) u) =
      (∑ i ∈ range (N+1), backward f (j+i) (u+1)) -
      (N+1 : R) * backward f (j+N+1) (u+1) := by
  induction N with
  | zero => simp [backward_step f j u]
  | succ N ih =>
    rw [sum_range_succ, ih]
    conv_rhs => rw [sum_range_succ]
    rw [backward_step f (j+(N+1)) u]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
    ring

theorem backward_double_shift (P : Polynomial R) (D : ℕ) (hD : P.natDegree ≤ D)
    (u : R) (j : ℕ) :
    backward P.eval j (u+2) =
      ∑ i ∈ range (D+1), (i+1 : R) * backward P.eval (j+i) u := by
  rw [backward_weighted_telescope]
  rw [backward_polynomial_vanish P (n := j+D+1) (by omega) (u+1)]
  rw [mul_zero, sub_zero, ← backward_tail_bound P D hD (u+1) j]
  congr 1
  ring

end ReflectedNewton
namespace ReflectedNewton
open Finset

noncomputable def rising (j : ℕ) (x : ℝ) : ℝ := Ring.multichoose x j

theorem rising_literal (j : ℕ) (x : ℝ) :
    rising j x = Ring.choose (x+j-1) j := Ring.multichoose_eq x j

@[simp] theorem rising_zero_order (x : ℝ) : rising 0 x = 1 := by
  exact Ring.multichoose_zero_right x

@[simp] theorem rising_at_zero_succ (j : ℕ) : rising (j+1) 0 = 0 := by
  exact Ring.multichoose_zero_succ j

theorem rising_difference (j : ℕ) (x : ℝ) :
    rising (j+1) x - rising (j+1) (x-1) = rising j x := by
  have h := Ring.multichoose_succ_succ (x-1) j
  simp only [sub_add_cancel] at h
  unfold rising
  linarith

theorem backward_from_first {R : Type*} [CommRing R] (f : R → R) (n : ℕ) (x : R) :
    backward f (n+1) x = backward (backward f 1) n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change backward f (n+1) x - backward f (n+1) (x-1) = _
    rw [ih, ih]
    rfl

theorem backward_const {R : Type*} [CommRing R] (c : R) (n : ℕ) (x : R) :
    backward (fun _ => c) (n+1) x = 0 := by
  induction n generalizing x with
  | zero => simp [backward]
  | succ n ih =>
    change backward (fun _ : R => c) (n+1) x - backward (fun _ : R => c) (n+1) (x-1) = 0
    rw [ih, ih, sub_self]

theorem backward_rising (j n : ℕ) (x : ℝ) :
    backward (rising j) n x = if n ≤ j then rising (j-n) x else 0 := by
  induction n generalizing j x with
  | zero => simp
  | succ n ih =>
    cases j with
    | zero =>
      have hr : rising 0 = fun _ : ℝ => 1 := by funext y; simp
      simp [hr, backward_const]
    | succ j =>
      rw [backward_from_first]
      have hb : backward (rising (j+1)) 1 = rising j := by
        funext y
        change rising (j+1) y - rising (j+1) (y-1) = rising j y
        exact rising_difference j y
      rw [hb, ih]
      simp only [Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub]

theorem backward_rising_at_zero (j n : ℕ) :
    backward (rising j) n 0 = if n=j then 1 else 0 := by
  rw [backward_rising]
  by_cases hnj : n=j
  · subst j
    simp
  · by_cases hn : n ≤ j
    · have hpos : 0 < j-n := by omega
      obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      simp [hn, hnj, hk]
    · simp [hn, hnj]

end ReflectedNewton
namespace ReflectedNewton
open Finset Polynomial

theorem backward_sub (f g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    backward (fun y => f y-g y) n x = backward f n x-backward g n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [backward, ih]; ring

theorem backward_const_mul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    backward (fun y => c*f y) n x = c*backward f n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [backward, ih]; ring

theorem backward_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (n : ℕ) (x : ℝ) :
    backward (fun y => ∑ i ∈ s, f i y) n x = ∑ i ∈ s, backward (f i) n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [backward, ih, Finset.sum_sub_distrib]

theorem backward_shift_argument (f : ℝ → ℝ) (u : ℝ) (n : ℕ) (x : ℝ) :
    backward (fun y => f (y-u)) n x = backward f n (x-u) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [backward, ih]
    congr 1
    congr 1
    ring

theorem backward_leading_coefficient (P : Polynomial ℝ) (u : ℝ) :
    backward P.eval P.natDegree u = P.leadingCoeff * (P.natDegree.factorial : ℝ) := by
  rw [backward_forward]
  have h := congrFun (P.fwdDiff_iter_degree_eq_factorial) (u-P.natDegree)
  simpa using h

theorem polynomial_zero_of_backward (P : Polynomial ℝ) (u : ℝ)
    (h : ∀ n, backward P.eval n u = 0) : P = 0 := by
  have hv := h P.natDegree
  rw [backward_leading_coefficient] at hv
  have hf : (P.natDegree.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero P.natDegree
  exact Polynomial.leadingCoeff_eq_zero.mp ((mul_eq_zero.mp hv).resolve_right hf)

theorem polynomial_eq_of_backward (P Q : Polynomial ℝ) (u : ℝ)
    (h : ∀ n, backward P.eval n u = backward Q.eval n u) : P = Q := by
  apply sub_eq_zero.mp
  apply polynomial_zero_of_backward (P-Q) u
  intro n
  have heval : (P-Q).eval = fun x => P.eval x-Q.eval x := by funext x; simp
  rw [heval, backward_sub, h n, sub_self]

noncomputable def risingPolynomial (j : ℕ) : Polynomial ℝ :=
  Ring.multichoose X j

@[simp] theorem risingPolynomial_eval (j : ℕ) (x : ℝ) :
    (risingPolynomial j).eval x = rising j x := by
  simpa [risingPolynomial, rising] using
    (Ring.map_multichoose (Polynomial.evalRingHom x) (X : Polynomial ℝ) j)

noncomputable def newtonPolynomial (P : Polynomial ℝ) (u : ℝ) : Polynomial ℝ :=
  ∑ j ∈ range (P.natDegree+1), C (backward P.eval j u) *
    (risingPolynomial j).comp (X-C u)

theorem newtonPolynomial_eval (P : Polynomial ℝ) (u : ℝ) :
    (newtonPolynomial P u).eval = fun x =>
      ∑ j ∈ range (P.natDegree+1), backward P.eval j u * rising j (x-u) := by
  funext x
  simp [newtonPolynomial, Polynomial.eval_finsetSum]

theorem backward_newtonPolynomial (P : Polynomial ℝ) (u : ℝ) (n : ℕ) :
    backward (newtonPolynomial P u).eval n u =
      if n < P.natDegree+1 then backward P.eval n u else 0 := by
  rw [newtonPolynomial_eval, backward_sum]
  simp only [backward_const_mul, backward_shift_argument, sub_self, backward_rising_at_zero]
  simp [mul_ite]

theorem backward_newton_expansion (P : Polynomial ℝ) (u : ℝ) : newtonPolynomial P u = P := by
  apply polynomial_eq_of_backward _ _ u
  intro n
  rw [backward_newtonPolynomial]
  split_ifs with hn
  · rfl
  · rw [backward_polynomial_vanish P (by omega)]

theorem backward_newton_formula (P : Polynomial ℝ) (u y : ℝ) :
    P.eval (u+y) = ∑ j ∈ range (P.natDegree+1), backward P.eval j u * rising j y := by
  have h := congrFun (newtonPolynomial_eval P u) (u+y)
  rw [backward_newton_expansion] at h
  simpa using h

end ReflectedNewton
namespace ReflectedNewton
open Finset

theorem weighted_shift_sum (d : ℕ → ℝ) (M s : ℕ) :
    (∑ i ∈ range M, (i+1 : ℝ)*d (s+i)) =
      ∑ j ∈ range (M+s), ((j+1-s : ℕ) : ℝ)*d j := by
  induction M with
  | zero =>
    simp only [range_zero, sum_empty, zero_add]
    symm
    apply sum_eq_zero
    intro j hj
    have hz : j+1-s=0 := by have := mem_range.mp hj; omega
    simp [hz]
  | succ M ih =>
    rw [sum_range_succ, ih]
    have hidx : M+1+s=(M+s)+1 := by omega
    rw [hidx, sum_range_succ]
    have hsub : M+s+1-s=M+1 := by omega
    simp only [hsub, Nat.cast_add, Nat.cast_one]
    rw [Nat.add_comm s M]

theorem weighted_shift_sum_truncated (d : ℕ → ℝ) (M s : ℕ)
    (hd : ∀ j, M ≤ j → d j = 0) :
    (∑ i ∈ range M, (i+1 : ℝ)*d (s+i)) =
      ∑ j ∈ range M, ((j+1-s : ℕ) : ℝ)*d j := by
  rw [weighted_shift_sum]
  symm
  apply sum_subset (range_mono (by omega : M ≤ M+s))
  intro j hj hnot
  have hM : M ≤ j := by simpa using hnot
  rw [hd j hM, mul_zero]

theorem backward_two_step_indexed (P : Polynomial ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hP : P.natDegree ≤ m-2) (s : ℕ) :
    backward P.eval s (m : ℝ) =
      ∑ j ∈ range (m-1), ((j+1-s : ℕ) : ℝ)*backward P.eval j ((m : ℝ)-2) := by
  have h := backward_double_shift P (m-2) hP ((m : ℝ)-2) s
  have hlen : m-2+1=m-1 := by omega
  simp only [sub_add_cancel, hlen] at h
  rw [h]
  apply weighted_shift_sum_truncated (fun j => backward P.eval j ((m : ℝ)-2)) (m-1) s
  intro j hj
  exact backward_polynomial_vanish P (by omega) _

noncomputable def reflectedCoefficient (P : Polynomial ℝ) (m k : ℕ) : ℝ :=
  P.eval (m : ℝ) - backward P.eval (k+1) (m : ℝ) - backward P.eval (m-1-k) (m : ℝ)

theorem reflected_coefficient_kernel (P : Polynomial ℝ) (m k : ℕ)
    (hm : 2 ≤ m) (hk : k ≤ m-2) (hP : P.natDegree ≤ m-2) :
    reflectedCoefficient P m k =
      ∑ j ∈ range (m-1), (kernel m k j : ℝ)*backward P.eval j ((m : ℝ)-2) := by
  change backward P.eval 0 (m : ℝ) - backward P.eval (k+1) (m : ℝ) -
    backward P.eval (m-1-k) (m : ℝ) = _
  rw [backward_two_step_indexed P m hm hP, backward_two_step_indexed P m hm hP,
      backward_two_step_indexed P m hm hP, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  rw [← sub_mul, ← sub_mul]
  congr 1
  have hj' : j ≤ m-2 := by have := mem_range.mp hj; omega
  have hint : ((j+1-0 : ℕ) : ℤ) - ((j+1-(k+1) : ℕ) : ℤ) -
      ((j+1-(m-1-k) : ℕ) : ℤ) = kernel m k j := by
    unfold kernel
    omega
  exact_mod_cast hint

end ReflectedNewton
namespace ReflectedNewton
open Finset Polynomial

noncomputable def reflectedLift (P : Polynomial ℝ) (m : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (m-1), C (reflectedCoefficient P m k) *
    (risingPolynomial (k+1)).comp (X-C (m : ℝ))

theorem reflectedLift_eval (P : Polynomial ℝ) (m : ℕ) :
    (reflectedLift P m).eval = fun x =>
      ∑ k ∈ range (m-1), reflectedCoefficient P m k * rising (k+1) (x-m) := by
  funext x
  simp [reflectedLift, Polynomial.eval_finsetSum]

theorem reflectedLift_at_center (P : Polynomial ℝ) (m : ℕ) :
    (reflectedLift P m).eval (m : ℝ) = 0 := by
  have h := congrFun (reflectedLift_eval P m) (m : ℝ)
  simpa using h

theorem reflectedLift_coefficient (P : Polynomial ℝ) (m k : ℕ) (hk : k < m-1) :
    backward (reflectedLift P m).eval (k+1) (m : ℝ) = reflectedCoefficient P m k := by
  rw [reflectedLift_eval, backward_sum]
  simp only [backward_const_mul, backward_shift_argument, sub_self, backward_rising_at_zero]
  simp [mul_ite, hk]

theorem reflectedLift_kernel (P : Polynomial ℝ) (m k : ℕ)
    (hm : 2 ≤ m) (hk : k ≤ m-2) (hP : P.natDegree ≤ m-2) :
    backward (reflectedLift P m).eval (k+1) (m : ℝ) =
      ∑ j ∈ range (m-1), (kernel m k j : ℝ)*backward P.eval j ((m : ℝ)-2) := by
  rw [reflectedLift_coefficient P m k (by omega)]
  exact reflected_coefficient_kernel P m k hm hk hP

theorem reflectedCoefficient_symmetry (P : Polynomial ℝ) (m k : ℕ)
    (hm : 2 ≤ m) (hk : k ≤ m-2) :
    reflectedCoefficient P m k = reflectedCoefficient P m (m-2-k) := by
  have h1 : m-2-k+1=m-1-k := by omega
  have h2 : m-1-(m-2-k)=k+1 := by omega
  simp only [reflectedCoefficient, h1, h2]
  ring

end ReflectedNewton
namespace ReflectedNewton
open Finset Polynomial

theorem risingPolynomial_factorial (j : ℕ) :
    C (j.factorial : ℝ)*risingPolynomial j=ascPochhammer ℝ j := by
  apply Polynomial.funext
  intro x
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer x j
  rw [Polynomial.ascPochhammer_smeval_eq_eval] at h
  simpa only [eval_mul,eval_C,risingPolynomial_eval,rising,nsmul_eq_mul] using h

theorem risingPolynomial_natDegree (j : ℕ) : (risingPolynomial j).natDegree=j := by
  have h := congrArg Polynomial.natDegree (risingPolynomial_factorial j)
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  simpa only [natDegree_C_mul hf,ascPochhammer_natDegree] using h

end ReflectedNewton
namespace ReflectedNewton
open Finset Polynomial

theorem backward_rising_shift (v n : ℕ) (u : ℝ) :
    backward (risingPolynomial v).eval n u=if n ≤ v then rising (v-n) u else 0 := by
  have hf : (risingPolynomial v).eval=rising v := by funext x; exact risingPolynomial_eval v x
  rw [hf,backward_rising]

theorem backward_rising_at_two (v n : ℕ) :
    backward (risingPolynomial v).eval n 2=((v+1-n : ℕ) : ℝ) := by
  rw [backward_rising_shift]
  by_cases hn : n ≤ v
  · rw [ite_eq_left hn]
    have ht := Ring.multichoose_two (R := ℝ) (v-n)
    change rising (v-n) 2=(v-n : ℕ)+1 at ht
    rw [ht]
    have heq : v-n+1=v+1-n := by omega
    exact_mod_cast heq
  · rw [ite_eq_right hn]
    have hz : v+1-n=0 := by omega
    simp [hz]

theorem rising_shift_two (v : ℕ) (y : ℝ) :
    rising v (y+2)=∑ j ∈ range (v+1), ((v+1-j : ℕ) : ℝ)*rising j y := by
  have hn := backward_newton_formula (risingPolynomial v) 2 y
  rw [risingPolynomial_eval,risingPolynomial_natDegree] at hn
  simp_rw [backward_rising_at_two] at hn
  simpa only [add_comm y 2] using hn

theorem choose_in_rising_basis (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    Ring.choose x (m-1)=∑ j ∈ range m, ((m-j : ℕ) : ℝ)*rising j (x-m) := by
  have hr := rising_shift_two (m-1) (x-m)
  have hlen : m-1+1=m := by omega
  have harg : x-(m : ℝ)+2+((m-1 : ℕ) : ℝ)-1=x := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring
  rw [rising_literal,harg,hlen] at hr
  exact hr

theorem constant_two_rising_coefficient (m j : ℕ) (hm : 2 ≤ m) (hj : j < m) :
    backward (fun x : ℝ => Ring.choose x (m-1)) j (m : ℝ)=((m-j : ℕ) : ℝ) := by
  have heval : (fun x : ℝ => Ring.choose x (m-1))=
      fun x => ∑ i ∈ range m, ((m-i : ℕ) : ℝ)*rising i (x-m) := by
    funext x
    exact choose_in_rising_basis m hm x
  rw [heval,backward_sum]
  simp only [backward_const_mul,backward_shift_argument,sub_self,backward_rising_at_zero]
  simp [mul_ite,hj]

end ReflectedNewton
namespace ReflectedNewton
open Finset Polynomial

theorem backward_add (f g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    backward (fun y => f y+g y) n x=backward f n x+backward g n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [backward,ih]; ring

end ReflectedNewton
namespace ReflectedNewton
open Finset Polynomial

theorem backward_segment (f : ℝ → ℝ) (u : ℝ) (j L : ℕ) :
    (∑ t ∈ range L, backward f (j+t) u)=backward f j (u+1)-backward f (j+L) (u+1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ,ih,backward_step f (j+L) u]
    have heq : j+(L+1)=j+L+1 := by omega
    rw [heq]
    ring

theorem backward_reversed_segment (f : ℝ → ℝ) (u : ℝ) (L : ℕ) :
    (∑ t ∈ range L, backward f (L-t) u)=backward f 1 (u+1)-backward f (L+1) (u+1) := by
  have heq : (∑ t ∈ range L, backward f (L-t) u)=
      ∑ t ∈ range L, backward f (1+t) u := by
    calc
      _ = ∑ t ∈ range L, backward f (1+(L-1-t)) u := by
        apply sum_congr rfl
        intro t ht
        congr 1
        have := mem_range.mp ht
        omega
      _ = _ := sum_range_reflect (fun t => backward f (1+t) u) L
  rw [heq,backward_segment]
  congr 1
  congr 1
  omega

theorem lift_coefficient_tail (P : Polynomial ℝ) (m j : ℕ)
    (hm : 3 ≤ m) (hj : 1 ≤ j ∧ j ≤ m-1) (hP : P.natDegree ≤ m-3) :
    (∑ t ∈ range (m-1-j), reflectedCoefficient P (m-1) (j-1+t)) =
      ((m-1-j : ℕ) : ℝ)*P.eval ((m : ℝ)-1)-backward P.eval j (m : ℝ)-
      backward P.eval 1 (m : ℝ)+backward P.eval (m-j) (m : ℝ) := by
  have hc : ((m-1 : ℕ) : ℝ)=(m : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have heq : ∀ t ∈ range (m-1-j), reflectedCoefficient P (m-1) (j-1+t)=
      P.eval ((m : ℝ)-1)-backward P.eval (j+t) ((m : ℝ)-1)-
      backward P.eval ((m-1-j)-t) ((m : ℝ)-1) := by
    intro t ht
    have ht' := mem_range.mp ht
    have hi1 : j-1+t+1=j+t := by omega
    have hi2 : m-1-1-(j-1+t)=m-1-j-t := by omega
    simp only [reflectedCoefficient,hc,hi1,hi2]
  rw [sum_congr rfl heq]
  simp only [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
  rw [backward_segment,backward_reversed_segment]
  have hx : (m : ℝ)-1+1=m := by ring
  have hidx : j+(m-1-j)=m-1 := by omega
  have hidx2 : m-1-j+1=m-j := by omega
  rw [hx,hidx,hidx2,backward_polynomial_vanish P (n := m-1) (by omega)]
  ring

theorem finite_suffix_sum (f : ℕ → ℝ) (M s : ℕ) (hs : s ≤ M) :
    (∑ k ∈ range M, if s ≤ k then f k else 0)=∑ t ∈ range (M-s), f (s+t) := by
  have hlen : s+(M-s)=M := by omega
  conv_lhs => rw [← hlen,Finset.sum_range_add]
  have hzero : (∑ k ∈ range s, if s ≤ k then f k else 0)=0 := by
    apply sum_eq_zero
    intro k hk
    rw [ite_eq_right (by have := mem_range.mp hk; omega)]
  rw [hzero,zero_add]
  apply sum_congr rfl
  intro t ht
  rw [ite_eq_left (by omega)]

theorem backward_lift_above_center (P : Polynomial ℝ) (m j : ℕ) (hm : 3 ≤ m) :
    backward (reflectedLift P (m-1)).eval j (m : ℝ)=
      ∑ k ∈ range (m-2), if j ≤ k+1 then reflectedCoefficient P (m-1) k else 0 := by
  rw [reflectedLift_eval,backward_sum]
  have hlen : m-1-1=m-2 := by omega
  rw [hlen]
  apply sum_congr rfl
  intro k hk
  rw [backward_const_mul,backward_shift_argument]
  have hx : (m : ℝ)-((m-1 : ℕ) : ℝ)=1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring
  rw [hx,backward_rising]
  by_cases hj : j ≤ k+1
  · rw [ite_eq_left hj,ite_eq_left hj]
    have hone : rising (k+1-j) 1=1 := Ring.multichoose_one _
    rw [hone,mul_one]
  · rw [ite_eq_right hj,ite_eq_right hj,mul_zero]

theorem backward_previous_lift_positive (P : Polynomial ℝ) (m j : ℕ)
    (hm : 3 ≤ m) (hj : 1 ≤ j ∧ j ≤ m-1) (hP : P.natDegree ≤ m-3) :
    backward (reflectedLift P (m-1)).eval j (m : ℝ)=
      ((m-1-j : ℕ) : ℝ)*P.eval ((m : ℝ)-1)-backward P.eval j (m : ℝ)-
      backward P.eval 1 (m : ℝ)+backward P.eval (m-j) (m : ℝ) := by
  rw [backward_lift_above_center P m j hm]
  have heq : ∀ k, (j ≤ k+1) ↔ (j-1 ≤ k) := by intro k; omega
  simp_rw [heq]
  rw [finite_suffix_sum _ _ _ (by omega)]
  have hlen : m-2-(j-1)=m-1-j := by omega
  rw [hlen]
  exact lift_coefficient_tail P m j hm hj hP

theorem backward_previous_lift_zero (P : Polynomial ℝ) (m : ℕ)
    (hm : 3 ≤ m) (hP : P.natDegree ≤ m-3) :
    (reflectedLift P (m-1)).eval (m : ℝ)=
      ((m-2 : ℕ) : ℝ)*P.eval ((m : ℝ)-1)-2*backward P.eval 1 (m : ℝ) := by
  have hz := backward_lift_above_center P m 0 hm
  simp only [Nat.zero_le,ite_true,backward_zero] at hz
  have ht := lift_coefficient_tail P m 1 hm ⟨by omega,by omega⟩ hP
  have hlen : m-1-1=m-2 := by omega
  simp only [Nat.sub_self,Nat.zero_add,hlen] at ht
  rw [backward_polynomial_vanish P (n := m-1) (by omega)] at ht
  rw [hz,ht]
  ring

end ReflectedNewton

end PermutationPeaks
