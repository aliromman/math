module

public import conjectures.ConsecutiveThreshold.TiltLaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section
namespace ConsecutiveThreshold
open Finset
open scoped BigOperators

/-- Two adjacent equal, positive masses of a log-concave law attain its maximum. -/
private theorem plateau {w : ℤ → ℝ} {a : ℤ} (lc : Mass.balanced w)
    (peak : 0<w a) (tie : w a=w (a+1)) : ∀ i,w i≤w a := by
  have up (i : ℤ) (hi : i≤a) : w i≤w (i+1) := by
    have h := lc i a 1 hi (by decide)
    rw [←tie] at h
    exact (mul_le_mul_iff_of_pos_right peak).mp h
  have down (i : ℤ) (hi : a≤i) : w (i+1)≤w i := by
    have h := lc a i 1 hi (by decide)
    rw [←tie] at h
    exact (mul_le_mul_iff_of_pos_left peak).mp h
  have left (t : ℕ) : w (a-t)≤w a := by
    induction t with
    | zero => simp
    | succ t ih =>
      have e := up (a-(t+1:ℕ)) (by omega)
      rw [show a-((t+1:ℕ):ℤ)+1 = a-t by omega] at e
      exact e.trans ih
  have right (t : ℕ) : w (a+t)≤w a := by
    induction t with
    | zero => simp
    | succ t ih => simpa only [Nat.cast_add,Nat.cast_one,←add_assoc] using (down (a+t) (by omega)).trans ih
  intro i
  by_cases h : i≤a
  · simpa only [show a-((a-i).toNat:ℤ)=i by omega] using left (a-i).toNat
  · simpa only [show a+((i-a).toNat:ℤ)=i by omega] using right (i-a).toNat

/-- An exponential tilt can put any prescribed lower-half layer at the mode.
The shift bound controls how small the required parameter can be. -/
theorem modal_choice (F : ℝ → Series) (A : ℕ → ℝ) (n N m : ℕ)
    (large : 2≤N) (lower : 2*m≤N)
    (pos : ∀ i≤N,0<A i) (symm : ∀ i≤N,A (N-i)=A i)
    (cut : ∀ i : ℕ,((i:ℝ)+1)*A (i+1)≤((i:ℝ)+n)*A i)
    (coeff : ∀ q : ℝ, ∀ j : ℕ,(F q).coeff (j:ℤ)=q^j*A j)
    (balance : ∀ q : ℝ,0≤q → Mass.balanced (F q).coeff) :
    ∃ q : ℝ,0<q ∧ q≤1 ∧ (m:ℝ)/(m+n)≤q ∧ ∀ i : ℤ,(F q).coeff i≤(F q).coeff m := by
  have choose (a : ℕ) (low : 2*(a+1)≤N) : ∃ q : ℝ,0<q ∧ q≤1 ∧
      ((a:ℝ)+1)/(a+1+n)≤q ∧ (F q).coeff a=(F q).coeff ((a+1:ℕ):ℤ) ∧
      ∀ i : ℤ,(F q).coeff i≤(F q).coeff (a:ℤ) := by
    have pa := pos a (by omega)
    have pb := pos (a+1) (by omega)
    have order : A a≤A (a+1) := by
      have e := balance 1 (by norm_num) (a:ℤ) (N-(a+1):ℕ) 1 (by omega) (by decide)
      rw [show ((N-(a+1):ℕ):ℤ)+1=((N-a:ℕ):ℤ) by omega,
          show (a:ℤ)+1=((a+1:ℕ):ℤ) by omega] at e
      simp only [coeff,one_pow,one_mul,symm a (by omega),symm (a+1) (by omega)] at e
      nlinarith only [e,pa,pb]
    let q := A a/A (a+1)
    have pq : 0<q := div_pos pa pb
    have bound : ((a:ℝ)+1)/(a+1+n)≤q := by
      apply (div_le_div_iff₀ (by positivity) pb).mpr
      nlinarith only [cut a,pa]
    have tie : (F q).coeff (a:ℤ)=(F q).coeff ((a+1:ℕ):ℤ) := by
      rw [coeff,coeff,pow_succ]
      dsimp only [q]
      field_simp
    refine ⟨q,pq,(div_le_one pb).mpr order,bound,tie,?_⟩
    apply plateau (balance q pq.le)
    · rw [coeff]
      exact mul_pos (pow_pos pq _) pa
    · simpa only [Nat.cast_add,Nat.cast_one] using tie
  cases m with
  | zero =>
    obtain ⟨q,pq,uq,_,_,h⟩ := choose 0 (by omega)
    exact ⟨q,pq,uq,by simp [pq.le],by simpa using h⟩
  | succ a =>
    obtain ⟨q,pq,uq,b,tie,h⟩ := choose a lower
    refine ⟨q,pq,uq,by simpa using b,?_⟩
    exact fun i ↦ (h i).trans_eq tie

end ConsecutiveThreshold
