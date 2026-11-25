module

public import conjectures.GallianRusinDice.Statement
import Mathlib.Tactic.Ring

@[expose] public section
namespace GallianRusinDice
open Polynomial Finset

noncomputable def polynomial : List ℤ → ℤ[X]
  | [] => 0
  | a::s => C a+X*polynomial s

def plus : List ℤ → List ℤ → List ℤ
  | [],v => v
  | v,[] => v
  | a::v,b::w => (a+b)::plus v w

def times : List ℤ → List ℤ → List ℤ
  | [],_ => []
  | a::s,t => plus (t.map (a*·)) (0::times s t)

def power (s : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | k+1 => times (power s k) s

theorem polynomial_add (s t : List ℤ) : polynomial (plus s t)=polynomial s+polynomial t := by
  induction s generalizing t with
  | nil => simp [plus,polynomial]
  | cons a s ih =>
    cases t with
    | nil => simp [plus,polynomial]
    | cons b t => simp [plus,polynomial,ih]; ring

theorem polynomial_scale (s : List ℤ) (a : ℤ) : polynomial (s.map (a*·))=C a*polynomial s := by
  induction s with
  | nil => simp [polynomial]
  | cons b s ih => simp [polynomial,ih]; ring

theorem polynomial_mul (s t : List ℤ) : polynomial (times s t)=polynomial s*polynomial t := by
  induction s with
  | nil => simp [times,polynomial]
  | cons a s ih => simp [times,polynomial_add,polynomial,polynomial_scale,ih]; ring

theorem polynomial_power (s : List ℤ) (k : ℕ) : polynomial (power s k)=polynomial s^k := by
  induction k with
  | zero => simp [polynomial,power]
  | succ k ih => rw [power,polynomial_mul,ih,pow_succ]

@[simp] theorem coefficient (s : List ℤ) (j : ℕ) : (polynomial s).coeff j=s[j]?.getD 0 := by
  induction s generalizing j with
  | nil => simp [polynomial]
  | cons a s ih =>
    cases j with
    | zero => simp [polynomial]
    | succ j =>
      simp [polynomial,ih,coeff_X_mul]
      exact coeff_C_of_ne_zero (Nat.succ_ne_zero _)

theorem polynomial_standard (m : ℕ) : polynomial (List.replicate m 1)=standard m := by
  induction m with
  | zero => simp [standard,polynomial]
  | succ m ih =>
    rw [List.replicate_succ,polynomial,ih]
    simp only [standard,sum_range_succ',C_1,pow_zero]
    rw [mul_sum]
    simp [pow_succ',add_comm]

end GallianRusinDice
