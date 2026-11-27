module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace ChipShadow
open Finset

def unitCoord (n k : ℕ) : ℚ := if k+1=n then 1 else 0

/-- Principal-part coordinates for the two neighboring knots with multiplicities a and b. -/
def corner : ℕ → ℕ → ℕ → ℚ
  | 0,b,k => unitCoord b k
  | a+1,0,k => unitCoord (a+1) k
  | a+1,b+1,k => corner a (b+1) k - corner (a+1) b k
termination_by a b _ => a+b

private theorem high (a b k : ℕ) (h : a+b<k+1) : corner a b k=0 := by
  cases a with
  | zero => simp [corner,unitCoord,show k+1≠b by omega]
  | succ a =>
    cases b with
    | zero => simp [corner,unitCoord,show k≠a by omega]
    | succ b =>
      rw [corner,high a (b+1) k (by omega),high (a+1) b k (by omega),sub_zero]
termination_by a+b

def diagonal (m k : ℕ) (p : ℕ → ℚ) : ℚ :=
  ∑ i ∈ range m,p i*corner (i+1) (m-i) k

private theorem recursive (m k : ℕ) (p : ℕ → ℚ) :
    diagonal (m+1) k p=(p 0-p m)*unitCoord (m+1) k+
      diagonal m k (fun i ↦ p (i+1)-p i) := by
  unfold diagonal
  have step (i : ℕ) (hi : i∈range (m+1)) :
      p i*corner (i+1) (m+1-i) k=p i*corner i (m+1-i) k-p i*corner (i+1) (m-i) k := by
    have eq : m+1-i=m-i+1 := by have := mem_range.mp hi;omega
    rw [eq,corner,mul_sub]
  rw [sum_congr rfl step,sum_sub_distrib,
    sum_range_succ' (fun i ↦ p i*corner i (m+1-i) k),
    sum_range_succ (fun i ↦ p i*corner (i+1) (m-i) k)]
  simp only [Nat.add_sub_add_right,Nat.sub_zero,Nat.sub_self,corner,sub_mul,sum_sub_distrib]
  ring

private theorem diagonal_high (m : ℕ) (p : ℕ → ℚ) : diagonal m m p=0 := by
  apply sum_eq_zero;intro i hi
  have lt := mem_range.mp hi
  cases h : m-i with
  | zero => omega
  | succ b => rw [corner,high i (b+1) m (by omega),high (i+1) b m (by omega)];simp

/-- The only zero combination along a diagonal has constant coefficients. -/
theorem diagonal_constant (m : ℕ) (p : ℕ → ℚ) (h : ∀ k,diagonal m k p=0) :
    ∀ i<m,p i=p 0 := by
  induction m generalizing p with
  | zero => omega
  | succ m ih =>
    let d (i : ℕ) := p (i+1)-p i
    have top := h m
    rw [recursive,diagonal_high] at top
    simp [unitCoord] at top
    have ends := sub_eq_zero.mp top
    have van (k : ℕ) : diagonal m k d=0 := by
      have a := h k
      rw [recursive,top,zero_mul,zero_add] at a
      exact a
    have diff := ih d van
    have seq (i : ℕ) (hi : i≤m) : p i = p 0 + i*d 0 := by
      induction i with
      | zero => simp
      | succ i hprev =>
        have e := diff i (by omega)
        change p (i+1)-p i=d 0 at e
        rw [hprev (by omega)] at e
        push_cast
        linarith
    intro i hi
    by_cases hm : m=0
    · have zi : i=0 := by omega
      simp [zi]
    · have e := seq m (Nat.le_refl _)
      rw [←ends] at e
      have z : (m:ℚ)*d 0=0 := by linarith
      have dz : d 0=0 := (mul_eq_zero.mp z).resolve_left (by exact_mod_cast hm)
      rw [seq i (by omega),dz,mul_zero,add_zero]

end ChipShadow
