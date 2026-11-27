module

public import conjectures.KarlovskySumBound.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

@[expose] public section
namespace KarlovskySumBound
open Finset
open scoped BigOperators

def tri (k : ℕ) := ∑ i : Fin k, (i.val+1)

theorem tri_twice (k : ℕ) : 2*tri k=k*(k+1) := by
  induction k with
  | zero => simp [tri]
  | succ k ih =>
    have eq : tri (k+1)=tri k+(k+1) := by
      simp [tri,Fin.sum_univ_castSucc]
    rw [eq]
    nlinarith only [ih]

/-- For k increasing entries, the product grows at least k! / k times
    as fast as their sum moves above the sum of 1 through k. -/
theorem prefix_growth (k : ℕ) (x : Fin k → ℕ) (low : ∀ i, i.val+1 ≤ x i) :
    ∃ E G : ℕ, (∑ i,x i)=tri k+E ∧ (∏ i,x i)=k.factorial+G ∧
      k.factorial*E ≤ k*G := by
  induction k with
  | zero => exact ⟨0,0,by simp [tri],by simp,by simp⟩
  | succ k ih =>
    obtain ⟨E,G,hs,hp,le⟩ := ih (fun i => x i.castSucc) (fun i => low i.castSucc)
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (low (Fin.last k))
    change x (Fin.last k) = k+1+d at hd
    refine ⟨E+d, G*(k+1)+(k.factorial+G)*d, ?_, ?_, ?_⟩
    · rw [Fin.sum_univ_castSucc,hs,hd]
      simp only [tri,Fin.sum_univ_castSucc (fun i : Fin (k+1) => i.val+1),Fin.val_castSucc,
        Fin.val_last]
      omega
    · rw [Fin.prod_univ_castSucc,hp,hd,Nat.factorial_succ]
      ring
    · rw [Nat.factorial_succ]
      have t := Nat.mul_le_mul_left (k+1) le
      nlinarith only [t,Nat.zero_le (G*d*(k+1)),Nat.zero_le (G*(k+1))]

theorem rank_lower {n : ℕ} {x : Fin n → ℕ} (pos : ∀ i,0<x i) (inc : StrictMono x)
    (i : Fin n) : i.val+1 ≤ x i := by
  obtain ⟨j,hj⟩ := i
  induction j with
  | zero => exact pos ⟨0,hj⟩
  | succ j ih =>
    have h := inc (show (⟨j,by omega⟩ : Fin n) < ⟨j+1,hj⟩ from Nat.lt_succ_self _)
    exact (ih (by omega)).trans_lt h

end KarlovskySumBound
