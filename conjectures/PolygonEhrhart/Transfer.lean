module

public import conjectures.PolygonEhrhart.Counts
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Interval.Finset.Fin

@[expose] public section
namespace PolygonEhrhart
open Finset Matrix

def kernel (w : ℕ) : Matrix (Fin (w+1)) (Fin (w+1)) ℕ :=
  fun i j ↦ w+1-max i.val j.val

theorem edge_choices {w : ℕ} (i j : Fin (w+1)) :
    (∑ z : Fin (w+1), if i≤z ∧ j≤z then 1 else 0) = kernel w i j := by
  rw [sum_boole]
  have eq : univ.filter (fun z : Fin (w+1) ↦ i≤z ∧ j≤z) = Icc (max i j) (Fin.last w) := by
    ext z;simp [max_le_iff,Fin.le_last]
  rw [eq,Fin.card_Icc]
  rfl

private theorem crown_weights (n w : ℕ) :
    crownCount n w = ∑ v : Fin n → Fin (w+1), ∏ i,kernel w (v i) (v (next i)) := by
  classical
  unfold crownCount
  apply sum_congr rfl;intro v _
  simp_rw [← edge_choices,Fintype.prod_sum,Fintype.prod_boole]
  apply sum_congr rfl;intro e _
  by_cases h : crownValid v e
  · rw [ite_eq_left h,ite_eq_left (show ∀ i,v i≤e i ∧ v (next i)≤e i from h)]
  · rw [ite_eq_right h,ite_eq_right (show ¬∀ i,v i≤e i ∧ v (next i)≤e i from h)]

private theorem sum_cons {V : Type*} [Fintype V] (k : ℕ) (f : (Fin (k+1) → V) → ℕ) :
    ∑ v,f v = ∑ x,∑ p : Fin k → V, f (Fin.cons x p) := by
  simpa [Fin.consEquiv,Fintype.sum_prod_type] using ((Fin.consEquiv (fun _ ↦ V)).sum_comp f).symm

private def chain {V : Type*} (M : Matrix V V ℕ) :
    (k : ℕ) → V → (Fin k → V) → V → ℕ
  | 0,x,_,y => M x y
  | k+1,x,f,y => M x (f 0) * chain M k (f 0) (fun i ↦ f i.succ) y

private theorem chain_sum {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ)
    (k : ℕ) (x y : V) : ∑ p : Fin k → V, chain M k x p y = (M^(k+1)) x y := by
  induction k generalizing x with
  | zero => simp [chain]
  | succ k ih =>
    rw [sum_cons,pow_succ' M (k+1),Matrix.mul_apply]
    simp only [chain,Fin.cons_zero,Fin.cons_succ,←mul_sum,ih]

/-- Sum over the starting vertex height to close the walk around the polygon. -/
theorem crown_thirteen (w : ℕ) : crownCount 13 w = ((kernel w)^13).trace := by
  rw [crown_weights,sum_cons]
  apply sum_congr rfl
  intro x _
  calc
    _ = ∑ p : Fin 12 → Fin (w+1), chain (kernel w) 12 x p x := by
      apply sum_congr rfl
      intro p _
      simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
      rfl
    _ = _ := chain_sum _ 12 x x

end PolygonEhrhart
