module

public import conjectures.SavchenkoSix.Minors
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
namespace SavchenkoSix
open Matrix

def pf4 {V : Type*} (M : V→V→ℤ) (a b c d : V) : ℤ :=
  M a b*M c d-M a c*M b d+M a d*M b c

def pf6 {V : Type*} (M : V→V→ℤ) (a b c d e f : V) : ℤ :=
  M a b*pf4 M c d e f-M a c*pf4 M b d e f+M a d*pf4 M b c e f
    -M a e*pf4 M b c d f+M a f*pf4 M b c d e

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
theorem det_skew4 (M : Matrix (Fin 4) (Fin 4) ℤ) (anti : ∀ i j,M j i= -M i j) :
    M.det=(pf4 M 0 1 2 3)^2 := by
  let B : Matrix (Fin 4) (Fin 4) ℤ := fun i j ↦
    if i=0 then if j=0 then 0 else if j=1 then M 0 1 else if j=2 then M 0 2 else M 0 3 else
    if i=1 then if j=0 then (-M 0 1) else if j=1 then 0 else if j=2 then M 1 2 else M 1 3 else
    if i=2 then if j=0 then (-M 0 2) else if j=1 then (-M 1 2) else if j=2 then 0 else M 2 3 else
    if j=0 then (-M 0 3) else if j=1 then (-M 1 3) else if j=2 then (-M 2 3) else 0
  have zero (i : Fin 4) : M i i=0 := by have h := anti i i; omega
  have eq : M=B := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact zero _ | exact anti _ _
  calc
    M.det=B.det := congrArg Matrix.det eq
    _ = _ := by
      simp only [Matrix.det_succ_row_zero (n:=3),Matrix.det_fin_three,
        Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.submatrix_apply,Fin.val_zero,Fin.val_succ,
        pow_zero,pow_succ,add_zero,pf4]
      simp (config := {maxSteps := 1200000}) (disch := decide) only [B,ite_eq_left,ite_eq_right]
      ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
theorem det_skew6 (M : Matrix (Fin 6) (Fin 6) ℤ) (anti : ∀ i j,M j i= -M i j) :
    M.det=(pf6 M 0 1 2 3 4 5)^2 := by
  let B : Matrix (Fin 6) (Fin 6) ℤ := fun i j ↦
    if i=0 then if j=0 then 0 else if j=1 then M 0 1 else if j=2 then M 0 2 else if j=3 then M 0 3 else if j=4 then M 0 4 else M 0 5 else
    if i=1 then if j=0 then (-M 0 1) else if j=1 then 0 else if j=2 then M 1 2 else if j=3 then M 1 3 else if j=4 then M 1 4 else M 1 5 else
    if i=2 then if j=0 then (-M 0 2) else if j=1 then (-M 1 2) else if j=2 then 0 else if j=3 then M 2 3 else if j=4 then M 2 4 else M 2 5 else
    if i=3 then if j=0 then (-M 0 3) else if j=1 then (-M 1 3) else if j=2 then (-M 2 3) else if j=3 then 0 else if j=4 then M 3 4 else M 3 5 else
    if i=4 then if j=0 then (-M 0 4) else if j=1 then (-M 1 4) else if j=2 then (-M 2 4) else if j=3 then (-M 3 4) else if j=4 then 0 else M 4 5 else
    if j=0 then (-M 0 5) else if j=1 then (-M 1 5) else if j=2 then (-M 2 5) else if j=3 then (-M 3 5) else if j=4 then (-M 4 5) else 0
  have zero (i : Fin 6) : M i i=0 := by have h := anti i i; omega
  have eq : M=B := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact zero _ | exact anti _ _
  calc
    M.det=B.det := congrArg Matrix.det eq
    _ = _ := by
      simp only [Matrix.det_succ_row_zero (n:=5),Matrix.det_succ_row_zero (n:=4),Matrix.det_succ_row_zero (n:=3),Matrix.det_fin_three,
        Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.submatrix_apply,Fin.val_zero,Fin.val_succ,
        pow_zero,pow_succ,add_zero,pf6,pf4]
      simp (config := {maxSteps := 1200000}) (disch := decide) only [B,ite_eq_left,ite_eq_right]
      ring

end SavchenkoSix
