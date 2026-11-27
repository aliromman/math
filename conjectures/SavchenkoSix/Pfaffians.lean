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

private def minor3 {V : Type*} (M : Matrix V V ℤ) (r0 r1 r2 c0 c1 c2 : V) : ℤ :=
  M r0 c0*M r1 c1*M r2 c2+M r0 c1*M r1 c2*M r2 c0+M r0 c2*M r1 c0*M r2 c1
    -M r0 c2*M r1 c1*M r2 c0-M r0 c1*M r1 c0*M r2 c2-M r0 c0*M r1 c2*M r2 c1

private theorem expand3 {V : Type*} (M : Matrix V V ℤ) (r c : Fin 3 → V) :
    (M.submatrix r c).det=minor3 M (r 0) (r 1) (r 2) (c 0) (c 1) (c 2) := by
  simp only [Matrix.det_fin_three,Matrix.submatrix_apply,minor3]
  ring

private def minor4 {V : Type*} (M : Matrix V V ℤ) (r0 r1 r2 r3 c0 c1 c2 c3 : V) : ℤ :=
  M r0 c0*minor3 M r1 r2 r3 c1 c2 c3
    -M r0 c1*minor3 M r1 r2 r3 c0 c2 c3
    +M r0 c2*minor3 M r1 r2 r3 c0 c1 c3
    -M r0 c3*minor3 M r1 r2 r3 c0 c1 c2

private theorem expand4 {V : Type*} (M : Matrix V V ℤ) (r c : Fin 4 → V) :
    (M.submatrix r c).det=minor4 M (r 0) (r 1) (r 2) (r 3) (c 0) (c 1) (c 2) (c 3) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.submatrix_submatrix,expand3,Matrix.submatrix_apply]
  change (-1:ℤ)^0*M (r 0) (c 0)*minor3 M (r 1) (r 2) (r 3) (c 1) (c 2) (c 3) +
    ((-1:ℤ)^1*M (r 0) (c 1)*minor3 M (r 1) (r 2) (r 3) (c 0) (c 2) (c 3) +
    ((-1:ℤ)^2*M (r 0) (c 2)*minor3 M (r 1) (r 2) (r 3) (c 0) (c 1) (c 3) +
    ((-1:ℤ)^3*M (r 0) (c 3)*minor3 M (r 1) (r 2) (r 3) (c 0) (c 1) (c 2)))) = _
  unfold minor4;ring

private def minor5 {V : Type*} (M : Matrix V V ℤ) (r0 r1 r2 r3 r4 c0 c1 c2 c3 c4 : V) : ℤ :=
  M r0 c0*minor4 M r1 r2 r3 r4 c1 c2 c3 c4
    -M r0 c1*minor4 M r1 r2 r3 r4 c0 c2 c3 c4
    +M r0 c2*minor4 M r1 r2 r3 r4 c0 c1 c3 c4
    -M r0 c3*minor4 M r1 r2 r3 r4 c0 c1 c2 c4
    +M r0 c4*minor4 M r1 r2 r3 r4 c0 c1 c2 c3

private theorem expand5 {V : Type*} (M : Matrix V V ℤ) (r c : Fin 5 → V) :
    (M.submatrix r c).det=minor5 M (r 0) (r 1) (r 2) (r 3) (r 4) (c 0) (c 1) (c 2) (c 3) (c 4) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.submatrix_submatrix,expand4,Matrix.submatrix_apply]
  change (-1:ℤ)^0*M (r 0) (c 0)*minor4 M (r 1) (r 2) (r 3) (r 4) (c 1) (c 2) (c 3) (c 4) +
    ((-1:ℤ)^1*M (r 0) (c 1)*minor4 M (r 1) (r 2) (r 3) (r 4) (c 0) (c 2) (c 3) (c 4) +
    ((-1:ℤ)^2*M (r 0) (c 2)*minor4 M (r 1) (r 2) (r 3) (r 4) (c 0) (c 1) (c 3) (c 4) +
    ((-1:ℤ)^3*M (r 0) (c 3)*minor4 M (r 1) (r 2) (r 3) (r 4) (c 0) (c 1) (c 2) (c 4) +
    ((-1:ℤ)^4*M (r 0) (c 4)*minor4 M (r 1) (r 2) (r 3) (r 4) (c 0) (c 1) (c 2) (c 3))))) = _
  unfold minor5;ring

private def minor6 {V : Type*} (M : Matrix V V ℤ) (r0 r1 r2 r3 r4 r5 c0 c1 c2 c3 c4 c5 : V) : ℤ :=
  M r0 c0*minor5 M r1 r2 r3 r4 r5 c1 c2 c3 c4 c5
    -M r0 c1*minor5 M r1 r2 r3 r4 r5 c0 c2 c3 c4 c5
    +M r0 c2*minor5 M r1 r2 r3 r4 r5 c0 c1 c3 c4 c5
    -M r0 c3*minor5 M r1 r2 r3 r4 r5 c0 c1 c2 c4 c5
    +M r0 c4*minor5 M r1 r2 r3 r4 r5 c0 c1 c2 c3 c5
    -M r0 c5*minor5 M r1 r2 r3 r4 r5 c0 c1 c2 c3 c4

private theorem expand6 {V : Type*} (M : Matrix V V ℤ) (r c : Fin 6 → V) :
    (M.submatrix r c).det=minor6 M (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.submatrix_submatrix,expand5,Matrix.submatrix_apply]
  change (-1:ℤ)^0*M (r 0) (c 0)*minor5 M (r 1) (r 2) (r 3) (r 4) (r 5) (c 1) (c 2) (c 3) (c 4) (c 5) +
    ((-1:ℤ)^1*M (r 0) (c 1)*minor5 M (r 1) (r 2) (r 3) (r 4) (r 5) (c 0) (c 2) (c 3) (c 4) (c 5) +
    ((-1:ℤ)^2*M (r 0) (c 2)*minor5 M (r 1) (r 2) (r 3) (r 4) (r 5) (c 0) (c 1) (c 3) (c 4) (c 5) +
    ((-1:ℤ)^3*M (r 0) (c 3)*minor5 M (r 1) (r 2) (r 3) (r 4) (r 5) (c 0) (c 1) (c 2) (c 4) (c 5) +
    ((-1:ℤ)^4*M (r 0) (c 4)*minor5 M (r 1) (r 2) (r 3) (r 4) (r 5) (c 0) (c 1) (c 2) (c 3) (c 5) +
    ((-1:ℤ)^5*M (r 0) (c 5)*minor5 M (r 1) (r 2) (r 3) (r 4) (r 5) (c 0) (c 1) (c 2) (c 3) (c 4)))))) = _
  unfold minor6;ring

set_option maxRecDepth 10000 in
theorem det_skew4 (M : Matrix (Fin 4) (Fin 4) ℤ) (anti : ∀ i j,M j i= -M i j) :
    M.det=(pf4 M 0 1 2 3)^2 := by
  have zero (i : Fin 4) : M i i=0 := by have h := anti i i;omega
  have e := expand4 M id id
  change M.det=minor4 M 0 1 2 3 0 1 2 3 at e
  rw [e]
  simp only [minor3,minor4,pf4,zero,anti 0 1,anti 0 2,anti 0 3,anti 1 2,anti 1 3,anti 2 3]
  ring

set_option maxRecDepth 10000 in
theorem det_skew6 (M : Matrix (Fin 6) (Fin 6) ℤ) (anti : ∀ i j,M j i= -M i j) :
    M.det=(pf6 M 0 1 2 3 4 5)^2 := by
  have zero (i : Fin 6) : M i i=0 := by have h := anti i i;omega
  have e := expand6 M id id
  change M.det=minor6 M 0 1 2 3 4 5 0 1 2 3 4 5 at e
  rw [e]
  simp only [minor3,minor4,minor5,minor6,pf6,pf4,zero,anti 0 1,anti 0 2,anti 0 3,anti 0 4,anti 0 5,anti 1 2,anti 1 3,anti 1 4,anti 1 5,anti 2 3,anti 2 4,anti 2 5,anti 3 4,anti 3 5,anti 4 5]
  ring

end SavchenkoSix
