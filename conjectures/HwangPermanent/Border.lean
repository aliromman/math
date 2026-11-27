module
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

@[expose] public section
namespace HwangPermanent

noncomputable section

open Finset Equiv Polynomial

variable {α R : Type*} [Fintype α] [DecidableEq α] [CommSemiring R]

def border (A : Matrix α α R) (r c : α → R) (s : R) : Matrix (Option α) (Option α) R
  | none, none => s
  | none, some j => r j
  | some i, none => c i
  | some i, some j => A i j

private theorem term_some (A : Matrix α α R) (r c : α → R) (s : R)
    (σ : Perm α) (a : α) :
    (∏ i, border A r c s (Perm.decomposeOption.symm (some (σ a), σ) i) i) =
      c (σ a) * r a * ∏ i ∈ univ.erase a, A (σ i) i := by
  classical
  rw [Fintype.prod_option]
  simp only [Perm.decomposeOption_symm_apply, Perm.coe_mul, Function.comp_apply,
    optionCongr_apply, Option.map_none, Option.map_some, swap_apply_left, border]
  rw [← Finset.mul_prod_erase univ _ (mem_univ a)]
  simp only [swap_apply_right, mul_assoc]
  congr 2
  apply prod_congr rfl
  intro i hi
  have hia : i ≠ a := (mem_erase.mp hi).1
  rw [swap_apply_of_ne_of_ne (by simp) (by simpa using hia)]

private theorem border_formula (A : Matrix α α R) (r c : α → R) (s : R) :
    (border A r c s).permanent =
      s * A.permanent + ∑ σ : Perm α, ∑ a, c (σ a) * r a * ∏ i ∈ univ.erase a, A (σ i) i := by
  classical
  unfold Matrix.permanent
  rw [← (Perm.decomposeOption.symm).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  congr 1
  · rw [Finset.mul_sum]
    apply sum_congr rfl
    intro σ _
    rw [Fintype.prod_option]
    simp [border]
  · rw [Finset.sum_comm]
    apply sum_congr rfl
    intro σ _
    let f (i : α) := ∏ j, border A r c s (Perm.decomposeOption.symm (some i, σ) j) j
    exact (Equiv.sum_comp σ f).symm.trans (sum_congr rfl fun i _ ↦ term_some A r c s σ i)

def shift (A : Matrix α α R) : Matrix α α R[X] :=
  fun i j ↦ C (A i j) + X

def gen (A : Matrix α α R) : R[X] := (shift A).permanent

private theorem derivative_gen (A : Matrix α α R) : derivative (gen A) =
    ∑ σ : Perm α, ∑ a, ∏ i ∈ univ.erase a, shift A (σ i) i := by
  classical
  simp [gen, Matrix.permanent, derivative_prod_finset, shift]

private theorem gen_border (A : Matrix α α R) (r c s : R) :
    gen (border A (fun _ ↦ r) (fun _ ↦ c) s) =
    (C s + X) * gen A + ((C c + X) * (C r + X)) * derivative (gen A) := by
  have heq : shift (border A (fun _ ↦ r) (fun _ ↦ c) s) =
      border (shift A) (fun _ ↦ C r + X) (fun _ ↦ C c + X) (C s + X) := by
    ext (i | i) (j | j) <;> rfl
  change (shift _).permanent = _
  rw [heq, border_formula, derivative_gen]
  simp only [Finset.mul_sum, gen]

omit [Fintype α] [DecidableEq α] in
private theorem shift_border (A : Matrix α α R) (r c : α → R) (s : R) :
    shift (border A r c s) = border (shift A)
      (fun i ↦ C (r i) + X) (fun i ↦ C (c i) + X) (C s + X) := by
  ext (i | i) (j | j) <;> rfl

private theorem gen_corner (A : Matrix α α R) (r c : α → R) :
    gen (border A r c 1) = gen (border A r c 0) + gen A := by
  simp only [gen, shift_border, border_formula, map_one, map_zero, zero_add]
  ring

def edge : Option α → R
  | none => 1
  | some _ => 0

/-- Put the board between two new indices, including the new top-right corner. -/
def wrap (A : Matrix α α R) : Matrix (Option (Option α)) (Option (Option α)) R :=
  border (border A (fun _ ↦ 0) (fun _ ↦ 1) 1) (fun _ ↦ 1) edge 1

private def plain (A : Matrix α α R) : Matrix (Option (Option α)) (Option (Option α)) R :=
  border (border A (fun _ ↦ 0) (fun _ ↦ 1) 1) (fun _ ↦ 1) (fun _ ↦ 0) 1

def triangular (P : R[X]) := (1 + X) * P + X * (1 + X) * derivative P

def step (P : R[X]) := triangular (triangular P) +
  ((1 + X) * P + (1 + X) ^ 2 * derivative P)

private theorem gen_perm_rows (A : Matrix α α R) (σ : Perm α) :
    gen (A.submatrix σ id) = gen A := Matrix.permanent_permute_cols σ (shift A)

theorem gen_wrap (A : Matrix α α R) : gen (wrap A) = step (gen A) := by
  let σ := swap (none : Option (Option α)) (some none)
  let B := border A (fun _ ↦ 1) (fun _ ↦ 1) 1
  have h₁ : (wrap A).submatrix σ id = border B edge edge 1 := by
    ext i j
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
      simp [wrap, B, border, edge, σ, swap_apply_def, Matrix.submatrix_apply]
  have h₀ : (plain A).submatrix σ id = border B edge edge 0 := by
    ext i j
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
      simp [plain, B, border, edge, σ, swap_apply_def, Matrix.submatrix_apply]
  rw [← gen_perm_rows (wrap A) σ, h₁, gen_corner, ← h₀, gen_perm_rows]
  have hleft (M : Matrix α α R) :
      gen (border M (fun _ ↦ 0) (fun _ ↦ 1) 1) = triangular (gen M) := by
    rw [gen_border]
    simp [triangular, mul_comm]
  unfold plain B
  rw [gen_border, hleft, gen_border]
  simp only [map_one, map_zero, zero_add, step]
  unfold triangular
  ring

theorem gen_reindex {β : Type*} [Fintype β] [DecidableEq β] (e : β ≃ α)
    (A : Matrix α α R) : gen (A.submatrix e e) = gen A := by
  unfold gen Matrix.permanent
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ ?_
  intro σ
  refine Fintype.prod_equiv e _ _ ?_
  intro i
  simp [shift, Equiv.permCongr_apply]

theorem eval_gen (A : Matrix α α R) (x : R) :
    (gen A).eval x = Matrix.permanent ((fun i j ↦ A i j + x) : Matrix α α R) := by
  simp [gen, Matrix.permanent, shift, eval_finsetSum, eval_prod]

theorem step_add (P Q : R[X]) : step (P + Q) = step P + step Q := by
  simp only [step, triangular, map_add, mul_add]
  ring

end

end HwangPermanent
