module

public import conjectures.BekkOrder.Quadrature
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace BekkOrder
open Finset Polynomial
variable {n m : ℕ}

def pairPoly (a : ℕ) : ℝ[X] := (X-C (a:ℝ))*(X-C ((a+1:ℕ):ℝ))

def kernelPoly (B : Basis n m) (i : Fin m) : ℝ[X] :=
  (C (n:ℝ)-X)*∏ j∈univ.erase i,pairPoly (B.start j)

def testPoly (B : Basis n m) (i : Fin m) (c : ℕ) : ℝ[X] :=
  (X-C (c:ℝ))*kernelPoly B i

theorem pair_eval (a x : ℕ) : (pairPoly a).eval (x:ℝ)=((x:ℝ)-a)*((x:ℝ)-(a+1:ℕ)) := by
  simp [pairPoly]

theorem pair_nonneg (a x : ℕ) : 0≤(pairPoly a).eval (x:ℝ) := by
  rw [pair_eval]
  by_cases h : x≤a
  · exact mul_nonneg_of_nonpos_of_nonpos (by exact_mod_cast (sub_nonpos.mpr (show (x:ℝ)≤a by exact_mod_cast h)))
      (sub_nonpos.mpr (by exact_mod_cast (show x≤a+1 by omega)))
  · exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast (show a≤x by omega)))
      (sub_nonneg.mpr (by exact_mod_cast (show a+1≤x by omega)))

theorem pair_pos {a x : ℕ} (ha : x≠a) (hb : x≠a+1) : 0<(pairPoly a).eval (x:ℝ) := by
  apply lt_of_le_of_ne (pair_nonneg a x)
  rw [pair_eval]
  exact Ne.symm (mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast ha)) (sub_ne_zero.mpr (by exact_mod_cast hb)))

theorem pair_zero {a x : ℕ} (h : x=a ∨ x=a+1) : (pairPoly a).eval (x:ℝ)=0 := by
  rcases h with rfl|rfl <;> simp [pairPoly]

theorem test_eval (B : Basis n m) (i : Fin m) (c x : ℕ) :
    (testPoly B i c).eval (x:ℝ)=((x:ℝ)-c)*(kernelPoly B i).eval (x:ℝ) := by simp [testPoly]

theorem kernel_eval (B : Basis n m) (i : Fin m) (x : ℕ) :
    (kernelPoly B i).eval (x:ℝ)=((n:ℝ)-x)*∏ j∈univ.erase i,(pairPoly (B.start j)).eval (x:ℝ) := by
  simp [kernelPoly,eval_prod]

theorem kernel_nonneg (B : Basis n m) (i : Fin m) {x : ℕ} (hx : x≤n) :
    0≤(kernelPoly B i).eval (x:ℝ) := by
  rw [kernel_eval]
  exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hx)) (prod_nonneg (fun j _ ↦ pair_nonneg _ _))

theorem kernel_pos (B : Basis n m) (i : Fin m) {x : ℕ} (hx : x=B.start i ∨ x=B.start i+1) :
    0<(kernelPoly B i).eval (x:ℝ) := by
  rw [kernel_eval]
  have hn : x<n := by have h := B.below i; omega
  apply mul_pos (sub_pos.mpr (by exact_mod_cast hn)) (prod_pos _)
  intro j hj
  have ne := (mem_erase.mp hj).1
  rcases lt_or_gt_of_ne ne with h|h
  · have d := B.separated j i h
    exact pair_pos (by omega) (by omega)
  · have d := B.separated i j h
    exact pair_pos (by omega) (by omega)

theorem kernel_top (B : Basis n m) (i : Fin m) : (kernelPoly B i).eval (n:ℝ)=0 := by
  rw [kernel_eval];simp

theorem kernel_zero (B : Basis n m) {i j : Fin m} (h : j≠i) {x : ℕ} (hx : x=B.start j ∨ x=B.start j+1) :
    (kernelPoly B i).eval (x:ℝ)=0 := by
  rw [kernel_eval,prod_eq_zero (mem_erase.mpr ⟨h,mem_univ _⟩) (pair_zero hx),mul_zero]

theorem pair_degree (a : ℕ) : (pairPoly a).natDegree≤2 := by
  exact natDegree_mul_le_of_le (natDegree_X_sub_C_le _) (natDegree_X_sub_C_le _)

theorem test_degree (B : Basis n m) (i : Fin m) (c : ℕ) : (testPoly B i c).natDegree≤2*m := by
  have sd := natDegree_prod_le (univ.erase i) (fun j ↦ pairPoly (B.start j))
  have sum := sum_le_sum (s:=univ.erase i) (fun j _ ↦ pair_degree (B.start j))
  have card : (univ.erase i).card=m-1 := by simp
  simp only [sum_const,nsmul_eq_mul,card] at sum
  have top : (C (n:ℝ)-X).natDegree≤1 := (natDegree_sub_le ..).trans (by simp)
  have first : (X-C (c:ℝ)).natDegree=1 := natDegree_X_sub_C _
  have a := natDegree_mul_le (p:=C (n:ℝ)-X) (q:=∏ j∈univ.erase i,pairPoly (B.start j))
  have b := natDegree_mul_le (p:=X-C (c:ℝ)) (q:=kernelPoly B i)
  change (kernelPoly B i).natDegree≤_ at a
  change (testPoly B i c).natDegree≤_ at b
  have hi := i.isLt
  change _ ≤ (m-1)*2 at sum
  omega

theorem test_average (B : Basis n m) (i : Fin m) (c : ℕ) (p : ℝ) :
    avg n p (fun x ↦ ((x:ℝ)-c)*(kernelPoly B i).eval (x:ℝ))=
      ∑ x∈B.nodes,weight B p x*((x:ℝ)-c)*(kernelPoly B i).eval (x:ℝ) := by
  have h := quadrature B p (testPoly B i c) (test_degree B i c)
  simp_rw [test_eval] at h
  simpa only [mul_assoc] using h.symm

end BekkOrder
end
