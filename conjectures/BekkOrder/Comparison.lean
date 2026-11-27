module

public import conjectures.BekkOrder.PairTests
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace BekkOrder
open Finset Polynomial
variable {n m : ℕ}

/-- The test vanishes at every basis node but the other end of the pair. -/
theorem isolated (B : Basis n m) (i : Fin m) {u c : ℕ}
    (ends : u=B.start i ∧ c=B.start i+1 ∨ u=B.start i+1 ∧ c=B.start i) (p : ℝ) :
    avg n p (fun x ↦ ((x:ℝ)-c)*(kernelPoly B i).eval (x:ℝ))=
      weight B p u*((u:ℝ)-c)*(kernelPoly B i).eval (u:ℝ) := by
  rw [test_average]
  apply sum_eq_single u
  · intro x hx ne
    rcases (B.mem_nodes x).mp hx with rfl|⟨j,hj⟩
    · rw [kernel_top,mul_zero]
    · by_cases same : j=i
      · subst j
        have hc : x=c := by rcases ends with e|e <;> omega
        rw [hc,sub_self,mul_zero,zero_mul]
      · rw [kernel_zero B same hj,mul_zero]
  · intro no
    have hu : u∈B.nodes := (B.mem_nodes _).mpr (.inr ⟨i,by rcases ends with h|h <;> simp [h.1]⟩)
    exact (no hu).elim

theorem left_mass (B : Basis n m) (i : Fin m) (p : ℝ) :
    avg n p (fun x ↦ ((x:ℝ)-(B.start i+1:ℕ))*(kernelPoly B i).eval (x:ℝ))=
      -weight B p (B.start i)*(kernelPoly B i).eval (B.start i:ℝ) := by
  rw [isolated B i (Or.inl ⟨rfl,rfl⟩)]
  push_cast;ring

theorem right_mass (B : Basis n m) (i : Fin m) (p : ℝ) :
    avg n p (fun x ↦ ((x:ℝ)-B.start i)*(kernelPoly B i).eval (x:ℝ))=
      weight B p (B.start i+1)*(kernelPoly B i).eval ((B.start i+1:ℕ):ℝ) := by
  rw [isolated B i (Or.inr ⟨rfl,rfl⟩)]
  push_cast;ring

/-- A pair from the lexicographically earlier basis separates the two feasible parameters. -/
theorem ordered {A B : Basis n m} (ab : Before A B) {p q : ℝ}
    (hp : p∈InteriorFeasible A) (hq : q∈InteriorFeasible B) : p≤q := by
  by_contra! rev
  obtain ⟨i,initial,gt⟩ := ab
  obtain ⟨w,pos,matchmom⟩ := hq.2
  let c := A.start i+1
  let k (x : ℕ) := (kernelPoly A i).eval (x:ℝ)
  have hmom := matchmom (testPoly A i c) (test_degree A i c)
  have sign (x : ℕ) (hx : x∈B.nodes) : 0≤(testPoly A i c).eval (x:ℝ) := by
    rw [test_eval]
    rcases (B.mem_nodes x).mp hx with rfl|⟨j,hj⟩
    · rw [kernel_top,mul_zero]
    · by_cases ji : j < i
      · rw [←initial j ji] at hj
        rw [kernel_zero A ji.ne hj,mul_zero]
      · have above : B.start i≤B.start j := by
          rcases eq_or_lt_of_le (le_of_not_gt ji) with e|e
          · rw [e]
          · have h := B.separated i j e; omega
        have hx' : c≤x := by dsimp [c]; omega
        have xn : x≤n := by have h := B.below j; omega
        exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hx')) (kernel_nonneg A i xn)
  have nonneg : 0≤avg n q (fun x ↦ ((x:ℝ)-c)*k x) := by
    have h := sum_nonneg (fun x hx ↦ mul_nonneg (pos x hx) (sign x hx))
    rw [hmom] at h
    simpa only [avg,binWeight,test_eval,k] using h
  have cross := avg_crossing hq.1.1 rev hp.1.2 (fun x hx ↦ kernel_nonneg A i hx)
    (show ∃ x≤n, x≠c ∧ 0<k x from ⟨A.start i,by have h := A.below i; omega,
      by dsimp [c];omega,kernel_pos A i (Or.inl rfl)⟩) nonneg
  change 0<avg n p (fun x ↦ ((x:ℝ)-(A.start i+1:ℕ))*(kernelPoly A i).eval (x:ℝ)) at cross
  rw [left_mass] at cross
  have v := (feasible_iff A p).mp hp.2 (A.start i) ((A.mem_nodes _).mpr (.inr ⟨i,Or.inl rfl⟩))
  exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr v) (kernel_pos A i (Or.inl rfl)).le).not_gt cross

end BekkOrder
end
