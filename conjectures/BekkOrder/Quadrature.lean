module

public import conjectures.BekkOrder.Statement
public import conjectures.BekkOrder.Monotone
import Mathlib.Tactic.LinearCombination

@[expose] public section
noncomputable section
namespace BekkOrder
open Finset Polynomial
variable {n m : ℕ}

abbrev lag (B : Basis n m) (u : ℕ) := Lagrange.basis B.nodes (fun t : ℕ ↦ (t:ℝ)) u

def weight (B : Basis n m) (p : ℝ) (u : ℕ) := avg n p (fun x ↦ (lag B u).eval (x:ℝ))

private theorem injection (B : Basis n m) : Set.InjOn (fun t : ℕ ↦ (t:ℝ)) B.nodes :=
  fun _ _ _ _ h ↦ Nat.cast_injective h

theorem lag_degree (B : Basis n m) {u : ℕ} (h : u∈B.nodes) :
    (lag B u).natDegree=2*m := by rw [lag,Lagrange.natDegree_basis (injection B) h,B.nodes_card];omega

/-- Integration of the cardinal interpolant gives each basic weight, including at a breakpoint. -/
theorem quadrature (B : Basis n m) (p : ℝ) (P : ℝ[X]) (hP : P.natDegree≤2*m) :
    ∑ x∈B.nodes,weight B p x*P.eval (x:ℝ) = avg n p (fun x ↦ P.eval (x:ℝ)) := by
  have deg : P.degree < (B.nodes.card:WithBot ℕ) := by
    have hd : P.natDegree<B.nodes.card := by rw [B.nodes_card]; omega
    exact P.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hd)
  have h := Lagrange.eq_interpolate (f:=P) (injection B) deg
  have ev (x : ℕ) : P.eval (x:ℝ)=∑ u∈B.nodes, (P.eval (u:ℝ))*(lag B u).eval (x:ℝ) := by
    nth_rw 1 [h]
    simp only [Lagrange.interpolate_apply,eval_finsetSum,eval_mul,eval_C,lag]
  have fn : (fun x : ℕ ↦ P.eval (x:ℝ)) = (fun x : ℕ ↦ ∑ u∈B.nodes,P.eval (u:ℝ)*(lag B u).eval (x:ℝ)) := funext ev
  rw [fn]
  unfold weight avg
  simp only [sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro u _
  ring

private theorem weighted_lag (B : Basis n m) (w : ℕ→ℝ) {u : ℕ} (hu : u∈B.nodes) :
    ∑ x∈B.nodes,w x*(lag B u).eval (x:ℝ)=w u := by
  rw [sum_eq_single u]
  · rw [lag,Lagrange.eval_basis_self (injection B) hu,mul_one]
  · intro x hx h
    rw [lag,Lagrange.eval_basis_of_ne (Ne.symm h) hx,mul_zero]
  · exact fun h ↦ (h hu).elim

theorem feasible_iff (B : Basis n m) (p : ℝ) : Feasible B p ↔ ∀ u∈B.nodes,0≤weight B p u := by
  constructor
  · rintro ⟨w,hw,h⟩ u hu
    have eq := h (lag B u) (lag_degree B hu).le
    rw [weighted_lag B w hu] at eq
    change w u=weight B p u at eq
    rw [←eq]
    exact hw u hu
  · intro h
    exact ⟨weight B p,h,quadrature B p⟩

end BekkOrder
end
