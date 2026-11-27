module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.Order.Polynomial
import Mathlib.Topology.Instances.Rat
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Ring

@[expose] public section
namespace PolygonEhrhart
open Finset Polynomial

/-- A positive counting function bounded by the ambient box has degree at most its dimension. -/
theorem counting_natDegree_le {P : ℚ[X]} (pos : ∀ t : ℕ, 0<P.eval (t:ℚ))
    (hb : ∀ t : ℕ, P.eval (t:ℚ)≤(t+1:ℚ)^28) : P.natDegree≤28 := by
  by_contra! high
  let Q : ℚ[X] := (X+C 1)^28
  have qdeg : Q.natDegree=28 := by simp [Q,natDegree_pow]
  have qnz : Q≠0 := by intro h; rw [h,natDegree_zero] at qdeg;omega
  have pnz : P≠0 := by intro h;rw [h,natDegree_zero] at high;omega
  have hd : Q.degree<P.degree := by
    rw [degree_eq_natDegree qnz,degree_eq_natDegree pnz]
    exact WithBot.coe_lt_coe.mpr (qdeg ▸ high)
  have conv := (div_tendsto_atTop_zero_of_degree_lt hd).comp
    (tendsto_natCast_atTop_atTop (R:=ℚ))
  obtain ⟨t,ht⟩ := (conv.eventually_lt_const (show (0:ℚ)<1 by decide)).exists
  change Q.eval (t:ℚ)/P.eval (t:ℚ)<1 at ht
  rw [div_lt_iff₀ (pos t),one_mul] at ht
  exact (hb t).not_gt (by simpa [Q] using ht)

def weight (i : Fin 28) : ℚ :=
  (-1:ℚ)^i.val * (Nat.choose 28 (i.val+1):ℚ) / (i.val+1:ℚ)

/-- The derivative at zero of the interpolant at the integers zero through 28. -/
def slope : (Fin 29→ℚ) →ₗ[ℚ] ℚ where
  toFun v := ∑ i : Fin 28, weight i*(v i.succ-v 0)
  map_add' x y := by
    simp only [Pi.add_apply,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  map_smul' c x := by
    simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul,mul_sum]
    apply sum_congr rfl
    intro i _
    ring

private theorem slope_power : ∀ j : Fin 29, slope (fun t : Fin 29 ↦ (t.val:ℚ)^j.val)=
    if j=1 then 1 else 0 := by decide +kernel

theorem slope_eq_coeff (P : ℚ[X]) (hd : P.natDegree≤28) :
    slope (fun t : Fin 29 ↦ P.eval (t.val:ℚ))=P.coeff 1 := by
  have decomp : (fun t : Fin 29 ↦ P.eval (t.val:ℚ)) =
      ∑ k : Fin 29, P.coeff k.val • (fun t : Fin 29 ↦ (t.val:ℚ)^k.val) := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [eval_eq_sum_range' (show P.natDegree<29 by omega)]
    exact (Fin.sum_univ_eq_sum_range (fun i ↦ P.coeff i*(t.val:ℚ)^i) 29).symm
  rw [decomp,map_sum]
  simp [slope_power]

end PolygonEhrhart
