module

public import conjectures.SavchenkoSix.TrianglePairs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section
namespace SavchenkoSix
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem regular_row {r : ℕ} {T : Tournament V} (h : Regular r T) (x : V) :
    ∑ y,T.adj x y = (r:ℤ) := by
  simp only [Tournament.adj,sum_boole,h x]

private theorem vertex_twice {r : ℕ} {T : Tournament V} (h : Regular r T) (a : V) :
    2*throughVertex T a=(r:ℤ)*((r:ℤ)+1) := by
  let A := T.adj
  let K := ∑ b,∑ c,A a b*A a c*A b c
  have row (x : V) : ∑ y,A x y=(r:ℤ) := regular_row h x
  have rr : ∑ b,∑ c,A a b*A b c=(r:ℤ)^2 := by simp only [←mul_sum,row,←sum_mul,pow_two]
  have star : ∑ b,∑ c,A a b*A a c=(r:ℤ)^2 := by simp only [←mul_sum,row,←sum_mul,pow_two]
  have pair (b c : V) : A a b*A a c*A b c+A a c*A a b*A c b =
      A a b*A a c - (if b=c then A a b else 0) := by
    by_cases bc : b=c
    · subst c
      have sq := arc_sq T a b
      have diag : A b b=0 := by simp [A,Tournament.adj,T.loopless]
      simp only [diag,mul_zero,add_zero,ite_true]
      change _=(T.adj a b)*(T.adj a b)-T.adj a b
      nlinarith
    · have rel := arc_sum T bc
      change A b c + A c b=1 at rel
      simp only [bc,ite_false,sub_zero]
      linear_combination (A a b*A a c)*rel
  have swap : (∑ b,∑ c,A a c*A a b*A c b)=K := sum_comm
  have twice := sum_congr (s₁:=univ) rfl (fun b _ ↦ sum_congr (s₁:=univ) rfl (fun c _ ↦ pair b c))
  simp only [sum_add_distrib,sum_sub_distrib,swap,sum_ite_eq,mem_univ,ite_true,row,star] at twice
  have split (b c : V) : A a b*A b c*A c a=A a b*A b c-A a b*A a c*A b c := by
    by_cases ac : a=c
    · subst c
      have ba := opposite_zero T a b
      have diag : A a a=0 := by simp [A,Tournament.adj,T.loopless]
      change A a b*A b a=0 at ba
      simp [diag,ba]
    · have rel := arc_sum T ac
      change A a c+A c a=1 at rel
      linear_combination (A a b*A b c)*rel
  have tri : throughVertex T a=(r:ℤ)^2-K := by
    change (∑b,∑c,A a b*A b c*A c a)=_
    simp_rw [split]
    simp only [sum_sub_distrib,rr,K]
  change K+K=(r:ℤ)^2-r at twice
  rw [tri]
  linarith

/-- The counts of repeated six-step walks cancel except for a four-cycle correction. -/
theorem ordinary_difference {r : ℕ} (T U : Tournament V) (hT : Regular r T) (hU : Regular r U) :
    2*((orderedSix T : ℤ)-orderedSix U)=
    2*((T.adj^6).trace-(U.adj^6).trace)+3*((T.adj^4).trace-(U.adj^4).trace) := by
  have same (a : V) : throughVertex T a=throughVertex U a := by
    linarith only [vertex_twice hT a,vertex_twice hU a]
  have t := repeated_count T
  have u := repeated_count U
  have p := arc_triangles T
  have q := arc_triangles U
  simp_rw [same] at t p
  linarith

end SavchenkoSix
