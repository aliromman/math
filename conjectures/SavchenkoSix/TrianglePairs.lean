module

public import conjectures.SavchenkoSix.Repeated
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section
namespace SavchenkoSix
open Finset Matrix
variable {V : Type*} (T : Tournament V)

theorem arc_sum {a b : V} (h : a≠b) : T.adj a b+T.adj b a=1 := by
  simp only [Tournament.adj,T.orientation h]
  cases T.arc b a <;> decide

theorem opposite_zero (a b : V) : T.adj a b*T.adj b a=0 := by
  by_cases h : a=b
  · subst b; simp [Tournament.adj,T.loopless]
  · simp only [Tournament.adj,T.orientation h]
    cases T.arc b a <;> decide

theorem arc_sq (a b : V) : (T.adj a b)^2=T.adj a b := by
  simp [Tournament.adj]

private def rooted (a b c d : V) : ℤ := closed4 T.adj a b c d*T.adj c a*T.adj b d

private theorem pair_split [DecidableEq V] (a b c d : V) :
    triangle T a b c * triangle T a b d =
    (if c=d then triangle T a b c else 0) + rooted T a b c d + rooted T a b d c := by
  by_cases h : c=d
  · subst d
    simp only [ite_true,rooted,closed4,triangle]
    have diag : T.adj c c=0 := by simp [Tournament.adj,T.loopless]
    rw [diag];simp
    have ab := arc_sq T a b; have bc := arc_sq T b c; have ca := arc_sq T c a
    calc _ = (T.adj a b)^2*(T.adj b c)^2*(T.adj c a)^2 := by ring
         _ = _ := by rw [ab,bc,ca]
  · simp only [h,ite_false,zero_add]
    unfold triangle rooted closed4
    have ab := arc_sq T a b
    calc
      _ = (T.adj a b)^2*(T.adj b c*T.adj c a*T.adj b d*T.adj d a) := by ring
      _ = T.adj a b*(T.adj b c*T.adj c a*T.adj b d*T.adj d a)*(T.adj c d+T.adj d c) := by rw [ab,arc_sum T h,mul_one]
      _ = _ := by ring

private theorem mark_one (a b c d : V) : closed4 T.adj a b c d =
    rooted T a b c d + rooted T b c d a + rooted T c d a b + rooted T d a b c := by
  let v := closed4 T.adj a b c d
  have form : rooted T a b c d + rooted T b c d a + rooted T c d a b + rooted T d a b c =
      v*(T.adj c a+T.adj a c)*(T.adj b d+T.adj d b) := by
    unfold rooted v closed4
    ring
  rw [form]
  by_cases zero : v=0
  · change v=_
    simp [zero]
  have ac : c≠a := by
    rintro rfl
    apply zero
    change _*_*_*_=0
    rw [opposite_zero];ring
  have bd : b≠d := by
    rintro rfl
    apply zero
    change T.adj a b*T.adj b c*T.adj c b*T.adj b a=0
    calc _ = (T.adj c b*T.adj b c)*(T.adj a b*T.adj b a) := by ring
         _ = _ := by rw [opposite_zero,zero_mul]
  rw [arc_sum T ac,arc_sum T bd,mul_one,mul_one]

variable [Fintype V] [DecidableEq V]

private theorem sum_rooted : (T.adj^4).trace=4*∑ a,∑ b,∑ c,∑ d,rooted T a b c d := by
  let R (x : Fin 4→V) := rooted T (x 0) (x 1) (x 2) (x 3)
  let rot (i : Fin 4) := Equiv.addRight i
  have mark (x : Fin 4→V) : closed4 T.adj (x 0) (x 1) (x 2) (x 3)=
       R x+R (x∘rot 1)+R (x∘rot 2)+R (x∘rot 3) := mark_one T _ _ _ _
  rw [trace4,←sum_four,←sum_four (rooted T)]
  calc _ = _ := sum_congr rfl fun x _ ↦ mark x
       _ = _ := by
        simp only [sum_add_distrib,sum_rotate]
        change _=4*∑ x,R x
        ring

theorem arc_triangles : 2*(∑ a,∑ b,(throughArc T a b)^2) =
    2*(∑ a,throughVertex T a)+(T.adj^4).trace := by
  have swap (a b : V) : ∑ c,∑ d,rooted T a b d c = ∑ c,∑ d,rooted T a b c d := sum_comm
  have each (a b : V) : (throughArc T a b)^2 = (∑ c,triangle T a b c)+
      2*∑ c,∑ d,rooted T a b c d := by
    simp only [throughArc,pow_two,sum_mul,mul_sum]
    simp_rw [pair_split T]
    simp only [sum_add_distrib,sum_ite_eq',mem_univ,ite_true,swap]
    simp only [←mul_sum]
    ring
  simp_rw [each]
  rw [sum_rooted]
  simp only [sum_add_distrib,←mul_sum,throughVertex]
  ring

end SavchenkoSix
