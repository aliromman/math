module

public import conjectures.SavchenkoSix.Statement
public import conjectures.SavchenkoSix.TupleSums
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section
namespace SavchenkoSix
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V] (T : Tournament V)

def triangle (a b c : V) : ℤ := T.adj a b*T.adj b c*T.adj c a

def throughVertex (a : V) : ℤ := ∑ b,∑ c,triangle T a b c

def throughArc (a b : V) : ℤ := ∑ c,triangle T a b c

private def w (x : Fin 6→V) : ℤ := closed6 T.adj (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
private def oneDup (x : Fin 6→V) : ℤ := if x 0=x 3 then w T x else 0
private def twoDups (x : Fin 6→V) : ℤ := if x 0=x 3 ∧ x 1=x 4 then w T x else 0
private def threeDups (x : Fin 6→V) : ℤ := if x 0=x 3 ∧ x 1=x 4 ∧ x 2=x 5 then w T x else 0

omit [Fintype V] [DecidableEq V] in
private theorem w_indicator (x : Fin 6→V) : w T x = if (∀ i : Fin 6,T.arc (x i) (x (i+1))=true) then 1 else 0 := by
  have all : (∀ i : Fin 6,T.arc (x i) (x (i+1))=true) ↔
      T.arc (x 0) (x 1)=true ∧ T.arc (x 1) (x 2)=true ∧ T.arc (x 2) (x 3)=true ∧
      T.arc (x 3) (x 4)=true ∧ T.arc (x 4) (x 5)=true ∧ T.arc (x 5) (x 0)=true := by
    constructor
    · exact fun h ↦ ⟨h 0,h 1,h 2,h 3,h 4,h 5⟩
    · intro h i
      fin_cases i <;> tauto
  rw [if_congr all rfl rfl]
  simp only [w,closed6,Tournament.adj,ite_mul,one_mul,zero_mul]
  split_ifs <;> simp_all

omit [Fintype V] [DecidableEq V] in
private theorem admissible_injective {x : Fin 6→V} (H : ∀ i : Fin 6, T.arc (x i) (x (i+1))=true) :
    Function.Injective x ↔ x 0≠x 3 ∧ x 1≠x 4 ∧ x 2≠x 5 := by
  constructor
  · exact fun h ↦ ⟨h.ne (by decide),h.ne (by decide),h.ne (by decide)⟩
  · intro dis i j eq
    have step (k : Fin 6) : x k≠x (k+1) := by
      intro e
      simpa [e,T.loopless] using H k
    have skip (k : Fin 6) : x k≠x (k+2) := by
      intro e
      have op := T.orientation (step k)
      have right := H (k+1)
      rw [show k+1+1=k+2 by omega,←e] at right
      simp [right,H k] at op
    have a0 := step 0; have a1 := step 1; have a2 := step 2
    have a3 := step 3; have a4 := step 4; have a5 := step 5
    have b0 := skip 0; have b1 := skip 1; have b2 := skip 2
    have b3 := skip 3; have b4 := skip 4; have b5 := skip 5
    fin_cases i <;> fin_cases j <;> norm_num at * <;> grind

private abbrev rot (i : Fin 6) := Equiv.addRight i

omit [Fintype V] in
private theorem exclusions (x : Fin 6→V) :
    w T x = (if Function.Injective x then w T x else 0) +
      oneDup T x+oneDup T (x∘rot 1)+oneDup T (x∘rot 2)-
      twoDups T x-twoDups T (x∘rot 1)-twoDups T (x∘rot 2)+threeDups T x := by
  have shift1 : w T (x∘rot 1)=w T x := by
    change closed6 _ (x 1) (x 2) (x 3) (x 4) (x 5) (x 0) = _
    unfold w closed6
    ring
  have shift2 : w T (x∘rot 2)=w T x := by
    change closed6 _ (x 2) (x 3) (x 4) (x 5) (x 0) (x 1) = _
    unfold w closed6
    ring
  unfold oneDup twoDups threeDups
  simp only [shift1,shift2]
  change w T x = (if Function.Injective x then w T x else 0) +
    (if x 0=x 3 then w T x else 0)+(if x 1=x 4 then w T x else 0)+(if x 2=x 5 then w T x else 0)-
    (if x 0=x 3 ∧ x 1=x 4 then w T x else 0)-
    (if x 1=x 4 ∧ x 2=x 5 then w T x else 0)-
    (if x 2=x 5 ∧ x 3=x 0 then w T x else 0)+
    (if x 0=x 3 ∧ x 1=x 4 ∧ x 2=x 5 then w T x else 0)
  by_cases H : ∀ i : Fin 6,T.arc (x i) (x (i+1))=true
  · rw [if_congr (admissible_injective T H) rfl rfl]
    by_cases h₀ : x 0=x 3 <;> by_cases h₁ : x 1=x 4 <;> by_cases h₂ : x 2=x 5 <;>
      simp [h₀,h₁,h₂,eq_comm (a:=x 3) (b:=x 0)]
  · simp [w_indicator T x,H]

private theorem one_sum : ∑ x,oneDup T x = ∑ a, (throughVertex T a)^2 := by
  unfold oneDup w
  rw [sum_six (fun a b c d e f ↦ if a=d then closed6 T.adj a b c d e f else 0)]
  simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true]
  simp only [throughVertex,triangle,pow_two,sum_mul,mul_sum,closed6,mul_assoc]
  repeat' (apply sum_congr rfl; intro _ _)
  ring

private theorem two_sum : ∑ x,twoDups T x = ∑ a,∑ b, (throughArc T a b)^2 := by
  unfold twoDups w
  rw [sum_six (fun a b c d e f ↦ if a=d ∧ b=e then closed6 T.adj a b c d e f else 0)]
  simp_rw [ite_and]
  simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true]
  simp only [throughArc,triangle,pow_two,sum_mul,mul_sum,closed6,mul_assoc]
  repeat' (apply sum_congr rfl; intro _ _)
  ring

private theorem three_sum : ∑ x,threeDups T x = ∑ a,throughVertex T a := by
  unfold threeDups w
  rw [sum_six (fun a b c d e f ↦ if a=d ∧ b=e ∧ c=f then closed6 T.adj a b c d e f else 0)]
  simp_rw [ite_and]
  simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true,closed6,throughVertex,triangle]
  apply sum_congr rfl;intro a _
  apply sum_congr rfl;intro b _
  apply sum_congr rfl;intro c _
  simp only [Tournament.adj]
  split_ifs <;> norm_num

theorem repeated_count : (T.adj^6).trace = (orderedSix T : ℤ)+3*(∑ a,(throughVertex T a)^2)-
    3*(∑ a,∑ b,(throughArc T a b)^2)+∑ a,throughVertex T a := by
  classical
  have inj : (orderedSix T : ℤ) = ∑ x : Fin 6→V, if Function.Injective x then w T x else 0 := by
    rw [←sum_injections (w T)]
    simp only [orderedSix,Nat.cast_sum,apply_ite (Nat.cast : ℕ→ℤ),Nat.cast_one,Nat.cast_zero,w_indicator]
  have tot : (T.adj^6).trace = ∑ x : Fin 6→V,w T x := by
    rw [trace6,←sum_six]; rfl
  rw [tot]
  calc ∑ x : Fin 6→V,w T x = _ := sum_congr rfl (fun x _ ↦ exclusions T x)
       _ = _ := by
        simp only [sum_add_distrib,sum_sub_distrib, sum_rotate,←inj,one_sum,two_sum,three_sum]
        ring

end SavchenkoSix
