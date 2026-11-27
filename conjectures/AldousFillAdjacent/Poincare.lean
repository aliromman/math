module

public import conjectures.AldousFillAdjacent.Routes
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace AldousFillAdjacent
open Finset
open scoped BigOperators Matrix

variable {m : ℕ}

private def changeSq (f : Deck m → ℝ) (g : Deck m) : ℝ :=
  ∑ x, (f x-f (x*g))^2

private theorem change_eq (f : Deck m → ℝ) (g : Deck m) :
    changeSq f g = 2*(f ⬝ᵥ f)-2*(∑ x, f x*f (x*g)) := by
  have shift : (∑ x, f (x*g)*f (x*g)) = f ⬝ᵥ f :=
    Equiv.sum_comp (Equiv.mulRight g) (fun x ↦ f x*f x)
  have pair (a b : ℝ) : (a-b)^2=a*a+b*b-2*(a*b) := by ring
  simp only [changeSq,pair,sum_sub_distrib,sum_add_distrib,←mul_sum,shift]
  change (f ⬝ᵥ f)+(f ⬝ᵥ f)-_ = _
  ring

private theorem one_step (f : Deck m → ℝ) (i : Option (Fin m)) :
    changeSq f (move i) ≤ 2*((m:ℝ)+1)*(f ⬝ᵥ L m f) := by
  have a : (∑ i, changeSq f (move i))=2*((m:ℝ)+1)*(f ⬝ᵥ L m f) := by
    change _=2*((m:ℝ)+1)*(f ⬝ᵥ (f-P m f))
    rw [dotProduct_sub]
    have avg : (𝔼 i, ∑ x, f x*f (x*move i))=f ⬝ᵥ P m f := by
      simp only [dotProduct,P_apply,mul_expect,expect_sum_comm]
    simp only [change_eq,sum_sub_distrib,sum_const,card_univ,Fintype.card_option,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_add,Nat.cast_one,←mul_sum]
    rw [←Fintype.card_mul_expect,avg]
    simp [Fintype.card_option]
    ring
  rw [←a]
  exact single_le_sum (fun j _ ↦ sum_nonneg (s:=univ) fun x _ ↦ sq_nonneg (f x - f (x*move j))) (mem_univ i)

private def increments (f : Deck m → ℝ) (x : Deck m) : List (Option (Fin m)) → List ℝ
  | [] => []
  | s::l => (f x-f (x*move s))::increments f (x*move s) l

private theorem inc_sum (f : Deck m → ℝ) (x : Deck m) (l : List (Option (Fin m))) :
    (increments f x l).sum=f x-f (x*route l) := by
  induction l generalizing x with
  | nil => simp [increments,route]
  | cons a l ih => simp [increments,route,List.prod_cons,ih,mul_assoc]

private theorem inc_length (f : Deck m → ℝ) (x : Deck m) (l : List (Option (Fin m))) :
    (increments f x l).length=l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp [increments,ih]

private theorem inc_sq (f : Deck m → ℝ) (l : List (Option (Fin m))) :
    (∑ x, ((increments f x l).map (·^2)).sum) ≤
      l.length * (2*((m:ℝ)+1)*(f ⬝ᵥ L m f)) := by
  induction l with
  | nil => simp [increments]
  | cons a l ih =>
    simp only [increments,List.map_cons,List.sum_cons,sum_add_distrib,List.length_cons,Nat.cast_succ]
    have shift : (∑ x, ((increments f (x*move a) l).map (·^2)).sum) =
        ∑ x, ((increments f x l).map (·^2)).sum :=
      Equiv.sum_comp (Equiv.mulRight (move a)) (fun x ↦ ((increments f x l).map (·^2)).sum)
    rw [shift]
    have h := one_step f a
    unfold changeSq at h
    linarith

private theorem route_sq (f : Deck m → ℝ) (l : List (Option (Fin m))) :
    changeSq f (route l) ≤ (l.length:ℝ)^2 * (2*((m:ℝ)+1)*(f ⬝ᵥ L m f)) := by
  have point (x : Deck m) :=
    Multiset.sq_sum_le_card_mul_sum_sq (α:=ℝ) (increments f x l : Multiset ℝ)
  simp only [Multiset.sum_coe,Multiset.coe_card,Multiset.map_coe,inc_sum,inc_length] at point
  have sum := sum_le_sum (s:=univ) fun x _ ↦ point x
  rw [←mul_sum] at sum
  have v := mul_le_mul_of_nonneg_left (inc_sq f l) (Nat.cast_nonneg (α:=ℝ) l.length)
  unfold changeSq
  linarith

theorem energy_zero {f : Deck m → ℝ} (he : f ⬝ᵥ L m f=0) (g : Deck m) : f g=f 1 := by
  obtain ⟨l,rfl,_⟩ := short_route g
  have hv := route_sq f l
  rw [he] at hv
  have hi := single_le_sum (s:=univ) (fun x _ ↦ sq_nonneg (f x-f (x*route l))) (mem_univ 1)
  unfold changeSq at hv
  simp only [one_mul] at hi
  nlinarith

/-- A polynomial bound on the inverse spectral gap from short adjacent-swap routes. -/
theorem poincare (f : Deck m → ℝ) (cent : ∑ x, f x=0) :
    f ⬝ᵥ f ≤ (2*(m:ℝ)^2)^2*((m:ℝ)+1)*(f ⬝ᵥ L m f) := by
  have term (g : Deck m) : changeSq f g ≤
      (2*(m:ℝ)^2)^2*(2*((m:ℝ)+1)*(f ⬝ᵥ L m f)) := by
    obtain ⟨l,rfl,le⟩ := short_route g
    apply (route_sq f l).trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) (energy f))
    have lc : (l.length:ℝ) ≤ 2*(m:ℝ)^2 := by exact_mod_cast le
    exact pow_le_pow_left₀ (by positivity) lc 2
  have z : (∑ g : Deck m, ∑ x, f x*f (x*g))=0 := by
    rw [sum_comm]
    apply sum_eq_zero
    intro x _
    have shift : (∑ i, f (x*i))=∑ i, f i := Equiv.sum_comp (Equiv.mulLeft x) f
    rw [←mul_sum,shift,cent,mul_zero]
  have h := sum_le_sum (s:=univ) (fun x _ ↦ term x)
  simp only [change_eq,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,←mul_sum,z,mul_zero,sub_zero] at h
  have np : (0:ℝ)<Fintype.card (Deck m) := Nat.cast_pos.mpr Fintype.card_pos
  apply le_of_mul_le_mul_left _ np
  linarith

end AldousFillAdjacent
