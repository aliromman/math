module

public import conjectures.AldousFillAdjacent.Statement
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace AldousFillAdjacent
open Finset
open scoped BigOperators Matrix

variable {m : ℕ}

noncomputable def P (m : ℕ) : (Deck m → ℝ) →ₗ[ℝ] (Deck m → ℝ) where
  toFun f x := 𝔼 i, f (x*move i)
  map_add' f g := by ext x; simp [expect_add_distrib]
  map_smul' a f := by ext x; simp [←mul_expect]

noncomputable abbrev L (m : ℕ) := (LinearMap.id : (Deck m → ℝ) →ₗ[ℝ] (Deck m → ℝ))-P m

theorem P_apply (f : Deck m → ℝ) (x : Deck m) : P m f x = 𝔼 i, f (x*move i) := rfl

theorem move_square (i : Option (Fin m)) : move i * move i = 1 := by
  cases i <;> simp [move]

private theorem shift (i : Option (Fin m)) (f : Deck m → ℝ) :
    (∑ x, f (x*move i)) = ∑ x, f x := Equiv.sum_comp (Equiv.mulRight (move i)) f

theorem sum_P (f : Deck m → ℝ) : (∑ x, P m f x) = ∑ x, f x := by
  simp only [P_apply,←expect_sum_comm,shift,expect_const univ_nonempty]

theorem dot_P (f g : Deck m → ℝ) : f ⬝ᵥ P m g = P m f ⬝ᵥ g := by
  simp only [dotProduct,P_apply,mul_expect,expect_mul,←expect_sum_comm]
  apply expect_congr rfl
  intro i _
  simpa [mul_assoc,move_square] using
    (shift i (fun x ↦ f (x*move i)*g x))

theorem dot_L (f g : Deck m → ℝ) : f ⬝ᵥ L m g = L m f ⬝ᵥ g := by
  change f ⬝ᵥ (g-P m g)=(f-P m f) ⬝ᵥ g
  simp only [dotProduct_sub,sub_dotProduct,dot_P]

theorem energy (f : Deck m → ℝ) : 0 ≤ f ⬝ᵥ L m f := by
  change 0≤f ⬝ᵥ (f-P m f)
  rw [dotProduct_sub,sub_nonneg]
  simp only [dotProduct,P_apply,mul_expect,←expect_sum_comm]
  apply expect_le univ_nonempty
  intro i _
  have h := sum_le_sum (s:=univ) (fun x _ ↦ show
    2*(f x*f (x*move i)) ≤ f x*f x+f (x*move i)*f (x*move i) by nlinarith [sq_nonneg (f x-f (x*move i))])
  rw [←mul_sum,sum_add_distrib,shift i (fun x ↦ f x*f x)] at h
  linarith

def δ (m : ℕ) : Deck m → ℝ := Pi.single 1 1

theorem delta_value (x : Deck m) : δ m x = if x=1 then 1 else 0 := by simp [δ,Pi.single_apply]

theorem p_nonneg {f : Deck m → ℝ} (hf : ∀ x, 0≤f x) (x : Deck m) : 0≤P m f x :=
  expect_nonneg fun _ _ ↦ hf _

theorem delta_nonneg (x : Deck m) : 0≤δ m x := by rw [delta_value]; split <;> norm_num

theorem return1 : 1/((m:ℝ)+1) ≤ P m (δ m) 1 := by
  rw [P_apply,Fintype.expect_eq_sum_div_card]
  simp only [one_mul,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa [move,delta_value] using single_le_sum (fun i _ ↦ delta_nonneg (move i)) (mem_univ none)

theorem return2 : 1/((m:ℝ)+1) ≤ P m (P m (δ m)) 1 := by
  rw [P_apply]
  refine (expect_const univ_nonempty _).symm.le.trans (expect_le_expect fun i _ ↦ ?_)
  rw [P_apply,Fintype.expect_eq_sum_div_card]
  simp only [one_mul,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa [move_square,delta_value] using
    single_le_sum (fun j _ ↦ delta_nonneg (move i*move j)) (mem_univ i)

end AldousFillAdjacent
