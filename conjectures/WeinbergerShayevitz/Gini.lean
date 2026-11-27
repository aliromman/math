module

public import conjectures.WeinbergerShayevitz.Statement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace WeinbergerShayevitz
open Finset
open scoped BigOperators

noncomputable def cmp (x y : ℝ) : ℝ := (if y<x then 1 else 0) - (if x<y then 1 else 0)

theorem cmp_swap (x y : ℝ) : cmp y x = -cmp x y := by unfold cmp; ring

variable {X : Type*} [Fintype X]

/-- The expected signed bit times the relative position of the guessed word
when scores `w` determine the order. -/
noncomputable def alignment (z w : X → ℝ) : ℝ := 𝔼 x, z x * (𝔼 y, cmp (w x) (w y))

private theorem rotation (f : X → X → X → ℝ) :
    (𝔼 x, 𝔼 y, 𝔼 z, f y z x) = 𝔼 x, 𝔼 y, 𝔼 z, f x y z := by
  calc
    _ = 𝔼 y, 𝔼 x, 𝔼 z, f y z x := expect_comm ..
    _ = _ := expect_congr rfl fun y _ ↦ expect_comm ..

private theorem order_triple (a b c : ℝ) :
    cmp a b*cmp a c + cmp b c*cmp b a + cmp c a*cmp c b ≤ 1 := by
  dsimp [cmp]
  split_ifs <;> norm_num

variable [Nonempty X]

private theorem rank_variance (w : X → ℝ) :
    (𝔼 x, (𝔼 y, cmp (w x) (w y)) ^ 2) ≤ (1:ℝ)/3 := by
  let f (x y z : X) := cmp (w x) (w y) * cmp (w x) (w z)
  have h := Finset.expect_le_expect (s := (univ : Finset X)) (fun x _ ↦
    Finset.expect_le_expect (s := (univ : Finset X)) (fun y _ ↦
    Finset.expect_le_expect (s := (univ : Finset X)) (fun u _ ↦ order_triple (w x) (w y) (w u))))
  change (𝔼 x, 𝔼 y, 𝔼 u, (f x y u + f y u x + f u x y)) ≤ _ at h
  simp only [expect_add_distrib,expect_const univ_nonempty] at h
  have h' := rotation (fun x y z ↦ f y z x)
  rw [rotation f] at h'
  rw [rotation f,h'] at h
  simp only [pow_two,Fintype.expect_mul_expect]
  change (𝔼 x, 𝔼 y, 𝔼 z, f x y z) ≤ _
  linarith

theorem alignment_sq (z w : X → ℝ) :
    (alignment z w)^2 ≤ (𝔼 x, (z x)^2)/3 := by
  have h := expect_mul_sq_le_sq_mul_sq univ z (fun x ↦ 𝔼 y, cmp (w x) (w y))
  apply h.trans
  have v := mul_le_mul_of_nonneg_left (rank_variance w) (expect_nonneg (s:=univ) fun x _ ↦ sq_nonneg (z x))
  linarith

omit [Nonempty X] in
private theorem twice_alignment (z w : X → ℝ) :
    (𝔼 x, 𝔼 y, (z x-z y)*cmp (w x) (w y)) = 2*alignment z w := by
  have hs : (𝔼 x, 𝔼 y, z y*cmp (w x) (w y)) = -alignment z w := by
    rw [expect_comm]
    unfold alignment
    rw [← expect_neg_distrib]
    apply expect_congr rfl
    intro x _
    rw [mul_expect, ← expect_neg_distrib]
    apply expect_congr rfl
    intro y _
    rw [cmp_swap (w x) (w y), mul_neg]
  simp_rw [sub_mul,expect_sub_distrib]
  rw [hs]
  simp only [← mul_expect,alignment]
  ring

omit [Nonempty X] in
theorem alignment_le (z w : X → ℝ) : alignment z w ≤ alignment z z := by
  have h := expect_le_expect (s:=univ) (fun x _ ↦ expect_le_expect (s:=univ)
    (fun y _ ↦ show (z x-z y)*cmp (w x) (w y) ≤ (z x-z y)*cmp (z x) (z y) by
      dsimp [cmp]; split_ifs <;> linarith))
  rw [twice_alignment,twice_alignment] at h
  linarith

end WeinbergerShayevitz
