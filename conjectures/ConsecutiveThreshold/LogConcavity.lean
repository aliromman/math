module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace ConsecutiveThreshold
open Finset
open scoped BigOperators

/-- A finite, nonnegative mass function on the integers. -/
structure Mass where
  w : ℤ → ℝ
  sites : Finset ℤ
  nonneg : ∀ i, 0≤w i
  zero_off : ∀ i, i∉sites → w i=0

namespace Mass

noncomputable def total (f : Mass) : ℝ := ∑ i∈f.sites,f.w i

def balanced (f : ℤ → ℝ) : Prop :=
  ∀ a b d : ℤ, a≤b → 0≤d → f a*f (b+d) ≤ f (a+d)*f b

noncomputable def conv (f g : Mass) : Mass where
  w r := ∑ i∈f.sites, f.w i*g.w (r-i)
  sites := (f.sites ×ˢ g.sites).image (fun z ↦ z.1+z.2)
  nonneg r := sum_nonneg fun i _ ↦ mul_nonneg (f.nonneg i) (g.nonneg _)
  zero_off r missing := by
    apply sum_eq_zero
    intro i hi
    rw [g.zero_off (r-i) (fun hr ↦ missing (mem_image.mpr
      ⟨(i,r-i),mem_product.mpr ⟨hi,hr⟩,by dsimp; omega⟩)),mul_zero]

theorem conv_on (f g : Mass) (r u : ℤ) (S : Finset ℤ)
    (cover : ∀ x∈f.sites,x+u∈S) :
    (conv f g).w (r-u)=∑ i∈S,f.w (i-u)*g.w (r-i) := by
  let E := f.sites.image (fun x ↦ x+u)
  have hE : E⊆S := by
    intro i hi
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
    exact cover x hx
  have a : ∑ i∈E,f.w (i-u)*g.w (r-i) = (conv f g).w (r-u) := by
    rw [sum_image (fun x _ y _ h ↦ add_right_cancel h)]
    apply sum_congr rfl
    intro x _
    rw [add_sub_cancel_right,show r-(x+u)=r-u-x by omega]
  rw [←a]
  apply sum_subset hE
  intro i _ no
  rw [f.zero_off (i-u) (fun hh ↦ no (mem_image.mpr ⟨i-u,hh,by omega⟩)),zero_mul]

private theorem cross_sum {α : Type*} (S : Finset α) (u v x y : α → ℝ) :
    ∑ i∈S, ∑ j∈S,(u i*v j-u j*v i)*(x i*y j-x j*y i) =
      2*((∑ i∈S,u i*x i)*(∑ j∈S,v j*y j)-(∑ i∈S,u i*y i)*(∑ j∈S,v j*x j)) := by
  have split (i j : α) :
      (u i*v j-u j*v i)*(x i*y j-x j*y i) =
        (u i*x i)*(v j*y j) - (u i*y i)*(v j*x j) -
        (v i*x i)*(u j*y j) + (v i*y i)*(u j*x j) := by ring
  simp_rw [split,sum_add_distrib,sum_sub_distrib,← mul_sum,← sum_mul]
  ring

/-- Convolution preserves the two-by-two determinant inequalities. -/
theorem balanced_conv (f g : Mass) (hf : balanced f.w) (hg : balanced g.w) :
    balanced (conv f g).w := by
  intro a b d ab hd
  let S := f.sites ∪ f.sites.image (fun i ↦ i+d)
  let u := f.w
  let v := fun i ↦ f.w (i-d)
  let x := fun i ↦ g.w (a+d-i)
  let y := fun i ↦ g.w (b+d-i)
  have cov0 (i : ℤ) (hi : i∈f.sites) : i+0∈S := by simpa only [add_zero] using (mem_union_left (f.sites.image (fun i ↦ i+d)) hi)
  have covd (i : ℤ) (hi : i∈f.sites) : i+d∈S := mem_union_right _ (mem_image_of_mem _ hi)
  have ux : (conv f g).w (a+d)=∑ i∈S,u i*x i := by simpa [u,x] using conv_on f g (a+d) 0 S cov0
  have uy : (conv f g).w (b+d)=∑ i∈S,u i*y i := by simpa [u,y] using conv_on f g (b+d) 0 S cov0
  have vx : (conv f g).w a=∑ i∈S,v i*x i := by simpa [v,x] using conv_on f g (a+d) d S covd
  have vy : (conv f g).w b=∑ i∈S,v i*y i := by simpa [v,y] using conv_on f g (b+d) d S covd
  have sign (i j : ℤ) (ord : i≤j) : 0≤u i*v j-u j*v i ∧ 0≤x i*y j-x j*y i := by
    constructor
    · have e := hf (i-d) (j-d) d (by omega) hd
      simpa [u,v,sub_nonneg,mul_comm] using e
    · have e := hg (a+d-j) (b+d-j) (j-i) (by omega) (by omega)
      have h₁ : a+d-j+(j-i)=a+d-i := by omega
      have h₂ : b+d-j+(j-i)=b+d-i := by omega
      simpa [x,y,h₁,h₂,sub_nonneg,mul_comm] using e
  have det : 0≤∑ i∈S, ∑ j∈S,(u i*v j-u j*v i)*(x i*y j-x j*y i) := by
    refine sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ ?_
    rcases le_total i j with h|h
    · exact mul_nonneg (sign i j h).1 (sign i j h).2
    · obtain ⟨c,e⟩ := sign j i h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  rw [cross_sum] at det
  rw [ux,uy,vx,vy]
  linarith

end Mass
end ConsecutiveThreshold
