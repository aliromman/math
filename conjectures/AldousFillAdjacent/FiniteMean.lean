module

public import conjectures.AldousFillAdjacent.Poincare
public import conjectures.AldousFillAdjacent.Hitting
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith

@[expose] public section
namespace AldousFillAdjacent
open Finset Filter
open scoped BigOperators Matrix Topology

variable {m : ℕ}

private noncomputable def fixedBoundary (m : ℕ) : (Deck m → ℝ) →ₗ[ℝ] (Deck m → ℝ) where
  toFun f x := if x=1 then f x else L m f x
  map_add' f g := by ext x; by_cases e : x=1 <;> simp [e]; ring
  map_smul' a f := by ext x; by_cases e : x=1 <;> simp [e]

private theorem fixed_injective : Function.Injective (fixedBoundary m) := by
  apply (injective_iff_map_eq_zero _).2
  intro f eq
  have val (x : Deck m) := congrFun eq x
  have zero : f 1=0 := by simpa [fixedBoundary] using val 1
  have off (x : Deck m) (hx : x≠1) : L m f x=0 := by
    simpa only [fixedBoundary,LinearMap.coe_mk,AddHom.coe_mk,hx,↓reduceIte,Pi.zero_apply] using val x
  have eL : L m f=0 := by
    ext x
    by_cases hx : x=1
    · subst x
      have sums : ∑ x, L m f x=0 := by change ∑ x, (f x-P m f x)=0; simp [sum_sub_distrib,sum_P]
      rwa [sum_eq_single_of_mem 1 (mem_univ _) fun y _ hy ↦ off y hy] at sums
    · exact off _ hx
  ext g
  exact (energy_zero (by rw [eL];simp) g).trans zero

private theorem bounded (m : ℕ) : BddAbove (Set.range (mean m)) := by
  obtain ⟨h,hh⟩ := LinearMap.surjective_of_injective fixed_injective
    (fun x : Deck m ↦ if x=1 then (0:ℝ) else 1)
  have h0 : h 1=0 := by simpa [fixedBoundary] using congrFun hh 1
  have hs (x : Deck m) (hx : x≠1) : h x=1+P m h x := by
    have e := congrFun hh x
    simp only [fixedBoundary,LinearMap.coe_mk,AddHom.coe_mk,hx,↓reduceIte] at e
    change h x-P m h x=1 at e
    linarith
  obtain ⟨z,_,hz⟩ := (univ : Finset (Deck m)).exists_min_image h univ_nonempty
  have nn (x : Deck m) : 0≤h x := by
    have low := hz x (mem_univ _)
    by_cases he : z=1
    · simpa [he,h0] using low
    · have e := hs z he
      have av : h z≤P m h z := (expect_const univ_nonempty _).symm.le.trans
        (expect_le_expect fun i _ ↦ hz (z*move i) (mem_univ _))
      linarith
  have upper (t : ℕ) (x : Deck m) : stopped m t 1 x≤h x := by
    induction t generalizing x with
    | zero => exact nn x
    | succ t ih =>
      by_cases hx : x=1
      · simp [stopped,hx,h0]
      · rw [stopped,ite_eq_right hx,hs x hx]
        exact add_le_add_right (expect_le_expect fun i _ ↦ ih (x*move i)) _
  refine ⟨𝔼 x, h x,?_⟩
  rintro _ ⟨t,rfl⟩
  rw [mean_fixed]
  exact expect_le_expect fun x _ ↦ upper t x

/-- The full mean first hitting time between independent uniform decks. -/
noncomputable def stationaryTime (m : ℕ) : ℝ := ⨆ t, mean m t

theorem mean_tendsto (m : ℕ) : Tendsto (mean m) atTop (𝓝 (stationaryTime m)) := by
  apply tendsto_atTop_ciSup _ (bounded m)
  intro a b hab
  rw [mean_fixed,mean_fixed]
  exact expect_le_expect fun x _ ↦ stopped_mono 1 x hab

end AldousFillAdjacent
