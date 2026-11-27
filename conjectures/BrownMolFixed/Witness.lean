module

public import conjectures.BrownMolFixed.Probability
import Mathlib.Data.Rat.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

@[expose] public section
namespace BrownMolFixed
open Finset

/-- The layers contain 36 vertices. Layers one and eight give the two cut vertices. -/
def sizes : Fin 10→ℕ := ![1,1,5,5,5,5,8,4,1,1]

private theorem available : Connected (chain sizes) (fun _ ↦ true) := by
  rw [connected_iff];decide +kernel

private def firstCut : Vertex sizes := ⟨1,⟨0,by decide⟩⟩
private def lastCut : Vertex sizes := ⟨8,⟨0,by decide⟩⟩

private theorem cuts : ∃ u v,u≠v ∧ Cut (chain sizes) u ∧ Cut (chain sizes) v := by
  refine ⟨firstCut,lastCut,by decide,?_,?_⟩
  · apply cut_of_disconnect (u:=lastCut) available (by decide)
    rw [connected_iff];decide +kernel
  · apply cut_of_disconnect (u:=firstCut) available (by decide)
    rw [connected_iff];decide +kernel

private theorem rational_value {n : ℕ} (w : Fin n→ℕ) (p : ℚ) :
    ((layerValue w p : ℚ):ℝ)=layerValue w (p:ℝ) := by
  unfold layerValue
  push_cast
  apply sum_congr rfl
  intro f _
  split_ifs <;> simp
  apply prod_congr rfl
  intro i _
  split_ifs <;> push_cast <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem signs :
    (1/8 : ℚ)<layerValue sizes (1/8) ∧ layerValue sizes (1/4)<(1/4 : ℚ) ∧
    (1/3 : ℚ)<layerValue sizes (1/3) ∧ layerValue sizes (1/2)<(1/2 : ℚ) := by decide +kernel

/-- A path of ten cliques has fixed points in three disjoint, explicit intervals. -/
theorem three : ∃ x∈Set.Ioo (1/8:ℝ) (1/4), ∃ y∈Set.Ioo (1/4:ℝ) (1/3), ∃ z∈Set.Ioo (1/3:ℝ) (1/2),
    reliability (chain sizes) x=x ∧ reliability (chain sizes) y=y ∧ reliability (chain sizes) z=z := by
  have ⟨s,t,u,v⟩ := signs
  have a := Rat.cast_lt (K:=ℝ).mpr s
  have b := Rat.cast_lt (K:=ℝ).mpr t
  have c := Rat.cast_lt (K:=ℝ).mpr u
  have d := Rat.cast_lt (K:=ℝ).mpr v
  simp only [rational_value,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at a b c d
  let f (p : ℝ) := layerValue sizes p-p
  have hf : Continuous f := (continuous_value sizes).sub continuous_id
  obtain ⟨x,hx,ex⟩ := root_between (by norm_num : (1/8:ℝ)<1/4) hf (.inr ⟨sub_pos.mpr a,sub_neg.mpr b⟩)
  obtain ⟨y,hy,ey⟩ := root_between (by norm_num : (1/4:ℝ)<1/3) hf (.inl ⟨sub_neg.mpr b,sub_pos.mpr c⟩)
  obtain ⟨z,hz,ez⟩ := root_between (by norm_num : (1/3:ℝ)<1/2) hf (.inr ⟨sub_pos.mpr c,sub_neg.mpr d⟩)
  exact ⟨x,hx,y,hy,z,hz,(reliability_chain sizes x).trans (sub_eq_zero.mp ex),
    (reliability_chain sizes y).trans (sub_eq_zero.mp ey),(reliability_chain sizes z).trans (sub_eq_zero.mp ez)⟩

theorem resolution : ¬Conjecture := by
  intro h
  obtain ⟨p,_,unique⟩ := h _ (chain sizes) cuts
  obtain ⟨x,hx,y,hy,z,_,ex,ey,_⟩ := three
  have xp := unique x ⟨⟨(by norm_num : (0:ℝ)<1/8).trans hx.1,hx.2.trans (by norm_num)⟩,ex⟩
  have yp := unique y ⟨⟨(by norm_num : (0:ℝ)<1/4).trans hy.1,hy.2.trans (by norm_num)⟩,ey⟩
  exact (hx.2.trans hy.1).ne (xp.trans yp.symm)

/-- info: 'BrownMolFixed.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end BrownMolFixed
