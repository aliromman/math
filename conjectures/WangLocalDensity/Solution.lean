module

public import conjectures.WangLocalDensity.DoubleBroom
public import conjectures.WangLocalDensity.LeafExtension

public section
namespace WangLocalDensity
open Finset DoubleBroom

/-- The central vertex and the two complementary halves are exactly the maximizers. -/
theorem double_broom_maxima {S : Finset V} (hS : S∈subtrees graph) :
    density graph S ≤ 31/52 ∧
    (density graph S = 31/52 ↔ S = decode 32 ∨ S = decode 14399 ∨ S = decode 116704) := by
  rw [exhaustive] at hS
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hS
  have comp : onMasks (fun b ↦ maskDensity masks b ≤ 31/52 ∧
      (maskDensity masks b = 31/52 ↔ b=32 ∨ b=14399 ∨ b=116704)) := by decide +kernel
  have inject (b : Mask) : decode a = decode b ↔ a=b := (decode_injective 17).eq_iff
  simpa only [density,exhaustive,density_image,inject] using comp a ha

/-- A leafless singleton attains Wang's maximum in a tree with six leaves. -/
theorem resolution : ¬Conjecture := by
  intro H
  let S : Finset V := {5}
  have smask : S=decode 32 := by decide +kernel
  have hS : S∈subtrees graph := by
    simp only [subtrees,mem_filter,mem_powerset,subset_univ,true_and]
    exact singleton_connected 5
  have best := (double_broom_maxima hS).2.mpr (Or.inl smask)
  have bad := H 17 graph tree S hS (by decide +kernel)
    (fun U hU _ ↦ (double_broom_maxima hU).1.trans_eq best.symm)
  obtain ⟨v,hv,hv'⟩ := bad
  have hv : v=5 := mem_singleton.mp hv
  subst v
  obtain ⟨w,_,only⟩ := hv'
  have e := (only 4 (by decide +kernel)).trans (only 6 (by decide +kernel)).symm
  exact (by decide : (4:V)≠6) e

/-- info: 'WangLocalDensity.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'WangLocalDensity.leaf_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaf_extension

end WangLocalDensity
