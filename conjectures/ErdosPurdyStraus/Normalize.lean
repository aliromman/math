module

public import conjectures.ErdosPurdyStraus.Support
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace ErdosPurdyStraus
open MeasureTheory Set
noncomputable section

/-- The affine coordinates of a largest triangle preserve its area ratio. -/
theorem normalize {K : Set Plane} {a b c : Plane} (h : Admissible K a b c) :
    ∃ B, Standard B ∧ volume.real K / triangleArea a b c = 2*volume.real B := by
  let o : Plane := ((a.1+b.1)/2,(a.2+b.2)/2)
  let u := c-o
  let v := b-a
  let L : Plane →ₗ[ℝ] Plane := Matrix.toLin (Module.Basis.finTwoProd ℝ)
    (Module.Basis.finTwoProd ℝ) !![u.1,v.1;u.2,v.2]
  have coordinates (z : Plane) : L z = (u.1*z.1+v.1*z.2,u.2*z.1+v.2*z.2) :=
    Matrix.toLin_finTwoProd_apply ..
  have det : LinearMap.det L = -cross a b c := by
    simp [L,LinearMap.det_toLin,Matrix.det_fin_two,cross,u,v,o]
    ring
  have pos := h.positive
  have detne : LinearMap.det L ≠ 0 := by
    rw [det,neg_ne_zero]
    intro e
    simp [triangleArea,e] at pos
  let E := ((L.equivOfDetNeZero detne).toContinuousLinearEquiv.toHomeomorph).trans (Homeomorph.addLeft o)
  let B := E ⁻¹' K
  have eval (p : Plane) : E p=o+L p := rfl
  have img (p : Plane) : E p=(o.1+u.1*p.1+v.1*p.2,o.2+u.2*p.1+v.2*p.2) := by
    rw [eval,coordinates]
    ext <;> dsimp <;> ring
  have lo : E baseLo=a := by rw [img]; ext <;> simp [o,u,v] <;> ring
  have hi : E baseHi=b := by rw [img]; ext <;> simp [o,u,v] <;> ring
  have top : E apex=c := by rw [img]; ext <;> simp [o,u,v]
  have cv : Convex ℝ B := by
    intro p hp q hq α β hα hβ hab
    change E (α • p+β • q)∈K
    have e : E (α • p+β • q)= α • E p+β • E q := by
      simp only [eval,map_add,map_smul,smul_add]
      calc
        _ = (α • o+β • o)+(α • L p+β • L q) := by rw [←add_smul,hab,one_smul]
        _ = _ := by abel
    exact e ▸ h.convex hp hq hα hβ hab
  have cmem : c∈K := h.compact.isClosed.closure_eq ▸ frontier_subset_closure h.c_mem
  have bl : baseLo∈B := by change E baseLo∈K; rw [lo]; exact h.a_mem
  have bh : baseHi∈B := by change E baseHi∈K; rw [hi]; exact h.b_mem
  have bt : apex∈B := by change E apex∈K; rwa [top]
  have edge : (0:Plane)∉interior B := by
    have midpoint : o∈frontier K := by
      apply h.side
      refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
      ext <;> dsimp [o] <;> ring
    change (0:Plane) ∉ interior (E ⁻¹' K)
    rw [←E.preimage_interior,mem_preimage,eval,map_zero,add_zero]
    exact midpoint.2
  have oriented (p q r : Plane) : cross (E p) (E q) (E r)=(-cross a b c)*cross p q r := by
    simp only [img,cross,u,v,o,Prod.fst_sub,Prod.snd_sub]
    ring
  have triangles (p : Plane) (hp:p∈B) (q : Plane) (hq:q∈B) (r : Plane) (hr:r∈B) :
      |cross p q r|≤1 := by
    have H := h.largest (E p) hp (E q) hq (E r) hr
    simp only [triangleArea,oriented,abs_mul,abs_neg] at H
    have A : 0 < |cross a b c| := by dsimp [triangleArea] at pos; linarith
    apply (mul_le_mul_iff_right₀ A).mp
    linarith
  refine ⟨B,⟨cv,E.isCompact_preimage.mpr h.compact,bl,bh,bt,?_,triangles⟩,?_⟩
  · intro p hp
    refine ⟨supported cv bl bh bt edge p hp,?_⟩
    have t := triangles baseLo bl baseHi bh p hp
    have E : cross baseLo baseHi p = -p.1 := by simp [cross]; ring
    rw [E,abs_neg] at t
    exact (le_abs_self p.1).trans t
  · have : (volume : Measure Plane).IsAddHaarMeasure :=
      inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod volume))
    have pre : K = (fun z : Plane => -o+z) ⁻¹' (L '' B) := by
      ext z
      constructor
      · intro hz
        refine ⟨E.symm z,?_,?_⟩
        · change E (E.symm z)∈K
          rwa [E.apply_symm_apply]
        · have id := E.apply_symm_apply z
          rw [eval] at id
          exact eq_neg_add_of_add_eq id
      · rintro ⟨y,hy,eq⟩
        change E y ∈ K at hy
        rw [eval,eq] at hy
        simpa using hy
    have scale : volume.real K = |cross a b c| * volume.real B := by
      unfold Measure.real
      rw [pre, measure_preimage_add, Measure.addHaar_image_linearMap,
        ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _),det,abs_neg]
    rw [scale,triangleArea]
    have A : 0 < |cross a b c| := by dsimp [triangleArea] at pos; linarith
    field_simp

end
end ErdosPurdyStraus
