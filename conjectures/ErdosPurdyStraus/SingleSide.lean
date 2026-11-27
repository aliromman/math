module

public import conjectures.ErdosPurdyStraus.Extremizer
import Mathlib.Tactic.Linarith

public section
namespace ErdosPurdyStraus
open Set

/-- Each sloping side of the maximizing triangle passes through the interior. -/
theorem Parameter.single_side {t : ℝ} (ht : Parameter t) :
    ¬segment ℝ baseLo apex ⊆ frontier (body t) ∧ ¬segment ℝ baseHi apex ⊆ frontier (body t) := by
  let O : Set Plane := {p | p.1∈Ioo 0 1 ∧ |p.2|<width t p.1/2}
  have op : IsOpen O := (isOpen_Ioo.preimage continuous_fst).inter (isOpen_lt continuous_snd.abs
    (((width_continuous t).comp continuous_fst).div_const 2))
  have incl : O⊆interior (body t) := interior_maximal (fun p hp ↦ ⟨⟨hp.1.1.le,hp.1.2.le⟩,hp.2.le⟩) op
  have line (b : ℝ) (hb : |b|=1/2) : ¬segment ℝ ((0,b):Plane) apex ⊆ frontier (body t) := by
    intro h
    let p : Plane := (t,(1-t)*b)
    have t1 : t<1 := by linarith [ht.2.1]
    have contained : p∈segment ℝ ((0,b):Plane) apex := by
      refine ⟨1-t,t,sub_nonneg.mpr t1.le,ht.1.le,by ring,?_⟩
      ext <;> simp [p,apex,Prod.smul_mk,smul_eq_mul]
    have mem : p∈O := by
      refine ⟨⟨ht.1,t1⟩,?_⟩
      change |(1-t)*b|<width t t/2
      rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr t1.le),hb,ht.width_low le_rfl]
      linarith only [ht.1]
    exact (h contained).2 (incl mem)
  exact ⟨line _ (by norm_num),line _ (by norm_num)⟩

end ErdosPurdyStraus
