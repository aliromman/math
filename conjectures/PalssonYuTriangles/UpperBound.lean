module

public import conjectures.PalssonYuTriangles.Regular
import Mathlib.Data.Fintype.EquivFin

@[expose] public section
open Finset
namespace PalssonYu
noncomputable section

theorem types_mono {S T : Finset ℂ} (st : S ⊆ T) : triangleTypes S ⊆ triangleTypes T := by
  intro m hm
  obtain ⟨a,ha,b,hb,c,hc,v⟩ := mem_types.mp hm
  exact mem_types.mpr ⟨a,st ha,b,st hb,c,st hc,v⟩

set_option maxRecDepth 4096 in
/-- Deleting any point from eight cannot always leave a regular heptagon.
A given nonzero distance from a vertex of a heptagon occurs exactly twice. -/
theorem upper_of_seven (S : Finset ℂ)
    (seven : ∀ T ⊆ S, T.card=7 → RegularHeptagon T) : S.card≤7 := by
  classical
  by_contra! big
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α:=Fin 8) (β:=S)
    (by simpa using (show 8≤S.card by omega))
  let p (i : Fin 8) : ℂ := e i
  have inj : Function.Injective p := Subtype.val_injective.comp e.injective
  let f (j : Fin 8) := decide (D (p 0) (p j)=D (p 0) (p 1))
  have first : f 0=false := by
    have pos := D_pos (inj.ne (by decide : (0:Fin 8)≠1))
    simpa [f,D] using (show ¬D (p 0) (p 0)=D (p 0) (p 1) by simpa [D] using pos.ne)
  have second : f 1=true := by simp [f]
  have impossible : ∀ b : Fin 8 → Bool, b 0=false → b 1=true →
      ¬∀ t : Fin 8, t≠0 → t≠1 → ((univ.erase t).filter (fun i => b i=true)).card=2 := by decide
  apply impossible f first second
  intro t t0 t1
  let U := (univ.erase t).image p
  have se := seven U (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact (e i).property) (by simp [U,card_image_of_injective _ inj])
  have n := twice_at_vertex se (mem_image_of_mem p (mem_erase_of_ne_of_mem t0.symm (mem_univ _)))
    (mem_image_of_mem p (mem_erase_of_ne_of_mem t1.symm (mem_univ _)))
    (inj.ne (by decide : (0:Fin 8)≠1))
  simp only [U,filter_image,card_image_of_injective _ inj] at n
  simpa only [f,decide_eq_true_eq] using n

end
end PalssonYu
