module

public import conjectures.SavchenkoSix.Pfaffians
public import conjectures.SavchenkoSix.Moments

@[expose] public section
noncomputable section
namespace SavchenkoSix
open Finset Matrix

/-- Each four-vertex principal Pfaffian is the signed sum of three units. -/
theorem four_nonneg {n : ℕ} (T : Tournament (Fin n)) : 0≤excessOn T.sign univ 4 := by
  apply sum_nonneg
  intro s hs
  let e := s.orderIsoOfFin (mem_powersetCard.mp hs).2
  let f : Fin 4→Fin n := fun i ↦ e i
  have inj : Function.Injective f := Subtype.val_injective.comp e.injective
  let B := T.sign.submatrix f f
  have unit (i j : Fin 4) (h : i≠j) : B i j=1 ∨ B i j= -1 := by
    change T.sign (f i) (f j)=1 ∨ T.sign (f i) (f j)= -1
    simp only [Tournament.sign,inj.ne h,ite_false]
    split <;> simp
  have prod (i j k l : Fin 4) (h : i≠j) (h' : k≠l) :
      B i j*B k l=1 ∨ B i j*B k l= -1 := by
    rcases unit i j h with u|u <;> rcases unit k l h' with v|v <;> rw [u,v] <;> decide
  unfold excess
  rw [←det_submatrix_equiv_self e.toEquiv]
  change 0≤B.det-1
  rw [det_skew4 B (fun i j ↦ sign_flip T (f i) (f j))]
  unfold pf4
  rcases prod 0 1 2 3 (by decide) (by decide) with a|a <;>
    rcases prod 0 2 1 3 (by decide) (by decide) with b|b <;>
    rcases prod 0 3 1 2 (by decide) (by decide) with c|c <;> rw [a,b,c] <;> decide

end SavchenkoSix
end
