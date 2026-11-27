module

public import conjectures.McCuneSeatJumps.Cells
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
open MeasureTheory Finset Set
namespace McCuneSeatJumps

/-- The two coordinates compare the other population shares to state i. -/
def box (i : Fin 3) (u U v V : ℝ) : Set (ℝ × ℝ) := {x |
  shares x (i+1)-shares x i ∈ Ioo u U ∧ shares x (i+2)-shares x i ∈ Ioo v V}

theorem open_box (i : Fin 3) (u U v V : ℝ) : IsOpen (box i u U v V) :=
  (isOpen_Ioo.preimage ((continuous_shares _).sub (continuous_shares i))).inter
    (isOpen_Ioo.preimage ((continuous_shares _).sub (continuous_shares i)))

private def mat (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![-1,1;-2,-1], !![-1,-2;1,-1], !![2,1;1,2]] i

private def offset (i : Fin 3) : Fin 2 → ℝ := ![![0,1],![1,0],![-1,-1]] i

/-- Population differences have Jacobian determinant three for each choice of loser. -/
theorem volume_box (i : Fin 3) (u U v V : ℝ) :
    volume (box i u U v V) = ENNReal.ofReal (1/3:ℝ) *
      ENNReal.ofReal (U-u) * ENNReal.ofReal (V-v) := by
  let S : Set (Fin 2 → ℝ) := Set.univ.pi
    ![Ioo (u-offset i 0) (U-offset i 0),Ioo (v-offset i 1) (V-offset i 1)]
  let f := Matrix.toLin' (mat i)
  have hd : LinearMap.det f = 3 := by
    rw [LinearMap.det_toLin']; fin_cases i <;> norm_num [mat, Matrix.det_fin_two]
  have eq : MeasurableEquiv.finTwoArrow ⁻¹' box i u U v V = f ⁻¹' S := by
    ext w
    have hpi (t : Fin 2 → ℝ) : t ∈ S ↔
        t 0 ∈ Ioo (u-offset i 0) (U-offset i 0) ∧
        t 1 ∈ Ioo (v-offset i 1) (V-offset i 1) := by
      simp [S,Set.mem_pi,Fin.forall_fin_two]
    change _ ↔ f w ∈ S
    rw [hpi]
    change (_ < _ ∧ _ < _) ∧ _ < _ ∧ _ < _ ↔ (_ < _ ∧ _ < _) ∧ _ < _ ∧ _ < _
    fin_cases i <;>
      norm_num [shares,offset,mat,f,Matrix.toLin'_apply,Matrix.mulVec,
        dotProduct,Fin.sum_univ_two,MeasurableEquiv.finTwoArrow] <;>
      constructor <;> rintro ⟨⟨a,b⟩,c,d⟩ <;> refine ⟨⟨?_,?_⟩,?_,?_⟩ <;> linarith
  rw [← (volume_preserving_finTwoArrow ℝ).measure_preimage_equiv,eq,
    Measure.addHaar_preimage_linearMap volume (by rw [hd]; norm_num)]
  simp [hd,S,volume_pi_pi,Fin.prod_univ_two,Real.volume_Ioo,mul_assoc]

end McCuneSeatJumps
