module

public import conjectures.PresuttiStromquist.Density
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
namespace PresuttiStromquist
open MeasureTheory Set
open scoped NNReal ENNReal

theorem mixed_mono {a b c d A B C D : Measure Point}
    [IsFiniteMeasure A] [IsFiniteMeasure B] [IsFiniteMeasure C] [IsFiniteMeasure D]
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) :
    mixed a b c d ≤ mixed A B C D := by
  apply ENNReal.toReal_mono (by finiteness)
  exact (Measure.prod_mono ha (Measure.prod_mono hb (Measure.prod_mono hc hd))) event

/-- Four atoms arranged in the target order give a positive packing rate. -/
theorem Optimal.positive {μ : Measure Point} (h : Optimal μ) : 0 < mixed μ μ μ μ := by
  let p : Fin 4 → Point := ![(1/5,2/5),(2/5,4/5),(3/5,1/5),(4/5,3/5)]
  let M : Measure Point := ∑ i : Fin 4, Measure.dirac (p i)
  let c : ℝ≥0 := 1/4
  let ν : Measure Point := c • M
  have hM : IsFiniteMeasure M := by dsimp [M]; infer_instance
  have hν : IsProbabilityMeasure ν := by
    constructor
    simp [ν,M,c,ENNReal.smul_def,sum_apply]
    exact ENNReal.inv_mul_cancel (by norm_num) (by finiteness)
  have hs : ν squareᶜ = 0 := by
    simp [ν,M, Fin.sum_univ_four, p, square]
    norm_num
  have mono (i : Fin 4) : Measure.dirac (p i) ≤ M := by
    apply Measure.le_iff'.mpr
    intro s
    dsimp [M]
    rw [sum_apply]
    exact Finset.single_le_sum (f := fun j => Measure.dirac (p j) s) (fun _ _ => zero_le) (Finset.mem_univ i)
  have hm := mixed_mono (mono 0) (mono 1) (mono 2) (mono 3)
  have hv : (1:ℝ) ≤ mixed M M M M := by
    convert hm using 1
    simp [mixed, Measure.real, Measure.dirac_prod_dirac, event,p]
    norm_num
  have H := h.2.2 ν hν hs
  unfold rate at H
  rw [show ν = c • M from rfl, mixed_smul] at H
  norm_num [c] at H
  linarith

end PresuttiStromquist
end
