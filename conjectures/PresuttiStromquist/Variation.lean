module

public import conjectures.PresuttiStromquist.Root
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace PresuttiStromquist
open Set MeasureTheory Filter
open scoped Topology

theorem three_ae {μ : Measure Point} [IsFiniteMeasure μ] {P : Point → Prop} (h : ∀ᵐ u ∂μ, P u) :
    ∀ᵐ v ∂draws μ, P v.1 ∧ P v.2.1 ∧ P v.2.2 := by
  have hpair : ∀ᵐ v ∂μ.prod μ, P v.1 ∧ P v.2 :=
    (Measure.quasiMeasurePreserving_fst.ae h).and (Measure.quasiMeasurePreserving_snd.ae h)
  exact (Measure.quasiMeasurePreserving_fst.ae h).and (Measure.quasiMeasurePreserving_snd.ae hpair)

def same (p q u : Point) : Prop :=
  (q.1<u.1 ↔ p.1<u.1) ∧ (u.1<q.1 ↔ u.1<p.1) ∧ (q.2<u.2 ↔ p.2<u.2) ∧ (u.2<q.2 ↔ u.2<p.2)

private theorem comparisons (x u : ℝ) (h : u≠x) :
    ∀ᶠ q in 𝓝 x, (q<u ↔ x<u) ∧ (u<q ↔ u<x) := by
  rcases lt_or_gt_of_ne h with pos|neg
  · filter_upwards [Ioi_mem_nhds pos] with q hq
    exact ⟨iff_of_false hq.not_gt pos.not_gt,iff_of_true hq pos⟩
  · filter_upwards [Iio_mem_nhds neg] with q hq
    exact ⟨iff_of_true hq neg,iff_of_false hq.not_gt neg.not_gt⟩

private theorem same_near (p u : Point) (h : u.1≠p.1 ∧ u.2≠p.2) :
    ∀ᶠ q in 𝓝 p, same p q u := by
  have e := continuous_fst.continuousAt.tendsto.eventually (comparisons p.1 u.1 h.1)
  have f := continuous_snd.continuousAt.tendsto.eventually (comparisons p.2 u.2 h.2)
  filter_upwards [e,f] with q a b
  exact ⟨a.1,a.2,b⟩

theorem occurs_same (i : Fin 4) (p q : Point) (v : Triple)
    (a : same p q v.1) (b : same p q v.2.1) (c : same p q v.2.2) :
    occurs i q v = occurs i p v := by
  have eq : insertPoint i (q,v)∈event ↔ insertPoint i (p,v)∈event := by
    rcases a with ⟨a₁,a₂,a₃,a₄⟩; rcases b with ⟨b₁,b₂,b₃,b₄⟩; rcases c with ⟨c₁,c₂,c₃,c₄⟩
    fin_cases i <;> simp only [insertPoint,event,mem_ofPred_eq] <;> simp_all only
  classical
  by_cases h : insertPoint i (p,v)∈event
  · simp [occurs,h,eq.mpr h]
  · simp [occurs,h,mt eq.mp h]

/-- Moving the distinguished point is continuous when its coordinate lines have zero mass. -/
theorem continuousAt_link {μ : Measure Point} [IsFiniteMeasure μ] {p : Point}
    (h : ∀ᵐ u ∂μ, u.1≠p.1 ∧ u.2≠p.2) : ContinuousAt (link μ) p := by
  have each (i : Fin 4) : ContinuousAt (atPosition μ i) p := by
    apply continuousAt_of_dominated (bound:=fun _ ↦ (1:ℝ))
    · exact .of_forall fun q ↦ ((measurable_occurs i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · exact .of_forall fun q ↦ .of_forall fun v ↦ norm_occurs i q v
    · exact integrable_const 1
    · filter_upwards [three_ae h] with v hv
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [same_near p v.1 hv.1,same_near p v.2.1 hv.2.1,same_near p v.2.2 hv.2.2] with q a b c
      exact occurs_same i p q v a b c
  change ContinuousAt (fun q ↦ ∑ i : Fin 4, atPosition μ i q) p
  simp only [Fin.sum_univ_four]
  exact (((each 0).add (each 1)).add (each 2)).add (each 3)

theorem Optimal.stationary {μ : Measure Point} (opt : Optimal μ) :
    ∀ᵐ p ∂μ, link μ p = 4*mixed μ μ μ μ := by
  let : IsProbabilityMeasure μ := opt.1
  have inSquare : ∀ᵐ p ∂μ, p∈square := ae_iff.mpr opt.2.1
  have bound : link μ ≤ᵐ[μ] fun _ ↦ 4*mixed μ μ μ μ := by
    filter_upwards [inSquare] with p hp
    have zo : (Measure.dirac p) squareᶜ=0 := by
      rw [Measure.dirac_apply']; simp [hp]
      exact ((isClosed_Icc.prod isClosed_Icc).measurableSet.compl)
    have e := opt.linear_le (ν:=Measure.dirac p) zo
    rwa [←link_integral,integral_dirac] at e
  apply (integral_eq_iff_of_ae_le (integrable_link μ μ) (integrable_const _) bound).mp
  rw [link_integral,integral_const]
  simp [linearTerm]
  ring

theorem Optimal.support_link {μ : Measure Point} (opt : Optimal μ) {p : Point}
    (support : ∀ U ∈ 𝓝 p, μ U ≠ 0) (avoid : ∀ᵐ u ∂μ, u.1≠p.1 ∧ u.2≠p.2) :
    link μ p = 4*mixed μ μ μ μ := by
  let : IsProbabilityMeasure μ := opt.1
  by_contra h
  let N := {q | link μ q ≠ 4*mixed μ μ μ μ}
  have nb : N∈𝓝 p := (continuousAt_link avoid) (isOpen_compl_singleton.mem_nhds h)
  exact support N nb (ae_iff.mp opt.stationary)

end PresuttiStromquist
end
