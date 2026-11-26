module

public import conjectures.ErdosPurdyStraus.Profile
public import conjectures.ErdosPurdyStraus.Slices
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace ErdosPurdyStraus
open Set MeasureTheory

/-- Vertical sections are centered intervals of the proposed width. -/
def body (t : ℝ) : Set Plane := {p | p.1∈Icc 0 1 ∧ |p.2|≤width t p.1/2}

variable {t : ℝ}

private theorem sorted_bound (ht : Parameter t) {p q r : Plane}
    (hp : p∈body t) (hq : q∈body t) (hr : r∈body t) (pq : p.1≤q.1) (qr : q.1≤r.1) :
    |cross p q r|≤1 := by
  have xx := ht.width_upper hp.1
  have yy := ht.width_lower hq.1
  have zz := ht.width_lower hr.1
  have bound := ht.pair_bound hq.1 qr hr.1.2
  have top : (r.1-q.1)*width t p.1+(r.1-p.1)*width t q.1+(q.1-p.1)*width t r.1 ≤ 2 := by
    nlinarith only [bound,mul_le_mul_of_nonneg_left xx (sub_nonneg.mpr qr),mul_nonneg hp.1.1
      (show 0≤width t q.1+width t r.1-(r.1-q.1) by linarith only [yy,zz,hr.1.2])]
  have eq : cross p q r=(r.1-q.1)*p.2+(-(r.1-p.1)*q.2)+(q.1-p.1)*r.2 := by unfold cross; ring
  rw [eq]
  have a := abs_add_le ((r.1-q.1)*p.2) (-(r.1-p.1)*q.2)
  have b := abs_add_le ((r.1-q.1)*p.2+(-(r.1-p.1)*q.2)) ((q.1-p.1)*r.2)
  simp only [abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr pq),abs_of_nonneg (sub_nonneg.mpr qr),
    abs_of_nonneg (sub_nonneg.mpr (pq.trans qr))] at a b
  linarith only [a,b,top,mul_le_mul_of_nonneg_left hp.2 (sub_nonneg.mpr qr),
    mul_le_mul_of_nonneg_left hq.2 (sub_nonneg.mpr (pq.trans qr)),mul_le_mul_of_nonneg_left hr.2 (sub_nonneg.mpr pq)]

private theorem cycle (p q r : Plane) : |cross q r p|=|cross p q r| := by
  congr 1; unfold cross; ring

private theorem swap (p q r : Plane) : |cross q p r|=|cross p q r| := by
  rw [show cross q p r = -cross p q r by unfold cross; ring,abs_neg]

private theorem triangles (ht : Parameter t) {p q r : Plane} (hp : p∈body t) (hq : q∈body t) (hr : r∈body t) :
    |cross p q r|≤1 := by
  rcases le_total p.1 q.1 with pq|qp
  · rcases le_total q.1 r.1 with qr|rq
    · exact sorted_bound ht hp hq hr pq qr
    rcases le_total p.1 r.1 with pr|rp
    · have h := sorted_bound ht hp hr hq pr rq
      rwa [cycle q p r,swap p q r] at h
    · simpa only [←cycle r p q] using sorted_bound ht hr hp hq rp pq
  · rcases le_total p.1 r.1 with pr|rp
    · simpa only [swap p q r] using sorted_bound ht hq hp hr qp pr
    rcases le_total q.1 r.1 with qr|rq
    · simpa only [cycle p q r] using sorted_bound ht hq hr hp qr rp
    · have h := sorted_bound ht hr hq hp rq qp
      rwa [swap q r p,cycle p q r] at h

theorem Parameter.standard_body (ht : Parameter t) : Standard (body t) := by
  have closed : IsClosed (body t) :=
    (isClosed_Icc.preimage continuous_fst).inter (isClosed_le continuous_snd.abs
      (((width_continuous t).comp continuous_fst).div_const 2))
  have compact : IsCompact (body t) := by
    apply (isCompact_Icc.prod (isCompact_Icc (a:=(-1:ℝ)) (b:=1))).of_isClosed_subset closed
    intro p hp
    have hi := ht.width_upper hp.1
    have ab := abs_le.mp hp.2
    exact ⟨hp.1,by constructor <;> linarith [hp.1.2]⟩
  refine ⟨?_,compact,?_,?_,?_,fun p hp ↦ hp.1,fun _ hp _ hq _ hr ↦ triangles ht hp hq hr⟩
  · intro p hp q hq a b ha hb hab
    have h := ht.width_concave.2 hp.1 hq.1 ha hb hab
    have hs := abs_add_le (a*p.2) (b*q.2)
    rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb] at hs
    refine ⟨(convex_Icc (0:ℝ) 1) hp.1 hq.1 ha hb hab,?_⟩
    change |a*p.2+b*q.2|≤width t (a*p.1+b*q.1)/2
    simp only [smul_eq_mul] at h
    linarith only [h,hs,mul_le_mul_of_nonneg_left hp.2 ha,mul_le_mul_of_nonneg_left hq.2 hb]
  · change (0:ℝ)∈Icc 0 1 ∧ |-(1:ℝ)/2|≤width t 0/2
    rw [ht.width_zero]; norm_num
  · change (0:ℝ)∈Icc 0 1 ∧ |(1:ℝ)/2|≤width t 0/2
    rw [ht.width_zero]; norm_num
  · change (1:ℝ)∈Icc 0 1 ∧ |(0:ℝ)|≤width t 1/2
    rw [ht.width_one]; norm_num

theorem Parameter.area_body (ht : Parameter t) : volume.real (body t)=∫ x in (0:ℝ)..1,width t x := by
  rw [ht.standard_body.area]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (zero_le_one : (0:ℝ)≤1)]
  intro x hx
  have pos : 0≤width t x := (sub_nonneg.mpr hx.2).trans (ht.width_lower hx)
  have fiber : Prod.mk x ⁻¹' body t=Icc (-(width t x/2)) (width t x/2) := by
    ext y; exact (and_iff_right hx).trans abs_le
  rw [sectionLength,Measure.real,fiber,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith only [pos])]; ring

theorem Standard.realizes {K : Set Plane} (h : Standard K) : 2*volume.real K∈ratios := by
  have on_boundary {p : Plane} (hp : p∈K) (edge : p.1=0 ∨ p.1=1) : p∈frontier K := by
    apply (mem_frontier_iff_notMem_interior hp).mpr
    intro hi
    have sub : K⊆(Icc (0:ℝ) 1) ×ˢ (univ : Set ℝ) := fun x hx ↦ ⟨h.height x hx,mem_univ _⟩
    have hin := interior_mono sub hi
    rw [interior_prod_eq,interior_Icc] at hin
    exact edge.elim (fun e ↦ (ne_of_gt hin.1.1) e) (fun e ↦ (ne_of_lt hin.1.2) e)
  have area : triangleArea baseLo baseHi apex=1/2 := by norm_num [triangleArea,cross,baseLo,baseHi,apex]
  refine ⟨K,baseLo,baseHi,apex,⟨h.convex,h.compact,h.lo,h.hi,on_boundary h.top (Or.inr rfl),?_,by rw [area]; norm_num,?_⟩,by rw [area]; ring⟩
  · intro p hp
    apply on_boundary (h.convex.segment_subset h.lo h.hi hp) (Or.inl ?_)
    obtain ⟨a,b,_,_,_,rfl⟩ := hp
    simp [baseLo,baseHi,Prod.smul_mk]
  · intro p hp q hq v hv
    rw [area,triangleArea]
    linarith only [h.triangles p hp q hq v hv]

end ErdosPurdyStraus
end
