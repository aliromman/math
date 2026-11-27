module

public import conjectures.PresuttiStromquist.Density
public import conjectures.PresuttiStromquist.RangeCount
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
namespace PresuttiStromquist
namespace Discrete
open MeasureTheory Set
open scoped NNReal ENNReal

/-- Coordinate ranks give points inside the unit square. -/
def coordinate (x : ℕ) : ℝ := (x:ℝ)/((x:ℝ)+1)

private theorem increasing : StrictMono coordinate := by
  intro a b h
  have H : (a:ℝ)<b := by exact_mod_cast h
  unfold coordinate
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

def point (p : Pos) : Point := (coordinate p.1, coordinate p.2)

theorem point_mem (p : Pos) : point p ∈ square := by
  have H (n : ℕ) : coordinate n ∈ Icc (0:ℝ) 1 :=
    ⟨by unfold coordinate; positivity, by
      unfold coordinate
      apply (div_le_iff₀ (by positivity)).mpr
      linarith⟩
  exact ⟨H _,H _⟩

def Cloud.law : Cloud → Measure Point
  | .leaf p w => (w : ℝ≥0) • Measure.dirac (point p)
  | .node _ a b => a.law+b.law

instance (c : Cloud) : IsFiniteMeasure c.law := by
  induction c with
  | leaf p w => change IsFiniteMeasure ((w:ℝ≥0) • Measure.dirac (point p)); infer_instance
  | node f a b ia ib => change IsFiniteMeasure (a.law+b.law); infer_instance

theorem Cloud.support (c : Cloud) : c.law squareᶜ=0 := by
  induction c with
  | leaf p w =>
    have z : Measure.dirac (point p) squareᶜ = 0 :=
      by simp [Measure.dirac_apply,show (point p ∈ square) from point_mem p]
    simp [law,z]
  | node f a b ia ib => simp [law,ia,ib]

theorem Cloud.total (c : Cloud) (h : c.valid) : c.law univ=c.frame.weight := by
  induction c with
  | leaf p w => simp [law,frame,ENNReal.smul_def]
  | node f a b ia ib =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨rfl,ha⟩,hb⟩
    simp [law, frame, Frame.union, ia ha, ib hb]

private theorem fold_measure (c : Cloud) (F : Measure Point → ℝ)
    (add : ∀ a b : Cloud, F (a.law+b.law)=F a.law+F b.law)
    (smul : ∀ (p : Pos) (w : ℕ), F ((w:ℝ≥0) • Measure.dirac (point p)) =
      w • F (Measure.dirac (point p))) :
    F c.law = c.fold (fun p => F (Measure.dirac (point p))) := by
  induction c with
  | leaf p w => exact smul p w
  | node f a b ia ib => simp [Cloud.law,Cloud.fold,add,ia,ib]

private theorem first (a : Cloud) (b c d : Measure Point) [IsFiniteMeasure b]
    [IsFiniteMeasure c] [IsFiniteMeasure d] :
    mixed a.law b c d = a.fold (fun p => mixed (Measure.dirac (point p)) b c d) := by
  apply fold_measure a (fun x => mixed x b c d)
  · intros; simp (disch := finiteness) [mixed,Measure.add_prod,measureReal_add_apply]
  · intros; simp [mixed,Measure.prod_smul_left,measureReal_nnreal_smul_apply]

private theorem second (a : Measure Point) (b : Cloud) (c d : Measure Point)
    [IsFiniteMeasure a] [IsFiniteMeasure c] [IsFiniteMeasure d] :
    mixed a b.law c d = b.fold (fun p => mixed a (Measure.dirac (point p)) c d) := by
  apply fold_measure b (fun x => mixed a x c d)
  · intros; simp (disch := finiteness) [mixed,Measure.add_prod,Measure.prod_add,measureReal_add_apply]
  · intros; simp [mixed,Measure.prod_smul_left,Measure.prod_smul_right,measureReal_nnreal_smul_apply]

private theorem third (a b : Measure Point) (c : Cloud) (d : Measure Point)
    [IsFiniteMeasure a] [IsFiniteMeasure b] [IsFiniteMeasure d] :
    mixed a b c.law d = c.fold (fun p => mixed a b (Measure.dirac (point p)) d) := by
  apply fold_measure c (fun x => mixed a b x d)
  · intros; simp (disch := finiteness) [mixed,Measure.add_prod,Measure.prod_add,measureReal_add_apply]
  · intros; simp [mixed,Measure.prod_smul_left,Measure.prod_smul_right,measureReal_nnreal_smul_apply]

private theorem fourth (a b c : Measure Point) (d : Cloud)
    [IsFiniteMeasure a] [IsFiniteMeasure b] [IsFiniteMeasure c] :
    mixed a b c d.law = d.fold (fun p => mixed a b c (Measure.dirac (point p))) := by
  apply fold_measure d (fun x => mixed a b c x)
  · intros; simp (disch := finiteness) [mixed,Measure.prod_add,measureReal_add_apply]
  · intros; simp [mixed,Measure.prod_smul_right,measureReal_nnreal_smul_apply]

private theorem value (p q r s : Pos) :
    mixed (Measure.dirac (point p)) (Measure.dirac (point q))
      (Measure.dirac (point r)) (Measure.dirac (point s)) =
    if order p q r s then 1 else 0 := by
  simp only [mixed,Measure.dirac_prod_dirac,Measure.real,Measure.dirac_apply' _ measurable_event]
  simp only [Set.indicator, event,Set.mem_ofPred_eq,point,increasing.lt_iff_lt,order]
  split <;> simp_all

private theorem cast_fold (c : Cloud) (F : Pos → ℕ) :
    ((c.fold F : ℕ):ℝ) = c.fold (fun p => (F p : ℝ)) := by
  induction c with
  | leaf p w => simp [Cloud.fold,nsmul_eq_mul]
  | node f a b ia ib => simp [Cloud.fold,ia,ib]

theorem mixed_law (a b c d : Cloud) :
    mixed a.law b.law c.law d.law = (quad a b c d : ℝ) := by
  rw [first]
  simp_rw [second,third,fourth,value]
  simp only [quad,cast_fold,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

/-- Every certified integer lower bound gives a probability measure with that packing rate. -/
theorem certified (c : Cloud) (h : c.valid) (hn : 0<c.frame.weight) (steps : ℕ) :
    ∃ μ : Measure Point, IsProbabilityMeasure μ ∧ μ squareᶜ=0 ∧
      24*(lower steps c c c c : ℝ)/(c.frame.weight:ℝ)^4 ≤ rate μ := by
  let t : ℝ≥0 := (c.frame.weight : ℝ≥0)⁻¹
  refine ⟨t • c.law, ⟨?_⟩, by simp [c.support], ?_⟩
  · change (t : ℝ≥0∞) * c.law univ = 1
    rw [c.total h]
    have ht : (t : ℝ≥0∞) = (c.frame.weight : ℝ≥0∞)⁻¹ := by simp [t,hn.ne']
    rw [ht]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by finiteness)
  unfold rate
  rw [mixed_smul,mixed_law]
  have key : (lower steps c c c c : ℝ) ≤ (quad c c c c : ℝ) := by
    exact_mod_cast lower_le_quad steps c c c c h h h h
  have scal : (t:ℝ) = ((c.frame.weight:ℝ))⁻¹ := by simp [t]
  rw [scal,inv_pow,div_eq_mul_inv]
  nlinarith [mul_le_mul_of_nonneg_right key (by positivity : 0≤((c.frame.weight:ℝ)^4)⁻¹)]

end Discrete
end PresuttiStromquist
end
