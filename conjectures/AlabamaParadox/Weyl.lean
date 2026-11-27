module

public import conjectures.AlabamaParadox.Statement
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open UnitAddTorus

namespace AlabamaParadox

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Normalized product Haar measure on the unit torus. -/
def torusHaar (ι : Type*) [Fintype ι] : Measure (UnitAddTorus ι) :=
  Measure.pi fun _ => AddCircle.haarAddCircle

instance : IsProbabilityMeasure (torusHaar ι) := by unfold torusHaar; infer_instance

/-- The distribution of the first `N+1` observations. -/
def empirical {X : Type*} [MeasurableSpace X] (a : ℕ → X) (N : ℕ) : ProbabilityMeasure X :=
  ⟨((N+1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range (N+1), Measure.dirac (a n),
    ⟨by simp [ENNReal.inv_mul_cancel]⟩⟩

private theorem empirical_integral {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (a : ℕ → X) (N : ℕ) (f : C(X,ℂ)) :
    ∫ x, f x ∂(empirical a N : Measure X) =
      (∑ n ∈ Finset.range (N+1), f (a n)) / (N+1) := by
  change (∫ x, f x ∂(_ • _ : Measure X)) = _
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac' f _ f.continuous.stronglyMeasurable, ENNReal.toReal_add,
      Complex.real_smul, div_eq_inv_mul]
  · intro i _
    exact integrable_dirac' f.continuous.stronglyMeasurable (by simp)

private theorem fourier_as_character (h : ι → ℤ) (x : UnitAddTorus ι) :
    mFourier h x = ((AddCircle.toCircle (∑ i, h i • x i) : Circle) : ℂ) := by
  classical
  simp only [mFourier, ContinuousMap.coe_mk, fourier_apply]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, AddCircle.toCircle_add]

private theorem fourier_rotation (h : ι → ℤ) (x : UnitAddTorus ι) (n : ℕ) :
    mFourier h (n • x) = (mFourier h x)^n := by
  rw [fourier_as_character, fourier_as_character]
  have H : (∑ i, h i • (n • x) i) = n • ∑ i, h i • x i := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_comm n]
  rw [H, AddCircle.toCircle_nsmul, Circle.coe_pow]

private theorem geometric_limit {w : ℂ} (hw : ‖w‖ = 1) (hne : w ≠ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N+1), w ^ n) / (N+1)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N : ℕ => (2 / ‖w-1‖) * (1 / ((N:ℝ)+1)))
  · filter_upwards with N
    have H := norm_sub_le (w^(N+1)) 1
    rw [norm_pow, hw, one_pow, norm_one] at H
    rw [geom_sum_eq hne, norm_div, norm_div]
    simp [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ N+1), div_eq_mul_inv] at *
    gcongr
    linarith
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 / ‖w-1‖)

instance : (torusHaar ι).IsAddLeftInvariant := by unfold torusHaar; infer_instance

/-- Integer characters do not vanish on the generating direction. -/
def IrrationalDirection (v : UnitAddTorus ι) : Prop :=
  ∀ h : ι → ℤ, h ≠ 0 → ∑ i, h i • v i ≠ 0

private theorem fourier_integral_limit (v : UnitAddTorus ι) (hv : IrrationalDirection v)
    (h : ι → ℤ) : Tendsto (fun N => ∫ x, mFourier h x ∂(empirical (· • v) N : Measure _))
      atTop (𝓝 (∫ x, mFourier h x ∂torusHaar ι)) := by
  by_cases hz : h = 0
  · subst h
    simp [mFourier_zero]
  have hne : mFourier h v ≠ 1 := by
    rw [fourier_as_character]
    intro H
    exact hv h hz (AddCircle.injective_toCircle one_ne_zero (by apply Subtype.ext; simpa using H))
  have hunit : ‖mFourier h v‖ = 1 := by rw [fourier_as_character, Circle.norm_coe]
  have h_add (x : UnitAddTorus ι) : mFourier h (v+x) = mFourier h v * mFourier h x := by
    simp only [fourier_as_character, Pi.add_apply, smul_add, Finset.sum_add_distrib,
      AddCircle.toCircle_add, Circle.coe_mul]
  have I := integral_add_left_eq_self (μ := torusHaar ι) (mFourier h) v
  simp_rw [h_add, integral_const_mul] at I
  have I0 : (∫ x, mFourier h x ∂torusHaar ι) = 0 := by
    by_contra H
    apply hne
    apply mul_right_cancel₀ H
    simpa only [one_mul] using I
  simp_rw [I0, empirical_integral, fourier_rotation]
  exact geometric_limit hunit hne

omit [Fintype ι] in
private theorem integral_bound (μ : Measure (UnitAddTorus ι)) [IsProbabilityMeasure μ]
    (f : C(UnitAddTorus ι, ℂ)) : ‖∫ x, f x ∂μ‖ ≤ ‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ f.norm_coe_le_norm)

private theorem integral_cont (μ : Measure (UnitAddTorus ι)) [IsFiniteMeasure μ]
    (f : C(UnitAddTorus ι, ℂ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Weyl equidistribution on a finite product of circles, by Fourier approximation. -/
theorem weyl (v : UnitAddTorus ι) (hv : IrrationalDirection v) :
    Tendsto (empirical (· • v)) atTop (𝓝 (⟨torusHaar ι, inferInstance⟩ : ProbabilityMeasure _)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).2
  intro F
  let f : C(UnitAddTorus ι, ℂ) := F.toContinuousMap
  let μ := fun N : ℕ => (empirical (· • v) N : Measure (UnitAddTorus ι))
  let ν := torusHaar ι
  change Tendsto (fun N => ∫ x, f x ∂μ N) atTop (𝓝 (∫ x, f x ∂ν))
  have span_case (g : C(UnitAddTorus ι, ℂ)) (hg : g ∈ Submodule.span ℂ (Set.range mFourier)) :
      Tendsto (fun N => ∫ x, g x ∂μ N) atTop (𝓝 (∫ x, g x ∂ν)) := by
    induction hg using Submodule.span_induction with
    | mem g hg => obtain ⟨h,rfl⟩ := hg; exact fourier_integral_limit v hv h
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [ContinuousMap.add_apply, integral_add (integral_cont _ a) (integral_cont _ b)]
      exact ha.add hb
    | smul s a _ ha =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      exact ha.const_mul s
  rw [Metric.tendsto_nhds]
  intro ε he
  have hd : f ∈ closure (↑(Submodule.span ℂ (Set.range (mFourier (d := ι)))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_mFourier_closure_eq_top]; trivial
  obtain ⟨g,hg,hdist⟩ := Metric.mem_closure_iff.mp hd (ε/3) (by positivity)
  have clos (ρ : Measure (UnitAddTorus ι)) [IsProbabilityMeasure ρ] :
      dist (∫ x, f x ∂ρ) (∫ x, g x ∂ρ) < ε/3 := by
    rw [dist_eq_norm, ← integral_sub (integral_cont ρ f) (integral_cont ρ g)]
    exact (integral_bound ρ (f-g)).trans_lt (by simpa only [dist_eq_norm] using hdist)
  filter_upwards [Metric.tendsto_nhds.mp (span_case g hg) (ε/3) (by positivity)] with N hN
  calc
    _ ≤ dist (∫ x, f x ∂μ N) (∫ x, g x ∂μ N) + dist (∫ x, g x ∂μ N) (∫ x, f x ∂ν) := dist_triangle ..
    _ ≤ _ + (dist (∫ x, g x ∂μ N) (∫ x, g x ∂ν) + dist (∫ x, g x ∂ν) (∫ x, f x ∂ν)) := by gcongr; exact dist_triangle ..
    _ < ε := by have h₁ := clos (μ N); have h₂ := clos ν; rw [dist_comm] at h₂; linarith

/-- Weyl's theorem for any measurable set whose boundary has Haar measure zero. -/
theorem weyl_frequency (v : UnitAddTorus ι) (hv : IrrationalDirection v)
    (S : Set (UnitAddTorus ι)) (hm : MeasurableSet S) (hS : torusHaar ι (frontier S) = 0) :
    Tendsto (frequency (fun n => n • v ∈ S)) atTop (𝓝 ((torusHaar ι).real S)) := by
  classical
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (weyl v hv) hS
  apply (tendsto_add_atTop_iff_nat 1).1
  have ht := (ENNReal.tendsto_toReal (measure_ne_top (torusHaar ι) S)).comp h
  convert ht using 1
  ext N
  change _ = (((((N+1:ℕ):ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range (N+1), Measure.dirac (n • v)) S).toReal)
  simp [frequency, Measure.dirac_apply' _ hm, Set.indicator_apply, Finset.sum_boole, ENNReal.toReal_add, div_eq_inv_mul]
  rfl

abbrev mkCircle : ℝ → UnitAddCircle := (↑)

private theorem openArc (a b : ℝ) : IsOpen (mkCircle '' Ioo a b) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

private theorem closedArc (a b : ℝ) : IsClosed (mkCircle '' Icc a b) :=
  (isCompact_Icc.image (QuotientAddGroup.continuous_mk (N := AddSubgroup.zmultiples (1:ℝ)))).isClosed

private theorem arc_measurable (a b : ℝ) : MeasurableSet (mkCircle '' Ico a b) := by
  rcases lt_or_ge a b with h | h
  · rw [← Set.insert_left_Ioo h, Set.image_insert_eq]
    exact (openArc a b).measurableSet.insert _
  · simp [Set.Ico_eq_empty_of_le h]

private theorem arc_frontier (a b : ℝ) :
    frontier (mkCircle '' Ico a b) ⊆ {mkCircle a, mkCircle b} := by
  intro x hx
  have hc : x ∈ mkCircle '' Icc a b := closure_minimal (image_mono Ico_subset_Icc_self)
    (closedArc a b) hx.1
  obtain ⟨t,ht,rfl⟩ := hc
  by_cases ha : t = a
  · simp [ha]
  by_cases hb : t = b
  · simp [hb]
  exfalso
  exact hx.2 ((interior_maximal (image_mono Ioo_subset_Ico_self) (openArc a b))
    ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ha), lt_of_le_of_ne ht.2 hb⟩, rfl⟩)

private theorem arc_haar (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    AddCircle.haarAddCircle (mkCircle '' Ico a b) = ENNReal.ofReal (b-a) := by
  have h₁ : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ)))
  have ho : (volume : Measure UnitAddCircle) (mkCircle '' Ioo a b) = ENNReal.ofReal (b-a) := by
    rw [AddCircle.add_projection_respects_measure (1:ℝ) 0 (openArc a b).measurableSet]
    have E : (mkCircle ⁻¹' (mkCircle '' Ioo a b)) ∩ Ioc 0 (0+1) = Ioo a b := by
      ext x
      constructor
      · rintro ⟨⟨y,hy,hxy⟩,hx⟩
        have hy' : y ∈ Ioc 0 (0+1) := ⟨lt_of_le_of_lt ha hy.1, by linarith [hy.2]⟩
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hy' hx).1 hxy ▸ hy
      · intro hx
        exact ⟨⟨x,hx,rfl⟩, lt_of_le_of_lt ha hx.1, by linarith [hx.2]⟩
    rw [E, Real.volume_Ioo]
  rw [← h₁, ← ho]
  by_cases h : a < b
  · rw [← Set.insert_left_Ioo h, Set.image_insert_eq]
    exact measure_congr (insert_ae_eq_self _ _)
  · simp [Ioo_eq_empty h, Ico_eq_empty_of_le (by linarith : b ≤ a)]

private theorem frac_arc {x a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    mkCircle x ∈ mkCircle '' Ico a b ↔ Int.fract x ∈ Ico a b := by
  constructor
  · rintro ⟨t, ht, he⟩
    have h₁ : t ∈ Ico 0 (0+1) := ⟨ha.trans ht.1, by linarith [ht.2]⟩
    have h₂ : Int.fract x ∈ Ico 0 (0+1) := ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one x⟩
    have e := (AddCircle.coe_eq_coe_iff_of_mem_Ico h₁ h₂).1 (by simpa using he : mkCircle t = mkCircle (Int.fract x))
    rwa [← e]
  · intro h; exact ⟨_,h,AddCircle.coe_fract _⟩

/-- No nonzero integer combination of the coordinates is an integer. -/
def Nonresonant (y : ι → ℝ) : Prop := ∀ h : ι → ℤ, h ≠ 0 → ∀ t : ℤ, (∑ i, (h i:ℝ)*y i) ≠ t

theorem direction_of_nonresonant {y : ι → ℝ} (h : Nonresonant y) :
    IrrationalDirection (fun i => mkCircle (y i)) := by
  intro w hw he
  have H : mkCircle (∑ i, (w i:ℝ)*y i) = 0 := by
    have E : ∀ s : Finset ι, mkCircle (∑ i ∈ s, (w i:ℝ)*y i) = ∑ i ∈ s, w i • mkCircle (y i) := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty => simp [mkCircle]
      | @insert i s hi ih => simp only [Finset.sum_insert hi, ← zsmul_eq_mul, mkCircle] at *; rw [AddCircle.coe_add, AddCircle.coe_zsmul, ih]
    rw [E, he]
  obtain ⟨t,ht⟩ := (AddCircle.coe_eq_zero_iff 1).1 H
  exact h w hw t (by simpa [zsmul_eq_mul] using ht.symm)

/-- The Cartesian product of the half-open arcs with endpoints in `[0,1]`. -/
def torusBox (l r : ι → ℝ) : Set (UnitAddTorus ι) :=
  Set.univ.pi fun i => mkCircle '' Set.Ico (l i) (r i)

theorem box_null (l r : ι → ℝ) : torusHaar ι (frontier (torusBox l r)) = 0 := by
  let wall (i : ι) : Set (UnitAddTorus ι) := {x | x i = mkCircle (l i)} ∪ {x | x i = mkCircle (r i)}
  have hw (i : ι) : torusHaar ι (wall i) = 0 := by
    apply measure_union_null <;> exact Measure.pi_hyperplane _ _ _
  apply measure_mono_null (t := ⋃ i, wall i) _ (measure_iUnion_null hw)
  intro x hx
  have H := hx.1
  have G := hx.2
  simp only [torusBox, mem_closure_pi, interior_pi_set finite_univ, Set.mem_pi, mem_univ, forall_const] at H G
  push Not at G
  obtain ⟨i,hi⟩ := G
  exact mem_iUnion.mpr ⟨i, arc_frontier _ _ ⟨H i,hi⟩⟩

/-- Frequencies of half-open fractional-part boxes. -/
theorem weyl_box {y : ι → ℝ} (hy : Nonresonant y) (l r : ι → ℝ)
    (hl : ∀ i, 0 ≤ l i) (hlr : ∀ i, l i ≤ r i) (hr : ∀ i, r i ≤ 1) :
    Tendsto (frequency (fun n => ∀ i, Int.fract ((n:ℝ)*y i) ∈ Ico (l i) (r i))) atTop
      (𝓝 (∏ i, (r i-l i))) := by
  let v := fun i => mkCircle (y i)
  have hm : MeasurableSet (torusBox l r) := MeasurableSet.univ_pi fun i => arc_measurable _ _
  have h := weyl_frequency v (direction_of_nonresonant hy) (torusBox l r) hm (box_null l r)
  have vol : (torusHaar ι).real (torusBox l r) = ∏ i, (r i-l i) := by
    change ((Measure.pi _ (univ.pi _)).toReal) = _
    rw [Measure.pi_pi, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [arc_haar _ _ (hl i) (hr i), ENNReal.toReal_ofReal (sub_nonneg.mpr (hlr i))]
  rw [vol] at h
  convert h using 1
  congr 1
  funext n
  apply propext
  simp only [torusBox, mem_univ_pi]
  apply forall_congr'
  intro i
  change _ ↔ n • mkCircle (y i) ∈ _
  simpa only [← AddCircle.coe_nsmul, nsmul_eq_mul] using (frac_arc (x := (n:ℝ)*y i) (hl i) (hr i)).symm

private theorem grid_identity {m : ℕ} [NeZero m] (x : ℝ) (t : ℤ) :
    (m:ℝ) * Int.fract ((x-t)/m) = (((⌊x⌋-t : ℤ) : ZMod m).val:ℝ) + Int.fract x := by
  let D := ⌊x⌋-t
  let a := (D : ZMod m).val
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have ha : (a:ℤ) = D % m := ZMod.val_intCast D
  have H : (a:ℤ) + (m:ℤ)*(D/(m:ℤ)) = D := ha ▸ Int.emod_add_mul_ediv _ _
  have HR : (a:ℝ) + (m:ℝ)*((D/(m:ℤ):ℤ):ℝ) = (⌊x⌋:ℝ)-t := by exact_mod_cast H
  have HC : (x-(t:ℝ))/m = ((a:ℝ)+Int.fract x)/m + ((D/(m:ℤ):ℤ):ℝ) := by
    field_simp; nlinarith [Int.floor_add_fract x]
  have ha' : (a:ℝ)+1 ≤ m := by exact_mod_cast (ZMod.val_lt (D:ZMod m))
  have HB : ((a:ℝ) + Int.fract x)/m ∈ Ico 0 1 := by
    constructor
    · exact div_nonneg (add_nonneg (by positivity) (Int.fract_nonneg x)) hm.le
    · rw [div_lt_iff₀ hm]; linarith [Int.fract_lt_one x]
  rw [HC, Int.fract_add_intCast, Int.fract_eq_self.mpr HB]
  field_simp
  rfl

private theorem grid_interval {m : ℕ} [NeZero m] (x : ℝ) (t : ℤ) (k : ZMod m)
    {l r : ℝ} (hl : 0 ≤ l) (hr : r ≤ 1) :
    Int.fract ((x-t)/m) ∈ Ico ((k.val+l)/m) ((k.val+r)/m) ↔
      ((⌊x⌋-t : ℤ) : ZMod m) = k ∧ Int.fract x ∈ Ico l r := by
  let d : ZMod m := ((⌊x⌋-t : ℤ) : ZMod m)
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have H := grid_identity (m := m) x t
  change _ = (d.val:ℝ) + _ at H
  simp only [Set.mem_Ico, div_le_iff₀ hm, lt_div_iff₀ hm, mul_comm _ (m:ℝ), H]
  constructor
  · intro ⟨h1,h2⟩
    have E : d = k := by
      apply ZMod.val_injective
      by_contra hn
      rcases lt_or_gt_of_ne hn with h | h
      · have : (d.val:ℝ)+1 ≤ k.val := by exact_mod_cast h
        linarith [Int.fract_lt_one x]
      · have : (k.val:ℝ)+1 ≤ d.val := by exact_mod_cast h
        linarith [Int.fract_nonneg x]
    exact ⟨E, by rw [E] at h1; linarith, by rw [E] at h2; linarith⟩
  · rintro ⟨(E : d = k), h1,h2⟩
    rw [E]; constructor <;> linarith

private def bias (i : Option ι) : ℤ := i.elim 1 (fun _ => 0)

private def adjusted (m : ℕ) (y : Option ι → ℝ) (j : Option ι) : ℝ := (y j - bias j)/m

private theorem adjusted_nonresonant {m : ℕ} [NeZero m] {y : Option ι → ℝ}
    (hy : Nonresonant y) : Nonresonant (adjusted m y) := by
  intro h hn t H
  apply hy h hn (m*t+∑ i, h i * bias i)
  have hm : (m:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  simp only [adjusted, ← mul_div_assoc, ← Finset.sum_div] at H
  rw [div_eq_iff hm] at H
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib] at H
  linarith
private def digits {m : ℕ} (b : ι → ZMod m) : Option ι → ZMod m
  | none => -(∑ i, b i)
  | some i => b i

private theorem frequency_split {β : Type*} [Fintype β] (P : ℕ → Prop) (Q : β → ℕ → Prop)
    (which : ℕ → β) (h : ∀ n b, Q b n ↔ P n ∧ which n = b) (N : ℕ) :
    frequency P N = ∑ b, frequency (Q b) N := by
  classical
  simp only [frequency, ← Finset.sum_div]
  congr 1
  norm_cast
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp only [h]
  by_cases hp : P n <;> simp [hp]

/-- The fractional parts and the flag congruence have product-uniform frequency. The `none`
coordinate supplies the one digit determined by the congruence after all others are chosen. -/
theorem flag_box {m : ℕ} [NeZero m] {y : Option ι → ℝ} (hy : Nonresonant y)
    (l r : Option ι → ℝ) (hl : ∀ i, 0 ≤ l i) (hlr : ∀ i, l i ≤ r i) (hr : ∀ i, r i ≤ 1) :
    Tendsto (frequency (fun n => (∑ i, (⌊(n:ℝ)*y i⌋ : ZMod m)) = (n : ZMod m) ∧
      ∀ i, Int.fract ((n:ℝ)*y i) ∈ Ico (l i) (r i))) atTop (𝓝 ((∏ i, (r i-l i))/m)) := by
  classical
  let z := adjusted m y
  let lower (b : ι → ZMod m) (j : Option ι) := (((digits b j).val:ℝ) + l j)/m
  let upper (b : ι → ZMod m) (j : Option ι) := (((digits b j).val:ℝ) + r j)/m
  let Q (b : ι → ZMod m) (n : ℕ) := ∀ j, Int.fract ((n:ℝ)*z j) ∈ Ico (lower b j) (upper b j)
  let P (n : ℕ) := (∑ i, (⌊(n:ℝ)*y i⌋ : ZMod m)) = (n : ZMod m) ∧
    ∀ i, Int.fract ((n:ℝ)*y i) ∈ Ico (l i) (r i)
  let actual (n : ℕ) (j : Option ι) : ZMod m := (⌊(n:ℝ)*y j⌋ : ZMod m) - n*(bias j : ℤ)
  let which (n : ℕ) (i : ι) := actual n (some i)
  have qr n b : Q b n ↔ (∀ j, actual n j = digits b j) ∧
      ∀ j, Int.fract ((n:ℝ)*y j) ∈ Ico (l j) (r j) := by
    change (∀ j, _) ↔ _
    rw [← forall_and]
    apply forall_congr'
    intro j
    have E : (n:ℝ)*z j = ((n:ℝ)*y j-((n:ℤ)*bias j : ℤ))/m := by
      simp [z, adjusted]; ring
    simp only [lower, upper, E, actual]
    simpa using (grid_interval ((n:ℝ)*y j) ((n:ℤ)*bias j) (digits b j) (hl j) (hr j))
  have part n b : Q b n ↔ P n ∧ which n = b := by
    rw [qr]
    refine ⟨?_,?_⟩
    · rintro ⟨h,hr⟩
      have Et : which n = b := funext fun i => h (some i)
      refine ⟨⟨?_,hr⟩,Et⟩
      have En := h none
      rw [Fintype.sum_option]
      simp only [digits, actual, bias, Option.elim_none, Int.cast_one, mul_one] at En
      have Ht : ∑ i, (⌊(n:ℝ)*y (some i)⌋ : ZMod m) = ∑ i, b i := by
        apply Finset.sum_congr rfl; intro i _; simpa [which, actual, bias, digits] using h (some i)
      rw [Ht]; linear_combination En
    · rintro ⟨⟨h,hr⟩,rfl⟩
      refine ⟨?_,hr⟩
      intro j
      cases j with
      | none =>
        rw [Fintype.sum_option] at h
        simp [digits, which, actual, bias]
        linear_combination h
      | some i => rfl
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have tiles (b : ι → ZMod m) : Tendsto (frequency (Q b)) atTop
      (𝓝 ((∏ j, (r j-l j))/(m:ℝ)^(Fintype.card ι+1))) := by
    have H := weyl_box (adjusted_nonresonant (m := m) hy) (lower b) (upper b)
      (fun j => div_nonneg (add_nonneg (by positivity) (hl j)) hm.le)
      (fun j => by dsimp [lower, upper]; gcongr; exact hlr j)
      (fun j => by
        dsimp [upper]
        rw [div_le_iff₀ hm]
        have U : ((digits b j).val:ℝ)+1 ≤ m := by exact_mod_cast (digits b j).val_lt
        linarith [hr j])
    convert H using 2
    simp only [upper, lower, ← sub_div, add_sub_add_left_eq_sub, Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_option]
  have H := tendsto_finsetSum Finset.univ (fun b _ => tiles b)
  have ans : (∑ _ : ι → ZMod m, ((∏ j, (r j-l j))/(m:ℝ)^(Fintype.card ι+1))) =
        (∏ j, (r j-l j))/(m:ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, nsmul_eq_mul,
      Nat.cast_pow, pow_succ]
    field_simp
  rw [ans] at H
  exact H.congr' (Eventually.of_forall fun n => (frequency_split P Q which part n).symm)

/-- Reindexing a frequency vector preserves nonresonance. -/
theorem Nonresonant.comp_equiv {κ : Type*} [Fintype κ] {y : ι → ℝ} (hy : Nonresonant y)
    (e : κ ≃ ι) : Nonresonant (y ∘ e) := by
  intro h hn t H
  apply hy (h ∘ e.symm) (fun z => hn (by ext j; simpa using congrFun z (e j))) t
  rw [← e.sum_comp]
  simpa using H

/-- Independent shares summing to one yield nonresonant differences from the flag share. -/
theorem difference_nonresonant (p : Option ι → ℝ) (hsum : ∑ i, p i = 1)
    (hind : IndependentShares p) :
    Nonresonant (fun i : ι => p (some i) - p none) := by
  intro h hn t H
  let a (j : Option ι) := j.elim (-(∑ i, h i)) h - t
  have sum_zero : (∑ j, (a j : ℝ)*p j) = 0 := by
    rw [Fintype.sum_option] at hsum ⊢
    simp only [a, Option.elim_none, Option.elim_some, Int.cast_sub, Int.cast_neg,
      Int.cast_sum, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at H
    nlinarith [congrArg ((t:ℝ) * ·) hsum]
  have z := hind a sum_zero
  have et : h = fun _ => t := funext fun i => sub_eq_zero.mp (z (some i))
  have head := z none
  simp only [a, Option.elim_none, et, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at head
  have tz : ((Fintype.card ι:ℤ)+1)*t = 0 := by linarith
  have t0 := (mul_eq_zero.mp tz).resolve_left (by positivity)
  exact hn (by rw [et,t0]; rfl)

/-- The flag-frequency formula with an arbitrary nonempty finite index set. -/
theorem flag_frequency [Nonempty ι] {m : ℕ} [NeZero m] {y : ι → ℝ} (hy : Nonresonant y)
    (l r : ι → ℝ) (hl : ∀ i, 0 ≤ l i) (hlr : ∀ i, l i ≤ r i) (hr : ∀ i, r i ≤ 1) :
    Tendsto (frequency (fun n => (∑ i, (⌊(n:ℝ)*y i⌋ : ZMod m)) = (n : ZMod m) ∧
      ∀ i, Int.fract ((n:ℝ)*y i) ∈ Ico (l i) (r i))) atTop (𝓝 ((∏ i, (r i-l i))/m)) := by
  classical
  let s : ι := Classical.choice inferInstance
  let e := Equiv.optionSubtypeNe s
  have H := flag_box (m := m) (hy.comp_equiv e) (l ∘ e) (r ∘ e)
    (fun i => hl (e i)) (fun i => hlr (e i)) (fun i => hr (e i))
  have prod' := e.prod_comp (fun i => r i-l i)
  simp only [Function.comp_apply] at H
  rw [prod'] at H
  apply H.congr'
  filter_upwards with N
  congr 1
  funext n
  apply propext
  rw [e.sum_comp (fun i => (⌊(n:ℝ)*y i⌋ : ZMod m))]
  apply and_congr_right'
  constructor
  · intro h j
    obtain ⟨i,rfl⟩ := e.surjective j
    exact h i
  · exact fun h i => h (e i)

/-- Subtracting one distinguished independent share from each of the others. -/
theorem nonresonant_differences [DecidableEq ι] (p : ι → ℝ) (q : ι) (hsum : ∑ i, p i = 1)
    (hind : IndependentShares p) :
    Nonresonant (fun i : {j : ι // j ≠ q} => p i - p q) := by
  let e := Equiv.optionSubtypeNe q
  apply difference_nonresonant (p ∘ e) ((e.sum_comp p).trans hsum)
  intro a h j
  have H : ∑ i, ((a (e.symm i)):ℝ)*p i = 0 := by
    rw [← e.sum_comp]
    simpa using h
  simpa using hind (fun i => a (e.symm i)) H (e j)

/-- Deleting one independent share yields a nonresonant coordinate system. -/
theorem nonresonant_without_one [DecidableEq ι] (p : ι → ℝ) (q : ι) (hsum : ∑ i, p i = 1)
    (hind : IndependentShares p) : Nonresonant (fun i : {j : ι // j ≠ q} => p i) := by
  let e := Equiv.optionSubtypeNe q
  intro h hn t H
  let a (j : ι) : ℤ := (e.symm j).elim 0 h - t
  have coeff (j) : a (e j) = j.elim 0 h - t := by simp [a]
  have hsum' := (e.sum_comp p).trans hsum
  rw [Fintype.sum_option] at hsum'
  have sum_zero : (∑ i, (a i:ℝ)*p i) = 0 := by
    rw [← e.sum_comp, Fintype.sum_option]
    simp only [coeff, Option.elim_none, Option.elim_some, Int.cast_sub, Int.cast_neg,
      sub_mul, zero_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change _ + ((∑ i : {j : ι // j ≠ q}, (h i:ℝ)*p i) - _) = 0
    rw [H]
    nlinarith [congrArg ((t:ℝ)*·) hsum']
  have Z (j : Option {i : ι // i ≠ q}) : j.elim 0 h - t = 0 := (coeff j).symm.trans (hind a sum_zero (e j))
  have tz : t = 0 := by simpa using Z none
  apply hn
  ext i
  simpa [tz] using Z (some i)

/-- info: 'AlabamaParadox.flag_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flag_frequency

end
end AlabamaParadox
