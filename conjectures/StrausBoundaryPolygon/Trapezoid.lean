module

public import conjectures.StrausBoundaryPolygon.Quadrilateral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section
namespace StrausBoundaryPolygon
open Set MeasureTheory
open scoped Interval

theorem hull_strip_bound {ι : Type*} (V : ι → Plane) (m c : ℝ) (h : ∀ i, |(V i).2|≤m*(V i).1+c) (p : Plane) (hp : p∈convexHull ℝ (range V)) :
    -(m*p.1+c) ≤ p.2 ∧ p.2≤m*p.1+c := by
  have hi := hull_support V (-m) 1 c (by intro i; have := (abs_le.mp (h i)).2; linarith) p hp
  have lo := hull_support V (-m) (-1) c (by intro i; have := (abs_le.mp (h i)).1; linarith) p hp
  constructor <;> linarith

/-- A vertical trapezoid. Omitting the left boundary makes adjacent slices disjoint. -/
def strip (a b m c : ℝ) : Set Plane :=
  {p | p.1∈Ioc a b ∧ p.2∈Icc (-(m*p.1+c)) (m*p.1+c)}

theorem strip_measurable (a b m c : ℝ) : MeasurableSet (strip a b m c) := by
  change MeasurableSet ((Prod.fst ⁻¹' Ioc a b) ∩ ({p : Plane | -(m*p.1+c) ≤ p.2} ∩ {p : Plane | p.2 ≤ m*p.1+c}))
  apply (measurable_fst measurableSet_Ioc).inter
  exact (measurableSet_le (by fun_prop) measurable_snd).inter (measurableSet_le measurable_snd (by fun_prop))

theorem strip_volume {a b m c : ℝ} (hab : a≤b)
    (pos : ∀ x∈Ioc a b, 0≤m*x+c) :
    volume (strip a b m c) = ENNReal.ofReal ((b-a)*(m*(a+b)+2*c)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (strip_measurable ..)]
  have fiber (x : ℝ) : volume (Prod.mk x ⁻¹' strip a b m c) =
      (Ioc a b).indicator (fun x ↦ ENNReal.ofReal (2*m*x+2*c)) x := by
    by_cases hx : x∈Ioc a b
    · rw [indicator_of_mem hx]
      have s : Prod.mk x ⁻¹' strip a b m c = Icc (-(m*x+c)) (m*x+c) := by
        ext y
        change (x∈Ioc a b ∧ y∈Icc (-(m*x+c)) (m*x+c)) ↔ _
        simp only [hx,true_and]
      rw [s,Real.volume_Icc]
      congr 1
      ring
    · have s : Prod.mk x ⁻¹' strip a b m c = ∅ := by
        ext y
        change (x∈Ioc a b ∧ y∈Icc (-(m*x+c)) (m*x+c)) ↔ False
        simp only [hx,false_and]
      simp [s,hx]
  simp_rw [fiber]
  rw [lintegral_indicator measurableSet_Ioc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hab]
    have h₁ : IntervalIntegrable (fun x : ℝ ↦ 2*m*x) volume a b :=
      (by fun_prop : Continuous _).intervalIntegrable ..
    rw [intervalIntegral.integral_add h₁ intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    congr 1
    simp only [smul_eq_mul]
    ring
  · exact (by fun_prop : Continuous (fun x : ℝ ↦ 2*m*x+2*c)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with x hx
    change 0≤2*m*x+2*c
    linarith [pos x hx]

theorem strip_disjoint {a b c d m w r s : ℝ} (h : b≤c) :
    Disjoint (strip a b m w) (strip c d r s) :=
  Set.disjoint_left.mpr fun _ hx hy ↦ (not_lt_of_ge (hx.1.2.trans h)) hy.1.1

private theorem interpolate_mem {K : Set Plane} (h : Convex ℝ K) {a b t m c : ℝ}
    (hab : a<b) (ht : t∈Icc a b) (hl : (a,m*a+c)∈K) (hr : (b,m*b+c)∈K) :
    (t,m*t+c)∈K := by
  let u := (b-t)/(b-a)
  let v := (t-a)/(b-a)
  have e : b-a≠0 := sub_ne_zero.mpr hab.ne'
  have one : u+v=1 := by dsimp [u,v]; field_simp; ring
  have z := h hl hr (show 0≤u from div_nonneg (by linarith [ht.2]) (by linarith))
    (show 0≤v from div_nonneg (by linarith [ht.1]) (by linarith)) one
  convert z using 1
  ext <;> simp [u,v] <;> field_simp <;> ring

theorem vertical_mem {K : Set Plane} (h : Convex ℝ K) {x a b y : ℝ}
    (ha : (x,a)∈K) (hb : (x,b)∈K) (hy : y∈Icc a b) : (x,y)∈K := by
  rcases eq_or_lt_of_le (hy.1.trans hy.2) with eq | lt
  · simpa only [le_antisymm hy.1 (eq ▸ hy.2)] using ha
  let u := (b-y)/(b-a)
  let v := (y-a)/(b-a)
  have e : b-a≠0 := sub_ne_zero.mpr lt.ne'
  have one : u+v=1 := by dsimp [u,v]; field_simp; ring
  have z := h ha hb (show 0≤u from div_nonneg (by linarith [hy.2]) (by linarith))
    (show 0≤v from div_nonneg (by linarith [hy.1]) (by linarith)) one
  convert z using 1
  ext <;> simp [u,v] <;> field_simp <;> ring

theorem strip_subset {K : Set Plane} (h : Convex ℝ K) {a b m c : ℝ} (hab : a<b)
    (h₁ : (a,m*a+c)∈K) (h₂ : (a,-(m*a+c))∈K)
    (h₃ : (b,m*b+c)∈K) (h₄ : (b,-(m*b+c))∈K) : strip a b m c ⊆ K := by
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  have xmem := Ioc_subset_Icc_self hx
  have lower := interpolate_mem (m:=-m) (c:=-c) h hab xmem
    (by simpa only [neg_mul,sub_eq_add_neg,←neg_add] using h₂)
    (by simpa only [neg_mul,sub_eq_add_neg,←neg_add] using h₄)
  apply vertical_mem h _ (interpolate_mem h hab xmem h₁ h₃) hy
  simpa only [neg_mul,←neg_add] using lower

end StrausBoundaryPolygon
