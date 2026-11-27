module

public import conjectures.StrausBoundaryPolygon.Nonagon

@[expose] public section
namespace StrausBoundaryPolygon.Example
open Set MeasureTheory
open scoped ENNReal
noncomputable section

private theorem lookup (i : Fin 9) : vertex i∈body := subset_convexHull ℝ _ (mem_range_self _)

local macro "get_vertex" : tactic => `(tactic|
  (first
    | (convert lookup 0 using 1 <;> norm_num [vertex,raw] <;> done)
    | (convert lookup 1 using 1 <;> norm_num [vertex,raw] <;> done)
    | (convert lookup 2 using 1 <;> norm_num [vertex,raw] <;> done)
    | (convert lookup 3 using 1 <;> norm_num [vertex,raw] <;> done)
    | (convert lookup 4 using 1 <;> norm_num [vertex,raw] <;> done)
    | (convert lookup 5 using 1 <;> norm_num [vertex,raw] <;> done)
    | (convert lookup 6 using 1 <;> norm_num [vertex,raw] <;> done)
    | (convert lookup 7 using 1 <;> norm_num [vertex,raw] <;> done)
    | (convert lookup 8 using 1 <;> norm_num [vertex,raw] <;> done)))

private theorem sliceA : strip 0 1 4 4 ⊆ body := by
  apply strip_subset convex (by norm_num) <;> get_vertex
private theorem sliceB : strip 1 2 1 7 ⊆ body := by
  apply strip_subset convex (by norm_num) <;> get_vertex
private theorem sliceC : strip 2 3 (-1) 11 ⊆ body := by
  apply strip_subset convex (by norm_num) <;> get_vertex
private theorem sliceD : strip 3 4 (-8) 32 ⊆ body := by
  apply strip_subset convex (by norm_num) <;> get_vertex

private theorem vol {a b m c : ℝ} (hab : a≤b) (h : ∀ x∈Ioc a b, 0≤m*x+c) :
    volume (strip a b m c) = ENNReal.ofReal ((b-a)*(m*(a+b)+2*c)) :=
  strip_volume hab h

theorem area_lower : 54 ≤ volume.real body := by
  have sub := union_subset (union_subset (union_subset sliceA sliceB) sliceC) sliceD
  have bound := measure_mono (μ:=volume) sub
  rw [measure_union (disjoint_union_left.mpr ⟨disjoint_union_left.mpr
    ⟨strip_disjoint (by norm_num),strip_disjoint (by norm_num)⟩,strip_disjoint (by norm_num)⟩) (strip_measurable ..),
    measure_union (disjoint_union_left.mpr ⟨strip_disjoint (by norm_num),strip_disjoint (by norm_num)⟩) (strip_measurable ..),
    measure_union (strip_disjoint (by norm_num)) (strip_measurable ..)] at bound
  repeat rw [vol (by norm_num) (by rintro x ⟨hl,hr⟩; linarith)] at bound
  norm_num at bound
  simpa [Measure.real] using ENNReal.toReal_mono compact.measure_lt_top.ne bound

/-- The four vertical slabs have total area 54. -/
theorem area : volume.real body = 54 := by
  have line (m c : ℝ) (h : ∀ i, |(vertex i).2|≤m*(vertex i).1+c) (p : Plane) (hp : p∈body) :=
    hull_strip_bound vertex m c h p hp
  let A := strip 0 1 4 4
  let B := strip 1 2 1 7
  let C := strip 2 3 (-1) 11
  let D := strip 3 4 (-8) 32
  let Z := ({0} : Set ℝ) ×ˢ (univ : Set ℝ)
  have measure0 : volume Z=0 := by simp [Z,Measure.volume_eq_prod]
  have cover : body ⊆ Z∪(((A∪B)∪C)∪D) := by
    intro p hp
    have xl := hull_support vertex (-1) 0 0 (by intro i; fin_cases i <;> norm_num [vertex,raw]) p hp
    have xu := hull_support vertex 1 0 4 (by intro i; fin_cases i <;> norm_num [vertex,raw]) p hp
    by_cases left : p.1=0
    · exact Or.inl ⟨left,mem_univ _⟩
    right
    by_cases x1 : p.1≤1
    · exact Or.inl (Or.inl (Or.inl ⟨⟨by grind,x1⟩,
        line 4 4 (by intro i; fin_cases i <;> norm_num [vertex,raw]) p hp⟩))
    by_cases x2 : p.1≤2
    · exact Or.inl (Or.inl (Or.inr ⟨⟨by linarith,x2⟩,
        line 1 7 (by intro i; fin_cases i <;> norm_num [vertex,raw]) p hp⟩))
    by_cases x3 : p.1≤3
    · exact Or.inl (Or.inr ⟨⟨by linarith,x3⟩,
        line (-1) 11 (by intro i; fin_cases i <;> norm_num [vertex,raw]) p hp⟩)
    · exact Or.inr ⟨⟨by linarith,by linarith⟩,
        line (-8) 32 (by intro i; fin_cases i <;> norm_num [vertex,raw]) p hp⟩
  have bd : volume body ≤ volume A+volume B+volume C+volume D := calc
    _ ≤ volume (Z∪(((A∪B)∪C)∪D)) := measure_mono cover
    _ ≤ volume Z+volume (((A∪B)∪C)∪D) := measure_union_le ..
    _ = volume (((A∪B)∪C)∪D) := by rw [measure0,zero_add]
    _ ≤ _ := (measure_union_le ..).trans (add_le_add
      ((measure_union_le ..).trans (add_le_add (measure_union_le ..) le_rfl)) le_rfl)
  dsimp only [A,B,C,D] at bd
  repeat rw [vol (by norm_num) (by rintro x ⟨xl,xr⟩; linarith)] at bd
  norm_num at bd
  exact le_antisymm (by simpa [Measure.real] using ENNReal.toReal_mono (by norm_num : (54:ℝ≥0∞)≠⊤) bd) area_lower

private theorem boxB : Ioo (1:ℝ) 2 ×ˢ Ioo (-8:ℝ) 8 ⊆ body := by
  rintro ⟨x,y⟩ ⟨⟨xl,xr⟩,⟨yl,yr⟩⟩
  apply sliceB
  exact ⟨⟨xl,xr.le⟩,by constructor <;> dsimp <;> linarith⟩

private theorem boxCD : Ioo (2:ℝ) (7/2) ×ˢ Ioo (-1:ℝ) 1 ⊆ body := by
  rintro ⟨x,y⟩ ⟨⟨xl,xr⟩,⟨yl,yr⟩⟩
  by_cases hx : x≤3
  · apply sliceC
    exact ⟨⟨xl,hx⟩,by constructor <;> dsimp <;> linarith⟩
  · apply sliceD
    exact ⟨⟨by linarith,by linarith⟩,by constructor <;> dsimp <;> linarith⟩

private theorem insideB {p : Plane} (hp : p∈Ioo (1:ℝ) 2 ×ˢ Ioo (-8:ℝ) 8) : p∈interior body :=
  interior_maximal boxB (isOpen_Ioo.prod isOpen_Ioo) hp

private theorem insideCD {p : Plane} (hp : p∈Ioo (2:ℝ) (7/2) ×ˢ Ioo (-1:ℝ) 1) : p∈interior body :=
  interior_maximal boxCD (isOpen_Ioo.prod isOpen_Ioo) hp

theorem interior_nonempty : (interior body).Nonempty := ⟨(3/2,0),insideB (by norm_num)⟩

/-- Only the base of the trapezoid lies on the boundary of the nonagon. -/
theorem unique_edge (i : Fin 4) :
    segment ℝ (quadrilateral i) (quadrilateral (finRotate 4 i)) ⊆ frontier body ↔ i=0 := by
  fin_cases i
  · refine ⟨fun _ ↦ rfl,fun _ ↦ ?_⟩
    change segment ℝ (vertex 0) (vertex 1) ⊆ frontier body
    intro x hx
    apply supporting_frontier (v:=(-1,0)) (convex.segment_subset (lookup 0) (lookup 1) hx) _ (by norm_num)
    obtain ⟨u,t,_,_,_,rfl⟩ := hx
    intro p hp
    have b := hull_support vertex (-1) 0 0 (by intro j; fin_cases j <;> norm_num [vertex,raw]) p hp
    norm_num [vertex,raw] at b ⊢
    exact b
  all_goals
    refine ⟨fun h ↦ ?_,by intro eq; norm_num [Fin.ext_iff] at eq⟩
    have mid := h (midpoint_mem_segment (𝕜:=ℝ) _ _)
    have bad := mid.2
    exfalso
    apply bad
  · apply insideB
    norm_num [quadrilateral,vertex,raw,finRotate_apply,midpoint_eq_smul_add]
  · apply insideCD
    norm_num [quadrilateral,vertex,raw,finRotate_apply,midpoint_eq_smul_add]
  · apply insideB
    norm_num [quadrilateral,vertex,raw,finRotate_apply,midpoint_eq_smul_add]

end
end StrausBoundaryPolygon.Example
