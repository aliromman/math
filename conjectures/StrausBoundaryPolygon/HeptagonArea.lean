module

public import conjectures.StrausBoundaryPolygon.Coordinates
public import conjectures.StrausBoundaryPolygon.Trapezoid

@[expose] public section
namespace StrausBoundaryPolygon.Heptagon
open Set MeasureTheory
noncomputable section

abbrev V := regularVertex 7
abbrev R := regularBody 7

private theorem vertex_enclosure (i : Fin 7) :
    (-9013:ℝ)/10000 ≤ (V i).1 ∧ (V i).1 ≤ 1 ∧
    |(V i).2| ≤ (8/10)*(V i).1+1157/1000 ∧
    |(V i).2| ≤ (-228/1000)*(V i).1+929/1000 ∧
    |(V i).2| ≤ (-207/100)*(V i).1+2075/1000 := by
  obtain ⟨xl,xu,yl,yu⟩ := coordinate_bounds i
  simp only [abs_le]
  fin_cases i <;> norm_num [V,coordBox] at xl xu yl yu ⊢
  all_goals repeat' constructor
  all_goals linarith only [xl,xu,yl,yu]

/-- Three rational trapezoids enclose the regular heptagon. -/
theorem area_upper : volume.real R ≤ 2753/1000 := by
  let A := strip (-902/1000) (-223/1000) (8/10) (1157/1000)
  let B := strip (-223/1000) (624/1000) (-228/1000) (929/1000)
  let C := strip (624/1000) 1 (-207/100) (2075/1000)
  have cover : R ⊆ (A∪B)∪C := by
    intro p hp
    have lo := hull_support V (-1) 0 (9013/10000) (by intro i; linarith [(vertex_enclosure i).1]) p hp
    have hi := hull_support V 1 0 1 (by intro i; linarith [(vertex_enclosure i).2.1]) p hp
    by_cases a : p.1 ≤ -223/1000
    · exact Or.inl (Or.inl ⟨⟨by linarith,a⟩,hull_strip_bound V _ _ (fun i ↦ (vertex_enclosure i).2.2.1) p hp⟩)
    by_cases b : p.1 ≤ 624/1000
    · exact Or.inl (Or.inr ⟨⟨by linarith,b⟩,hull_strip_bound V _ _ (fun i ↦ (vertex_enclosure i).2.2.2.1) p hp⟩)
    · exact Or.inr ⟨⟨by linarith,by linarith⟩,hull_strip_bound V _ _ (fun i ↦ (vertex_enclosure i).2.2.2.2) p hp⟩
  have w : volume R ≤ volume A+volume B+volume C := calc
    _ ≤ volume ((A∪B)∪C) := measure_mono cover
    _ ≤ _ := (measure_union_le ..).trans (add_le_add (measure_union_le ..) le_rfl)
  dsimp only [A,B,C] at w
  repeat rw [strip_volume (by norm_num) (by rintro x ⟨hl,hr⟩; linarith)] at w
  have rat : volume R ≤ ENNReal.ofReal (2753/1000)  := w.trans (by
    rw [←ENNReal.ofReal_add (by norm_num) (by norm_num),←ENNReal.ofReal_add (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by norm_num))
  simpa only [Measure.real,ENNReal.toReal_ofReal (by norm_num : 0≤(2753:ℝ)/1000)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top rat

theorem area_positive : 0<volume.real R := by
  have mem (i : Fin 7) : V i∈R := subset_convexHull ℝ _ (mem_range_self _)
  have cv : Convex ℝ R := convex_convexHull ..
  have y (i : Fin 7) (hi : 0 < i.val) (upper : 1/2 ≤ (V i).2) (t : ℝ) (ht : |t|≤1/2) :
      ((V i).1,t)∈R := by
    have neg := mem (⟨7-i.val,by omega⟩ : Fin 7)
    change regularVertex 7 ⟨7-i.val,_⟩∈R at neg
    rw [reflected i hi] at neg
    have pos : ((V i).1,(V i).2)∈R := mem i
    exact vertical_mem cv neg pos ⟨by linarith [(abs_le.mp ht).1],by linarith [(abs_le.mp ht).2]⟩
  have b1 := coordinate_bounds 1
  have b2 := coordinate_bounds 2
  norm_num [coordBox] at b1 b2
  change _ ∧ _ ∧ _ ∧ _ at b1 b2
  have order : (V 2).1 < (V 1).1 := by dsimp [V]; linarith [b1.1,b2.2.1]
  have y1 := y 1 (by decide) (by dsimp [V]; linarith [b1.2.2.1])
  have y2 := y 2 (by decide) (by dsimp [V]; linarith [b2.2.2.1])
  have S := strip_subset (m:=0) (c:=1/2) cv order
    (by simpa using y2 (1/2) (by norm_num)) (by simpa using y2 (-(1/2)) (by norm_num))
    (by simpa using y1 (1/2) (by norm_num)) (by simpa using y1 (-(1/2)) (by norm_num))
  have lo := measure_mono (μ:=volume) S
  rw [strip_volume order.le (by intros; norm_num)] at lo
  have fin := ((finite_range V).isCompact_convexHull ℝ).measure_lt_top (μ:=volume)
  apply ENNReal.toReal_pos (ne_of_gt _) fin.ne
  exact (ENNReal.ofReal_pos.mpr (by nlinarith [order])).trans_le lo

end
end StrausBoundaryPolygon.Heptagon
