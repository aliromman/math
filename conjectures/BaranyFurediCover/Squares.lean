module

public import conjectures.BaranyFurediCover.Statement
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace BaranyFurediCover
open Set MeasureTheory Matrix

noncomputable def turn (a b : ℕ) : Plane →ₗ[ℝ] Plane :=
  (!![(a : ℝ), -(b : ℝ); (b : ℝ), a] : Matrix (Fin 2) (Fin 2) ℝ).toLin'

noncomputable def square (a b : ℕ) : Set Plane := turn a b '' Icc (0 : Plane) 1

def D (a b : ℕ) : ℝ := (a : ℝ)^2 + (b : ℝ)^2

theorem d_pos {a b : ℕ} (ha : 0 < a) : 0 < D a b := by
  unfold D
  positivity

theorem coord0 (a b : ℕ) (u : Plane) : turn a b u 0 = a*u 0-b*u 1 := by
  simp [turn, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

theorem coord1 (a b : ℕ) (u : Plane) : turn a b u 1 = b*u 0+a*u 1 := by
  simp [turn, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem det_turn (a b : ℕ) : LinearMap.det (turn a b) = D a b := by
  rw [turn, LinearMap.det_toLin', Matrix.det_fin_two]
  simp [D, pow_two]

theorem square_area (a b : ℕ) : area (square a b) = D a b := by
  rw [area, square, volume.addHaar_image_linearMap, ENNReal.toReal_mul, det_turn,
    Real.volume_Icc_pi_toReal (by exact zero_le_one)]
  have h : 0 ≤ D a b := by unfold D; positivity
  simp [ENNReal.toReal_ofReal, abs_of_nonneg h, h]

private def corner (e : Fin 2 → Bool) : Lattice := fun i => if e i then 1 else 0

private theorem box_hull : convexHull ℝ (range (fun e => pt (corner e))) = Icc (0 : Plane) 1 := by
  have eq : range (fun e => pt (corner e)) = univ.pi (fun _ : Fin 2 => ({0,1} : Set ℝ)) := by
    ext v
    simp only [mem_range, mem_univ_pi, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨e,rfl⟩ i
      cases h : e i <;> simp [pt,corner,h]
    · intro h
      refine ⟨fun i => decide (v i=1), funext fun i => ?_⟩
      rcases h i with h|h <;> simp [pt,corner,h]
  rw [eq, convexHull_pi]
  simp_rw [convexHull_pair, segment_eq_Icc zero_le_one]
  exact pi_univ_Icc (x := (0 : Plane)) (y := (1 : Plane))

theorem square_polygon (a b : ℕ) : LatticePolygon (square a b) := by
  let V (e : Fin 2 → Bool) : Lattice :=
    ![(a : ℤ)*corner e 0 - (b : ℤ)*corner e 1, (b : ℤ)*corner e 0 + (a : ℤ)*corner e 1]
  have he (e : Fin 2 → Bool) : turn a b (pt (corner e)) = pt (V e) := by
    ext i
    fin_cases i <;> simp [coord0,coord1,pt,V]
  refine ⟨Finset.univ.image V,?_⟩
  rw [square, ←box_hull, LinearMap.image_convexHull]
  congr 1
  rw [←Set.range_comp, Finset.coe_image, Finset.coe_univ, image_univ, ←Set.range_comp]
  exact congrArg range (funext he)

theorem square_compact (a b : ℕ) : IsCompact (square a b) :=
  isCompact_Icc.image (turn a b).continuous_of_finiteDimensional

theorem square_convex (a b : ℕ) : Convex ℝ (square a b) := by
  obtain ⟨V,h⟩ := square_polygon a b
  rw [h]
  exact convex_convexHull _ _

theorem square_interior {a b : ℕ} (ha : 0<a) : (interior (square a b)).Nonempty := by
  let f := (turn a b).equivOfDetNeZero ((det_turn a b).trans_ne (d_pos ha).ne')
  let U : Set Plane := univ.pi fun _ => Ioo (0 : ℝ) 1
  have op : IsOpen U := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have img : IsOpen ((turn a b) '' U) := f.toContinuousLinearEquiv.isOpenMap U op
  have sub : (turn a b) '' U ⊆ square a b := by
    apply image_mono
    exact fun v hv => ⟨fun i => (hv i (mem_univ _)).1.le, fun i => (hv i (mem_univ _)).2.le⟩
  have hU : U.Nonempty := ⟨fun _ => 1/2, fun _ _ => ⟨by norm_num, by norm_num⟩⟩
  exact (hU.image (turn a b)).mono (interior_maximal sub img)

/-- The two coordinates in the orthogonal basis, without division by its determinant. -/
def first (a b : ℕ) (x : Plane) : ℝ := a*x 0+b*x 1
def second (a b : ℕ) (x : Plane) : ℝ := a*x 1-b*x 0

theorem mem_square_iff {a b : ℕ} (ha : 0<a) (x : Plane) :
    x ∈ square a b ↔ first a b x ∈ Icc 0 (D a b) ∧ second a b x ∈ Icc 0 (D a b) := by
  have pos := d_pos (b:=b) ha
  constructor
  · rintro ⟨u,hu,rfl⟩
    have e : first a b (turn a b u) = D a b * u 0 := by rw [first,coord0,coord1]; unfold D; ring
    have f : second a b (turn a b u) = D a b * u 1 := by rw [second,coord0,coord1]; unfold D; ring
    rw [e,f]
    exact ⟨⟨mul_nonneg pos.le (hu.1 0), by simpa using mul_le_mul_of_nonneg_left (hu.2 0) pos.le⟩,
      ⟨mul_nonneg pos.le (hu.1 1), by simpa using mul_le_mul_of_nonneg_left (hu.2 1) pos.le⟩⟩
  · rintro ⟨hf,hs⟩
    let u : Plane := ![first a b x / D a b, second a b x / D a b]
    have hf' := (div_le_one pos).mpr hf.2
    have hs' := (div_le_one pos).mpr hs.2
    refine ⟨u,⟨?_,?_⟩,?_⟩
    · intro i; fin_cases i
      · exact div_nonneg hf.1 pos.le
      · exact div_nonneg hs.1 pos.le
    · intro i; fin_cases i
      · exact hf'
      · exact hs'
    · ext i
      fin_cases i <;> simp [coord0,coord1,u,first,second] <;> field_simp [pos.ne'] <;> unfold D <;> ring

end BaranyFurediCover
