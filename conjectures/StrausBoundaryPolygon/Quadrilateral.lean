module

public import conjectures.StrausBoundaryPolygon.Statement
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
namespace StrausBoundaryPolygon
open Set MeasureTheory Finset
noncomputable section

/-- Twice the signed area is the determinant of the diagonals. -/
def doubleQuad (a b c d : Plane) : ℝ := det (c-a) (d-b)

theorem area_four (p : Fin 4 → Plane) :
    polygonArea p = |doubleQuad (p 0) (p 1) (p 2) (p 3)|/2 := by
  unfold polygonArea
  rw [Fin.sum_univ_four]
  change |det (p 0) (p 1)+det (p 1) (p 2)+det (p 2) (p 3)+det (p 3) (p 0)|/2=_
  congr 2
  simp [doubleQuad,det]
  ring

private theorem hull_bound {ι : Type*} (v : ι → Plane) {f : Plane → ℝ} {c : ℝ}
    (affine : ∀ x y : Plane, ∀ u t : ℝ, u+t=1 →
      f (u • x+t • y)=u*f x+t*f y) (hv : ∀ i, |f (v i)| ≤ c) :
    ∀ p ∈ convexHull ℝ (range v), |f p| ≤ c := by
  apply convexHull_min (t:={p | |f p| ≤ c})
  · rintro _ ⟨i,rfl⟩
    exact hv i
  · intro x hx y hy u t hu ht one
    change |f (u • x+t • y)| ≤ c
    rw [affine _ _ _ _ one]
    calc
      _ ≤ |u*f x|+|t*f y| := abs_add_le ..
      _ = u*|f x|+t*|f y| := by rw [abs_mul,abs_mul,abs_of_nonneg hu,abs_of_nonneg ht]
      _ ≤ u*c+t*c := add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy ht)
      _ = c := by rw [←add_mul,one,one_mul]

local macro "quad_affine" : tactic => `(tactic|
  (intro x y u t one
   have ht : t=1-u := by linarith
   subst t
   simp [doubleQuad,det]
   ring))

/-- Maximizing over all four points of a convex hull reduces to its generating vertices. -/
theorem quadrilateral_bound {ι : Type*} (v : ι → Plane) {s : ℝ}
    (limit : ∀ i j k l, |doubleQuad (v i) (v j) (v k) (v l)|≤s)
    {a b c d : Plane} (ha : a∈convexHull ℝ (range v)) (hb : b∈convexHull ℝ (range v))
    (hc : c∈convexHull ℝ (range v)) (hd : d∈convexHull ℝ (range v)) :
    |doubleQuad a b c d|≤s := by
  refine hull_bound v (f:=fun z ↦ doubleQuad z b c d) (by quad_affine) ?_ a ha
  intro i
  refine hull_bound v (f:=fun z ↦ doubleQuad (v i) z c d) (by quad_affine) ?_ b hb
  intro j
  refine hull_bound v (f:=fun z ↦ doubleQuad (v i) (v j) z d) (by quad_affine) ?_ c hc
  intro k
  exact hull_bound v (f:=fun z ↦ doubleQuad (v i) (v j) (v k) z) (by quad_affine) (limit i j k) d hd

/-- A linear bound on the vertices holds throughout their convex hull. -/
theorem hull_support {ι : Type*} (v : ι → Plane) (a b c : ℝ)
    (h : ∀ i, (v i).1*a+(v i).2*b ≤ c) :
    ∀ p∈convexHull ℝ (range v), p.1*a+p.2*b ≤ c := by
  apply convexHull_min (t:={p : Plane | p.1*a+p.2*b ≤ c})
  · rintro _ ⟨i,rfl⟩
    exact h i
  · intro x hx y hy u t hu ht one
    change (u*x.1+t*y.1)*a+(u*x.2+t*y.2)*b ≤ c
    change x.1*a+x.2*b ≤ c at hx
    change y.1*a+y.2*b ≤ c at hy
    calc
      _ = u*(x.1*a+x.2*b)+t*(y.1*a+y.2*b) := by ring
      _ ≤ u*c+t*c := add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy ht)
      _ = c := by rw [←add_mul,one,one_mul]

/-- A boundary point can be certified by a supporting affine functional. -/
theorem supporting_frontier {K : Set Plane} {p v : Plane} (hp : p∈K)
    (h : ∀ x∈K, x.1*v.1+x.2*v.2 ≤ p.1*v.1+p.2*v.2)
    (nonzero : 0<v.1^2+v.2^2) : p∈frontier K := by
  refine ⟨subset_closure hp,?_⟩
  intro hi
  obtain ⟨ε,hε,inside⟩ := Metric.isOpen_iff.mp isOpen_interior p hi
  let t : ℝ := ε/(2*(‖v‖+1))
  have ht : 0<t := by dsimp [t]; positivity
  have hsmall : t*‖v‖<ε := by
    have := (div_mul_cancel₀ ε (show 2*(‖v‖+1)≠0 by positivity))
    change t*(2*(‖v‖+1))=ε at this
    nlinarith [mul_nonneg ht.le (norm_nonneg v)]
  have ball : p+t • v ∈ Metric.ball p ε := by
    simpa [Metric.mem_ball,dist_eq_norm, norm_smul,Real.norm_eq_abs,abs_of_pos ht] using hsmall
  have bound := h (p+t • v) (interior_subset (inside ball))
  simp at bound
  nlinarith [mul_pos ht nonzero]

end
end StrausBoundaryPolygon
