module

public import conjectures.StrausBoundaryPolygon.Trapezoid

@[expose] public section
namespace StrausBoundaryPolygon
open Set MeasureTheory Finset
noncomputable section
namespace Example

def raw : Fin 9 → ℤ × ℤ :=
  ![(0,4),(0,-4),(1,-8),(2,-9),(3,-8),(4,0),(3,8),(2,9),(1,8)]

def vertex (i : Fin 9) : Plane := ((raw i).1,(raw i).2)

def body := convexHull ℝ (range vertex)

def quadrilateral : Fin 4 → Plane := ![vertex 0,vertex 1,vertex 4,vertex 6]

private theorem vertex_mem (i : Fin 9) : vertex i∈body :=
  subset_convexHull ℝ _ (mem_range_self _)

theorem compact : IsCompact body := (finite_range vertex).isCompact_convexHull ℝ

theorem convex : Convex ℝ body := convex_convexHull ..

private theorem base_normal : ∀ p∈body, p.1*(-1)+p.2*0 ≤ 0 :=
  hull_support vertex _ _ _ (by intro i; fin_cases i <;> norm_num [vertex,raw])

private theorem lower_normal : ∀ p∈body, p.1+(-p.2) ≤ 11 := by
  simpa only [body,mul_one,mul_neg_one] using
    hull_support vertex 1 (-1) 11 (by intro i; fin_cases i <;> norm_num [vertex,raw])

private theorem upper_normal : ∀ p∈body, p.1+p.2 ≤ 11 := by
  simpa only [body,mul_one] using
    hull_support vertex 1 1 11 (by intro i; fin_cases i <;> norm_num [vertex,raw])

private theorem base_frontier {p : Plane} (hp : p∈body) (hx : p.1=0) : p∈frontier body := by
  apply supporting_frontier (v:=(-1,0)) hp _ (by norm_num)
  intro x h
  simpa [hx] using base_normal x h

private theorem q_frontier (i) : quadrilateral i∈frontier body := by
  fin_cases i
  · exact base_frontier (vertex_mem 0) (by norm_num [quadrilateral,vertex,raw])
  · exact base_frontier (vertex_mem 1) (by norm_num [quadrilateral,vertex,raw])
  · apply supporting_frontier (p:=vertex 4) (v:=(1,-1)) (vertex_mem 4) _ (by norm_num)
    intro x hx
    norm_num [vertex,raw]; linarith [lower_normal x hx]
  · apply supporting_frontier (p:=vertex 6) (v:=(1,1)) (vertex_mem 6) _ (by norm_num)
    intro x hx
    norm_num [vertex,raw]; linarith [upper_normal x hx]

theorem quad_area : polygonArea quadrilateral = 36 := by
  norm_num [area_four,doubleQuad,det,quadrilateral,vertex,raw]

private theorem q_inscribed : Inscribed body quadrilateral := by
  refine ⟨?_,q_frontier,?_,quad_area ▸ (by norm_num)⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [quadrilateral,vertex,raw]
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [orient,det,quadrilateral,vertex,raw]

private def intQuad (a b c d : ℤ×ℤ) : ℤ :=
  (c.1-a.1)*(d.2-b.2)-(c.2-a.2)*(d.1-b.1)

set_option maxHeartbeats 1000000 in
private theorem vertex_bound : ∀ a b c d, |intQuad (raw a) (raw b) (raw c) (raw d)| ≤ 72 := by
  decide +kernel

theorem maximal : MaximalInscribed body quadrilateral := by
  refine ⟨q_inscribed,?_⟩
  intro p hp
  rw [quad_area,area_four]
  have mem (i) : p i∈body := compact.isClosed.closure_eq ▸ (hp.2.1 i).1
  have limit (i j k l) : |doubleQuad (vertex i) (vertex j) (vertex k) (vertex l)| ≤ 72 := by
    unfold doubleQuad det vertex
    dsimp
    exact_mod_cast vertex_bound i j k l
  linarith [quadrilateral_bound vertex limit (mem 0) (mem 1) (mem 2) (mem 3)]

theorem shares : SharesEdge body quadrilateral := by
  refine ⟨0,?_⟩
  change segment ℝ (vertex 0) (vertex 1) ⊆ frontier body
  intro x hx
  apply base_frontier (convex.segment_subset (vertex_mem 0) (vertex_mem 1) hx)
  obtain ⟨u,t,_,_,_,rfl⟩ := hx
  norm_num [vertex,raw]

end Example
end
end StrausBoundaryPolygon
