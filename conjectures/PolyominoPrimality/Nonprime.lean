module

public import conjectures.PolyominoPrimality.Example
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Ring

public section
namespace PolyominoPrimality

private def route : List Side :=
  [⟨⟨(0,1),(1,4)⟩,true,false,true⟩, ⟨⟨(1,4),(2,5)⟩,false,false,false⟩,
   ⟨⟨(2,3),(4,4)⟩,false,true,true⟩, ⟨⟨(0,2),(2,3)⟩,true,true,true⟩,
   ⟨⟨(2,1),(4,2)⟩,false,true,true⟩, ⟨⟨(1,0),(2,1)⟩,true,true,false⟩]

private theorem telescope {R : Type*} [CommRing R] (I : Ideal R) (x : Point → R)
    (a b : Point) (L : List Side) (ends : a :: L.map Side.w = L.map Side.v ++ [b])
    (rel : ∀ s ∈ L, x s.v * x s.z - x s.w * x s.u ∈ I) :
    x a * (L.map (fun s => x s.z)).prod - x b * (L.map (fun s => x s.u)).prod ∈ I := by
  induction L generalizing a with
  | nil =>
    obtain rfl : a=b := by simpa using ends
    simp
  | cons s tail ih =>
    have front : a = s.v := (List.cons.inj ends).1
    have more : s.w :: tail.map Side.w = tail.map Side.v ++ [b] := (List.cons.inj ends).2
    rw [front]
    have step := rel s (by simp)
    have later := ih s.w more (fun t ht => rel t (by simp [ht]))
    let p := (tail.map (fun t => x t.z)).prod
    let q := (tail.map (fun t => x t.u)).prod
    change x s.v * (x s.z * p) - x b * (x s.u * q) ∈ I
    have e : x s.v * (x s.z * p) - x b * (x s.u * q) =
        p * (x s.v * x s.z - x s.w * x s.u) + x s.u * (x s.w * p - x b * q) := by ring
    rw [e]
    exact I.add_mem (I.mul_mem_left _ step) (I.mul_mem_left _ later)

variable (K : Type*) [Field K]
private noncomputable abbrev X := variableAt K exampleCells
private noncomputable abbrev ideal := polyominoIdeal K exampleCells

private theorem side_mem (s : Side) (h : s.rect ∈ innerIntervals exampleCells) :
    X K s.v * X K s.z - X K s.w * X K s.u ∈ ideal K := by
  have m : minor K exampleCells s.rect ∈ ideal K := Ideal.subset_span ⟨s.rect,h,rfl⟩
  have n := (ideal K).neg_mem m
  obtain ⟨r,i,j,v⟩ := s
  cases i <;> cases j <;> cases v <;>
    first | simpa [minor,Side.v,Side.w,Side.z,Side.u,mul_comm,neg_sub] using m
          | simpa [minor,Side.v,Side.w,Side.z,Side.u,mul_comm,neg_sub] using n

private def marks := route.map Side.z
private def marked (p : Point) : K := if p ∈ marks then 1 else 0

private theorem vertices_ok : ∀ r ∈ innerIntervals exampleCells, ∀ i j : Bool,
    r.corner i j ∈ vertices exampleCells := by decide +kernel

private theorem blocked : ∀ r ∈ innerIntervals exampleCells,
    (r.corner false false ∉ marks ∨ r.corner true true ∉ marks) ∧
    (r.corner true false ∉ marks ∨ r.corner false true ∉ marks) := by decide +kernel

private noncomputable def ev (c : Point → K) := MvPolynomial.eval (fun p : Vertex exampleCells => c p.val)

private theorem eval_var (c : Point → K) {p : Point} (h : p ∈ vertices exampleCells) :
    ev K c (X K p) = c p := by simp [ev,variableAt,h]

private theorem evals (c : Point → K) (hc : ∀ r ∈ innerIntervals exampleCells,
    c (r.corner false false) * c (r.corner true true) =
    c (r.corner true false) * c (r.corner false true)) : ideal K ≤ RingHom.ker (ev K c) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨r,hr,rfl⟩
  apply RingHom.mem_ker.mpr
  simp only [minor,map_sub,map_mul]
  rw [eval_var K c (vertices_ok r hr _ _),eval_var K c (vertices_ok r hr _ _),
      eval_var K c (vertices_ok r hr _ _),eval_var K c (vertices_ok r hr _ _),hc r hr,sub_self]

theorem nonprime : ¬ (polyominoIdeal K exampleCells).IsPrime := by
  intro hp
  let P := (route.map (fun s => X K s.z)).prod
  let Q := (route.map (fun s => X K s.u)).prod
  have good : ∀ s ∈ route, s.rect ∈ innerIntervals exampleCells := by decide +kernel
  have product : X K (1,1) * (P-Q) ∈ ideal K := by
    rw [mul_sub]
    exact telescope (ideal K) (X K) (1,1) (1,1) route (by decide)
      (fun s hs => side_mem K s (good s hs))
  rcases hp.mem_or_mem product with h | h
  · have f := evals K (fun _ => 1) (by simp) h
    have bad := RingHom.mem_ker.mp f
    rw [eval_var K _ (p:=(1,1)) (by decide)] at bad
    exact one_ne_zero bad
  · have zeros (r : Rect) (hr : r ∈ innerIntervals exampleCells) :
        marked K (r.corner false false) * marked K (r.corner true true) =
        marked K (r.corner true false) * marked K (r.corner false true) := by
      obtain ⟨a|a,b|b⟩ := blocked r hr <;> simp [marked,a,b]
    have bad := RingHom.mem_ker.mp (evals K (marked K) zeros h)
    have positive : ∀ s ∈ route, s.z ∈ vertices exampleCells ∧ s.z ∈ marks := by decide +kernel
    have negative : ∀ s ∈ route, s.u ∈ vertices exampleCells ∧ s.u ∉ marks := by decide +kernel
    have pos (s) (hs : s ∈ route) : ev K (marked K) (X K s.z) = 1 := by
      rw [eval_var K _ (positive s hs).1]
      simp [marked,(positive s hs).2]
    have neg (s) (hs : s ∈ route) : ev K (marked K) (X K s.u) = 0 := by
      rw [eval_var K _ (negative s hs).1]
      simp [marked,(negative s hs).2]
    have ep : ev K (marked K) P = 1 := by
      unfold P
      rw [map_list_prod]
      apply List.prod_eq_one
      simpa using (show ∀ v ∈ route, ev K (marked K) (X K v.z)=1 from pos)
    have eq : ev K (marked K) Q = 0 := by
      unfold Q
      rw [map_list_prod]
      apply List.prod_eq_zero_iff.mpr
      apply List.mem_map.mpr
      let s := route.head!
      exact ⟨X K s.u,List.mem_map.mpr ⟨s,by decide,rfl⟩,neg s (by decide)⟩
    rw [map_sub,ep,eq,sub_zero] at bad
    exact one_ne_zero bad

end PolyominoPrimality
