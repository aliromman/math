module

public import conjectures.Hypertriangulations.BoundaryGeometry
public import conjectures.Hypertriangulations.BoundarySum

public section
noncomputable section
namespace Hypertriangulations
namespace Boundary
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {P : V→Plane} {E : V→V→Prop}

private abbrev HasEdge (T : Mesh P E) (i j : V) : Prop := ∃ t∈T.faces,t.edge i j

open Classical in
private theorem count_value (T : Mesh P E) (i j : V) :
    edgeCount T i j = if HasEdge T i j then 1 else 0 := by
  classical
  by_cases h : HasEdge T i j
  · obtain ⟨f,hf,he⟩ := h
    have eq : (T.faces.filter fun t => t.edge i j)={f} := by
      ext t
      simp only [mem_filter,mem_singleton]
      constructor
      · exact fun ⟨ht,et⟩ => same_left T ht hf et he
      · rintro rfl; exact ⟨hf,he⟩
    have h' : HasEdge T i j := ⟨f,hf,he⟩
    simp [edgeCount,eq,h']
  · have eq : (T.faces.filter fun t => t.edge i j)=∅ :=
      eq_empty_iff_forall_notMem.mpr fun t ht => h ⟨t,(mem_filter.mp ht).1,(mem_filter.mp ht).2⟩
    simp [edgeCount,eq,h]

private theorem supporting_counts (T : Mesh P E)
    (nd : ∃ a b c,orient (P a) (P b) (P c)≠0) {i j : V} (ne : P i≠P j)
    (left : ∀ z,0≤orient (P i) (P j) (P z))
    (only : ∀ z,orient (P i) (P j) (P z)=0 → z=i ∨ z=j) :
    edgeCount T i j=1 ∧ edgeCount T j i=0 := by
  classical
  have fwd : HasEdge T i j := exposed T nd ne left only
  have rev : ¬HasEdge T j i := by
    rintro ⟨t,ht,et⟩
    obtain ⟨k,_,h⟩ := edge_info et (T.positive _ ht)
    rw [orient_swap] at h
    exact (left k).not_gt (neg_pos.mp h)
  simp [count_value,fwd,rev]

theorem counts (T S : Mesh P E)
    (forced : ∀ i j, P i≠P j → (∀ z,0≤orient (P i) (P j) (P z)) →
      ∀ z,orient (P i) (P j) (P z)=0 → z=i ∨ z=j) (i j : V) :
    edgeCount T i j-edgeCount T j i=edgeCount S i j-edgeCount S j i := by
  classical
  by_cases nd : ∃ a b c,orient (P a) (P b) (P c)≠0
  · by_cases same : P i=P j
    · have zero (U : Mesh P E) {a b : V} (h : P a=P b) : edgeCount U a b=0 := by
        have absent : ¬HasEdge U a b := by
          rintro ⟨t,ht,et⟩
          obtain ⟨k,_,pos⟩ := edge_info et (U.positive _ ht)
          simp [h] at pos
        simp [count_value,absent]
      rw [zero T same,zero T same.symm,zero S same,zero S same.symm]
    by_cases left : ∀ z,0≤orient (P i) (P j) (P z)
    · obtain ⟨a,b⟩ := supporting_counts T nd same left (forced i j same left)
      obtain ⟨c,d⟩ := supporting_counts S nd same left (forced i j same left)
      rw [a,b,c,d]
    by_cases right : ∀ z,0≤orient (P j) (P i) (P z)
    · obtain ⟨a,b⟩ := supporting_counts T nd (Ne.symm same) right (forced j i (Ne.symm same) right)
      obtain ⟨c,d⟩ := supporting_counts S nd (Ne.symm same) right (forced j i (Ne.symm same) right)
      rw [a,b,c,d]
    push Not at left right
    obtain ⟨l,hl⟩ := left
    obtain ⟨r,hr⟩ := right
    have eq (U : Mesh P E) : edgeCount U i j=edgeCount U j i := by
      have he : HasEdge U i j ↔ HasEdge U j i :=
        ⟨fun ⟨t,ht,e⟩ => opposite U ht e hl,fun ⟨t,ht,e⟩ => opposite U ht e hr⟩
      simp only [count_value,he]
    rw [eq T,eq S,sub_self,sub_self]
  · have empty (U : Mesh P E) : U.faces=∅ :=
      eq_empty_iff_forall_notMem.mpr fun t ht => nd ⟨t.a,t.b,t.c,(U.positive _ ht).ne'⟩
    simp [edgeCount,empty]

end Boundary

open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {P : V→Plane} {E : V→V→Prop}

/-- The sum of an antisymmetric edge potential depends only on the oriented hull boundary. -/
theorem boundary_invariant (T S : Mesh P E)
    (forced : ∀ i j, P i≠P j → (∀ z,0≤orient (P i) (P j) (P z)) →
      ∀ z,orient (P i) (P j) (P z)=0 → z=i ∨ z=j)
    (g : V→V→ℤ) (anti : ∀ i j,g j i= -g i j) :
    (∑ t∈T.faces,(g t.a t.b+g t.b t.c+g t.c t.a)) =
      ∑ t∈S.faces,(g t.a t.b+g t.b t.c+g t.c t.a) :=
  boundary_of_coefficients T S (Boundary.counts T S forced) g anti

end Hypertriangulations
end
