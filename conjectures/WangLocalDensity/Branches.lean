module

public import conjectures.WangLocalDensity.Enumeration

@[expose] public section
namespace WangLocalDensity
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

abbrev Conn (G : SimpleGraph V) (A : Finset V) := (G.induce (A : Set V)).Connected

omit [Fintype V] in
private theorem drop_part {S A B : Finset V} (hS : Conn G S) (h : Conn G (S∪A∪B))
    (separated : ∀ a∈A,∀ b∈B, ¬G.Adj a b) : Conn G (S∪A) := by
  classical
  obtain ⟨v,hv⟩ := hS.nonempty
  let start : (S∪A : Finset V) := ⟨v,mem_union_left _ hv⟩
  let big : (S∪A∪B : Finset V) := ⟨v,mem_union_left _ start.property⟩
  let retract (z : (S∪A∪B : Finset V)) : (S∪A : Finset V) :=
    if hz : z.val∈S∪A then ⟨z.val,hz⟩ else start
  have inS (y : (S∪A : Finset V)) (hy : y.val∈S) :
      (G.induce (↑(S∪A) : Set V)).Reachable start y :=
    (hS.preconnected ⟨v,hv⟩ ⟨y,hy⟩).map
      (G.induceHomOfLE (show (S : Set V) ⊆ ↑(S∪A) from fun _ h => mem_union_left _ h)).toHom
  have imageStep {x y : (S∪A∪B : Finset V)} (step : G.Adj x.val y.val) :
      (G.induce (↑(S∪A) : Set V)).Reachable (retract x) (retract y) := by
    by_cases hx : x.val ∈ S∪A <;> by_cases hy : y.val ∈ S∪A
    · simpa only [retract,dite_eq_left hx,dite_eq_left hy] using
        (show (G.induce (↑(S∪A) : Set V)).Adj ⟨x,hx⟩ ⟨y,hy⟩ from step).reachable
    · have yB := (mem_union.mp y.property).resolve_left hy
      have xS := (mem_union.mp hx).resolve_right (fun xA => separated _ xA _ yB step)
      simpa only [retract,dite_eq_left hx,dite_eq_right hy] using (inS ⟨x,hx⟩ xS).symm
    · have xB := (mem_union.mp x.property).resolve_left hx
      have yS := (mem_union.mp hy).resolve_right (fun yA => separated _ yA _ xB step.symm)
      simpa only [retract,dite_eq_right hx,dite_eq_left hy] using inS ⟨y,hy⟩ yS
    · simp only [retract,dite_eq_right hx,dite_eq_right hy]
      exact .rfl
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨start,fun y => ?_⟩
  let by' : (S∪A∪B : Finset V) := ⟨y.val,mem_union_left _ y.property⟩
  have hr := (SimpleGraph.reachable_iff_reflTransGen ..).mp (h.preconnected big by')
  have via (t : (S∪A∪B : Finset V))
      (q : Relation.ReflTransGen (G.induce (↑(S∪A∪B) : Set V)).Adj big t) :
      (G.induce (↑(S∪A) : Set V)).Reachable (retract big) (retract t) := by
    induction q with
    | refl => exact .rfl
    | tail _ edge ih => exact ih.trans (imageStep edge)
  have hb : big.val∈S∪A := start.property
  have hby : by'.val ∈ S∪A := y.property
  have first : retract big=start := by
    unfold retract
    rw [dite_eq_left hb]
  have last : retract by'=y := by
    unfold retract
    rw [dite_eq_left hby]
    exact Subtype.ext rfl
  exact first ▸ last ▸ via _ hr

omit [Fintype V] in
theorem connected_split {S A B : Finset V} (hS : Conn G S)
    (sep : ∀ a∈A,∀ b∈B, ¬G.Adj a b) :
    Conn G (S∪A∪B) ↔ Conn G (S∪A) ∧ Conn G (S∪B) := by
  constructor
  · intro h
    apply And.intro (drop_part hS h sep)
    apply drop_part (B:=A) hS
    · simpa only [union_right_comm] using h
    · intro b hb a ha edge
      exact sep _ ha _ hb edge.symm
  · rintro ⟨ha,hb⟩
    obtain ⟨v,hv⟩ := hS.nonempty
    have both : ((↑(S∪A) : Set V) ∩ ↑(S∪B)).Nonempty :=
      ⟨v,mem_union_left _ hv,mem_union_left _ hv⟩
    have hh := SimpleGraph.induce_union_connected ha.preconnected hb.preconnected both
    have eq : (↑(S∪A∪B) : Set V) = ↑(S∪A) ∪ ↑(S∪B) := by ext x; simp; tauto
    rw [Conn,eq]
    exact hh

end WangLocalDensity
