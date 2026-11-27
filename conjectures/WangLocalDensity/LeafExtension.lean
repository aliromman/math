module

public import conjectures.WangLocalDensity.ConnectedComplement

@[expose] public section
namespace WangLocalDensity
open Finset SimpleGraph
open scoped Sym2

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
private theorem paths_avoid {S : Finset V} (c : Conn G S) {a b x y : V}
    (outside : b∉S) (hx : x∈S) (hy : y∈S) :
    (G.deleteEdges {s(a,b)}).Reachable x y := by
  let f : G.induce (S : Set V) →g G.deleteEdges {s(a,b)} := {
    toFun := Subtype.val
    map_rel' := by
      intro u v h
      refine deleteEdges_adj.mpr ⟨h,?_⟩
      change s(u.val,v.val)≠s(a,b)
      intro eq
      rcases Sym2.eq_iff.mp eq with h'|h'
      · exact outside (h'.2 ▸ v.property)
      · exact outside (h'.1 ▸ u.property) }
  exact (c.preconnected ⟨x,hx⟩ ⟨y,hy⟩).map f

private theorem cut_has_leaf (tree : G.IsTree) {S : Finset V} (cs : Conn G S) (cc : Conn G Sᶜ) :
    ∃ x∈S, ∃! y,G.Adj x y := by
  classical
  have cross : ∃ a∈S,∃ b∈Sᶜ,G.Adj a b := by
    by_contra h
    obtain ⟨a,ha⟩ := cs.nonempty
    obtain ⟨b,hb⟩ := cc.nonempty
    have stay (w : V) (walk : Relation.ReflTransGen G.Adj a w) : w∈S := by
      induction walk with
      | refl => exact ha
      | @tail u v _ edge ih =>
        by_contra bad
        exact h ⟨u,ih,v,mem_compl.mpr bad,edge⟩
    exact (mem_compl.mp hb) (stay b ((reachable_iff_reflTransGen ..).mp
      (tree.connected.preconnected a b)))
  obtain ⟨a,ha,b,hb,ab⟩ := cross
  have only {u v : V} (hu : u∈S) (hv : v∈Sᶜ) (edge : G.Adj u v) : u=a ∧ v=b := by
    have bridge := (isAcyclic_iff_forall_adj_isBridge.mp tree.isAcyclic) ab
    by_contra bad
    have different : s(u,v)≠s(a,b) := by
      intro eq
      rcases Sym2.eq_iff.mp eq with e|e
      · exact bad e
      · exact (mem_compl.mp hb) (e.1 ▸ hu)
    have path := (paths_avoid (a:=a) cs (mem_compl.mp hb) ha hu).trans
      ((deleteEdges_adj.mpr ⟨edge,different⟩).reachable)
    have tail := paths_avoid (a:=b) cc (show a∉Sᶜ by simp [ha]) hv hb
    rw [Sym2.eq_swap] at tail
    exact isBridge_iff.mp bridge (path.trans tail)
  by_cases sing : Subsingleton S
  · refine ⟨a,ha,b,ab,fun u hu => ?_⟩
    by_cases ins : u∈S
    · have eq := congrArg Subtype.val (sing.elim (⟨a,ha⟩ : S) ⟨u,ins⟩)
      exact (hu.ne eq).elim
    · exact (only ha (mem_compl.mpr ins) hu).2
  · let _ : Nontrivial S := not_subsingleton_iff_nontrivial.mp sing
    let H := G.induce (S : Set V)
    have tr : H.IsTree := ⟨cs,tree.isAcyclic.induce _⟩
    obtain ⟨u,v,ne,du,dv⟩ := tr.exists_ne_and_degree_eq_one
    have choose : ∃ w : S, H.degree w=1 ∧ w.val≠a := by
      by_cases e : u.val=a
      · exact ⟨v,dv,fun f => ne (Subtype.ext (e.trans f.symm))⟩
      · exact ⟨u,du,e⟩
    obtain ⟨w,dw,away⟩ := choose
    obtain ⟨y,adj,unique⟩ := degree_eq_one_iff_existsUnique_adj.mp dw
    refine ⟨w.val,w.property,y.val,adj,fun v ev => ?_⟩
    by_cases ins : v∈S
    · exact congrArg Subtype.val (unique (⟨v,ins⟩ : S) ev)
    · exact (away (only w.property (mem_compl.mpr ins) ev).1).elim

/-- Every proper subtree lies in a proper subtree at least as dense that
    contains a leaf of the ambient tree. -/
theorem leaf_extension (tree : G.IsTree) {S : Finset V} (cs : Conn G S) (proper : S≠univ) :
    ∃ W : Finset V, S⊆W ∧ Conn G W ∧ W≠univ ∧ density G S≤density G W ∧
      ∃ v∈W, ∃! w,G.Adj v w := by
  obtain ⟨W,sub,cw,pw,cc,den⟩ := connected_complement_extension tree.connected cs proper
  exact ⟨W,sub,cw,pw,den,cut_has_leaf tree cw cc⟩

end WangLocalDensity
