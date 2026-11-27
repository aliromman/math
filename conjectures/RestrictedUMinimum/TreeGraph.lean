module

public import conjectures.RestrictedUMinimum.CutExpansion
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace RestrictedUMinimum.Tree

theorem shift_zero (k : ℕ) : shift k 0 = 0 := rfl
theorem shift_succ (k j : ℕ) : shift k (j + 1) = k + j + 1 := rfl

theorem edge_bounds (t : Tree) {i j : ℕ} (h : (i,j) ∈ t.edges) :
    i < j ∧ j ≤ t.branchesSize := by
  induction t generalizing i j with
  | point => simp [edges] at h
  | plant t ih =>
    simp only [edges, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨⟨x,y⟩, he, e⟩
    · cases h; simp [branchesSize]
    · cases e
      have hp := ih he
      simp [branchesSize, hp.1, hp.2]
  | merge a b ia ib =>
    simp only [edges, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨⟨x,y⟩, he, e⟩
    · have hp := ia h
      exact ⟨hp.1, by simp only [branchesSize]; omega⟩
    · cases e
      have hp := ib he
      cases y with
      | zero => omega
      | succ y =>
        cases x <;> simp only [shift_zero, shift_succ, branchesSize] <;> omega

/-- Every nonroot vertex has a neighbor with a smaller label. -/
private theorem predecessor (t : Tree) :
    ∀ v, 0 < v → v ≤ t.branchesSize → ∃ u < v, (u, v) ∈ t.edges := by
  induction t with
  | point => intro v hv hs; simp [branchesSize] at hs; omega
  | plant t ih =>
    intro v hv hs
    cases v with
    | zero => omega
    | succ v =>
      cases v with
      | zero => exact ⟨0, by decide, List.mem_cons_self⟩
      | succ v =>
        obtain ⟨u, hu, he⟩ := ih (v + 1) (by omega) (by simpa [branchesSize] using hs)
        exact ⟨u + 1, by omega, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, he, rfl⟩)⟩
  | merge a b ha hb =>
    intro v hv hs
    by_cases h : v ≤ a.branchesSize
    · obtain ⟨u, hu, he⟩ := ha v hv h
      exact ⟨u, hu, List.mem_append_left _ he⟩
    · obtain ⟨j, rfl⟩ : ∃ j, v = a.branchesSize + (j + 1) := ⟨v - (a.branchesSize + 1), by omega⟩
      obtain ⟨u, hu, he⟩ := hb (j + 1) (by omega) (by simpa [branchesSize] using hs)
      refine ⟨shift a.branchesSize u, ?_, List.mem_append_right _ (List.mem_map.mpr ⟨_, he, rfl⟩)⟩
      cases u <;> simp [shift]
      omega

private theorem graph_connected (t : Tree) : t.graph.Connected := by
  let r : Fin t.order := ⟨0, Nat.zero_lt_succ _⟩
  refine t.graph.connected_iff_exists_forall_reachable.mpr ⟨r, ?_⟩
  intro v
  induction v using WellFoundedLT.induction with
  | ind i ih =>
    by_cases h : i.val = 0
    · have eq : i = r := Fin.ext h
      rw [eq]
    · obtain ⟨j, hj, he⟩ := predecessor t i.val (by omega) (Nat.le_of_lt_succ i.isLt)
      let u : Fin t.order := ⟨j, hj.trans i.isLt⟩
      have adj : t.graph.Adj u i := ⟨fun hz => hj.ne (congrArg Fin.val hz), Or.inl he⟩
      exact (ih u hj).trans adj.reachable

/-- The unrooted graph of every presentation is a finite tree. -/
theorem graph_isTree (t : Tree) : t.graph.IsTree := by
  classical
  have hc := graph_connected t
  refine SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hc, ?_⟩
  let pairs := t.edges.map fun e => s(e.1, e.2)
  have upper : t.graph.edgeFinset.card ≤ pairs.toFinset.card := by
    apply Finset.card_le_card_of_injOn (Sym2.map Fin.val) ?_ (Sym2.map.injective Fin.val_injective).injOn
    intro e
    induction e using Sym2.inductionOn with
    | _ i j =>
      intro he
      have h : t.graph.Adj i j := SimpleGraph.mem_edgeFinset.mp he
      change s(i.val, j.val) ∈ pairs.toFinset
      rw [List.mem_toFinset, List.mem_map]
      rcases h.2 with hij | hji
      · exact ⟨(i.val, j.val), hij, rfl⟩
      · exact ⟨(j.val, i.val), hji, Sym2.eq_swap⟩
  have hcard : Nat.card t.graph.edgeSet ≤ t.branchesSize := by
    rw [Nat.card_eq_fintype_card, ← t.graph.edgeFinset_card, ← edges_length]
    exact upper.trans (by simpa only [pairs, List.length_map] using pairs.toFinset_card_le)
  apply le_antisymm _ hc.card_vert_le_card_edgeSet_add_one
  calc
    _ ≤ t.branchesSize + 1 := Nat.add_le_add_right hcard 1
    _ = Nat.card (Fin t.order) := by simp [order]

/-- A position in the presentation lists one edge of the unrooted graph. -/
def edgeAt (t : Tree) (i : Fin t.edges.length) : t.graph.edgeSet := by
  let p := t.edges.get i
  have hp : p ∈ t.edges := List.get_mem _ _
  have hb := t.edge_bounds hp
  let a : Fin t.order := ⟨p.1, Nat.lt_succ_of_le (hb.1.le.trans hb.2)⟩
  let b : Fin t.order := ⟨p.2, Nat.lt_succ_of_le hb.2⟩
  exact ⟨s(a,b), show t.graph.Adj a b from ⟨fun h => hb.1.ne (congrArg Fin.val h), Or.inl hp⟩⟩

theorem edgeAt_bijective (t : Tree) : Function.Bijective (edgeAt t) := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · rintro ⟨e, he⟩
    revert he
    induction e using Sym2.inductionOn with
    | _ a b =>
      intro he
      have hab : t.graph.Adj a b := he
      rcases hab.2 with hab | hba
      · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hab
        refine ⟨i, Subtype.ext ?_⟩
        apply Sym2.map.injective Fin.val_injective
        change s((t.edges.get i).1, (t.edges.get i).2) = s(a.val, b.val)
        rw [hi]
      · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hba
        refine ⟨i, Subtype.ext ?_⟩
        apply Sym2.map.injective Fin.val_injective
        change s((t.edges.get i).1, (t.edges.get i).2) = s(a.val, b.val)
        rw [hi]
        exact Sym2.eq_swap
  · rw [Fintype.card_fin, edges_length, SimpleGraph.card_edgeSet]
    have hc := t.graph_isTree.card_edgeFinset
    rw [Fintype.card_fin] at hc
    exact Nat.succ.inj hc.symm

/-- Read the mask bit for each edge of the labeled simple graph. -/
noncomputable def maskEquivGraph (t : Tree) : t.CutMask ≃ (t.graph.edgeSet → Bool) :=
  t.maskEquivEdges.trans <| Equiv.arrowCongr
    (Equiv.ofBijective (edgeAt t) (edgeAt_bijective t)) (Equiv.refl _)

/-- Sum once over each choice of edges in the actual labeled graph. -/
theorem cutPolynomial_eq_graph_edge_sum (t : Tree) :
    t.cutPolynomial = ∑ bits : t.graph.edgeSet → Bool, (t.cutForest (t.maskEquivGraph.symm bits)).term := by
  rw [cutPolynomial_eq_sum_cuts]
  exact Fintype.sum_equiv t.maskEquivGraph _ _ fun m => by simp

end RestrictedUMinimum.Tree
