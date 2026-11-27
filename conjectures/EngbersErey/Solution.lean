module

public import conjectures.EngbersErey.Statement
import Mathlib.Data.Nat.Dist

@[expose] public section

namespace EngbersErey

def exampleEdges (leafAt : ℕ) : List Edge :=
  (List.range 11).map (fun i => (i, i + 1)) ++ [(2, 12), (12, 13), (leafAt, 14)]

private abbrev G := graph 15 (exampleEdges 3)

private instance : DecidableRel G.Adj := fun u v => by
  unfold G graph
  infer_instance

/-- The first coordinate gives the attachment point on the path.
The second gives the distance to that point. -/
private def coordinates (u : Fin 15) : ℕ × ℕ :=
  if u.val < 12 then (u.val, 0) else if u.val = 14 then (3, 1) else (2, u.val - 11)

private def routeLength (u v : Fin 15) : ℕ :=
  let (a, h) := coordinates u
  let (b, k) := coordinates v
  if a = b then Nat.dist h k else h + Nat.dist a b + k

private theorem closer : ∀ u v : Fin 15, u ≠ v →
    ∃ w, G.Adj u w ∧ routeLength w v < routeLength u v := by decide

private theorem shortWalk (u v : Fin 15) : ∃ p : G.Walk u v, p.length ≤ routeLength u v := by
  by_cases h : u = v
  · subst v
    exact ⟨.nil, Nat.zero_le _⟩
  · obtain ⟨w, edge, decrease⟩ := closer u v h
    obtain ⟨p, hp⟩ := shortWalk w v
    exact ⟨.cons edge p, Nat.succ_le_of_lt (hp.trans_lt decrease)⟩
termination_by routeLength u v

private theorem connected : G.Connected :=
  ⟨fun u v => (shortWalk u v).elim fun p _ => ⟨p⟩⟩

theorem example_isTree : (graph 15 (exampleEdges 3)).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected, ?_⟩
  change Nat.card G.edgeSet + 1 = Nat.card (Fin 15)
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem projection_bound {u v : Fin 15} (p : G.Walk u v) :
    (coordinates u).1 ≤ (coordinates v).1 + p.length := by
  have step : ∀ x y : Fin 15, G.Adj x y → (coordinates x).1 ≤ (coordinates y).1 + 1 := by decide
  induction p with
  | nil => simp
  | cons edge p ih =>
    exact (step _ _ edge).trans (Nat.succ_le_succ ih)

theorem example_diam : (graph 15 (exampleEdges 3)).diam = 11 := by
  apply le_antisymm
  · have bound : ∀ u v, routeLength u v ≤ 11 := by decide
    obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
    obtain ⟨p, hp⟩ := shortWalk u v
    exact huv ▸ (SimpleGraph.dist_le p).trans (hp.trans (bound u v))
  · obtain ⟨p, hp⟩ := connected.exists_walk_length_eq_dist 11 0
    have lower : 11 ≤ p.length := by simpa [coordinates] using projection_bound p
    exact (hp ▸ lower).trans (SimpleGraph.dist_le_diam (G.connected_iff_ediam_ne_top.mp connected))

theorem averages :
    average (candidateEdges 15 11 true) = 6 ∧ average (exampleEdges 3) = 259 / 43 := by
  decide +kernel

theorem counterexample : ¬ Conjecture := by
  intro h
  have proposed := (h 15 11 (by decide) (by decide)).2 (by decide) (by decide)
  have valid : Valid 15 (exampleEdges 3) := by
    unfold Valid
    decide
  have upper := (proposed.2.2.2 _ valid example_isTree example_diam).1
  rw [averages.1, averages.2] at upper
  exact (by decide +kernel : ¬ (259 / 43 : ℚ) ≤ 6) upper

/-- info: 'EngbersErey.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample

end EngbersErey
