module

public import conjectures.OlarteSantosSpreerStump.Statement

@[expose] public section

namespace OlarteSantosSpreerStump

private abbrev V := Fin 12
private abbrev Face := Finset V

-- Check bounded quantifiers on their listed faces. The ambient powerset has 4096 members.
attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableExistsAndFinset

private def rows : Finset Face := {{0, 1, 2}, {3, 4, 5}, {6, 7, 8}}
private def columns : Finset Face := {{0, 3, 6}, {1, 4, 7}, {2, 5, 8}}

/-- At a grid point with code `3i + j`, the offset is `j - i` modulo three. -/
private def offset (a : V) : ℕ := (a.val % 3 + 3 - a.val / 3) % 3

private def center (k : Fin 3) : V := ⟨9 + k.val, by omega⟩

private def adjacent (a b : V) : Prop :=
  a ≠ b ∧
    ((a.val < 9 ∧ b.val < 9 ∧ (a.val / 3 = b.val / 3 ∨ a.val % 3 = b.val % 3)) ∨
     (a.val < 9 ∧ 9 ≤ b.val ∧ offset a ≠ b.val - 9) ∨
     (b.val < 9 ∧ 9 ≤ a.val ∧ offset b ≠ a.val - 9))

private instance : DecidableRel adjacent := fun a b => by unfold adjacent; infer_instance

private def graph : SimpleGraph V where
  Adj := adjacent
  symm := ⟨by decide +kernel⟩
  loopless := ⟨fun a h => h.1 rfl⟩

private instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel adjacent)

/-- The six grid lines and the eighteen triangles in the cones over the three hexagons. -/
private def triangles : Finset Face :=
  let lines := rows ∪ columns
  lines ∪ (Finset.univ : Finset (Fin 3)).biUnion (fun k =>
    lines.image fun L => insert (center k) (L.filter fun v => offset v ≠ k.val))

private def faces : Finset Face := triangles.biUnion Finset.powerset

private theorem listed_cliques : ∀ s ∈ faces, graph.IsClique (s : Set V) := by
  decide +kernel

private theorem listed_extensions : ∀ s ∈ faces, ∀ a : V,
    (∀ b ∈ s, a ≠ b → graph.Adj a b) → insert a s ∈ faces := by
  decide +kernel

private theorem face_iff (s : Face) : s ∈ flagComplex graph ↔ s ∈ faces := by
  refine ⟨?_, listed_cliques s⟩
  induction s using Finset.induction_on with
  | empty => intro _; decide +kernel
  | insert a s ha ih =>
    intro h
    have hin : graph.IsClique (insert a (s : Set V)) := by
      simpa only [flagComplex, Set.mem_ofPred_eq, Finset.coe_insert] using h
    obtain ⟨hs, hadj⟩ := SimpleGraph.isClique_insert.mp hin
    exact listed_extensions s (ih hs) a hadj

private theorem pure_closed : PureWithoutBoundary 2 (flagComplex graph) := by
  unfold PureWithoutBoundary
  simp only [face_iff]
  refine ⟨⟨{0, 1, 2}, by decide +kernel, by decide +kernel⟩, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private theorem dual_of_lines (A B : Finset Face)
    (hA : A ⊆ faces)
    (h : ∀ s ∈ faces, s ∈ A ↔ ∀ t ∈ B, ∃ v ∈ s, v ∈ t) :
    (A : Family V) = dual (flagComplex graph) B := by
  ext s
  constructor
  · intro hs
    exact ⟨(face_iff s).2 (hA hs), (h s (hA hs)).1 hs⟩
  · rintro ⟨hs, ht⟩
    exact (h s ((face_iff s).1 hs)).2 ht

private theorem grid_dual : IsDualPair (flagComplex graph) rows columns :=
  ⟨dual_of_lines rows columns (by decide +kernel) (by decide +kernel),
   dual_of_lines columns rows (by decide +kernel) (by decide +kernel)⟩

private def cell (i : Fin 9) : V := i.castLE (by decide)

private theorem cell_essential (i : Fin 9) : cell i ∈ essential (rows : Family V) := by
  have cover : ∀ j : Fin 9, ∃ r ∈ rows, cell j ∈ r := by decide +kernel
  have minima : ∀ r ∈ rows, ∀ s ∈ rows, s ⊆ r → r ⊆ s := by decide +kernel
  obtain ⟨r, hr, hi⟩ := cover i
  exact ⟨r, ⟨hr, minima r hr⟩, hi⟩

/-- The nine grid points are essential. The octahedral boundary has only six vertices. -/
theorem not_conjecture : ¬ Conjecture := by
  intro h
  obtain ⟨T₁, T₂, _, e, _⟩ := h 2 V graph rows columns pure_closed grid_dual
  let f (i : Fin 9) : Fin (2 + 1) × Bool := (e ⟨cell i, cell_essential i⟩).val
  have inj : Function.Injective f := by
    intro i j hij
    have he := e.injective (Subtype.ext hij)
    exact Fin.ext (congrArg (fun v : essential (rows : Family V) => v.val.val) he)
  have bound := Fintype.card_le_of_injective f inj
  simp at bound

end OlarteSantosSpreerStump
