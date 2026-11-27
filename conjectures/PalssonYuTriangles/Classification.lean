module

public import conjectures.PalssonYuTriangles.Tables
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Tauto

@[expose] public section

set_option maxRecDepth 16000

namespace PalssonYu

abbrev Vertex := Fin 7
abbrev Row := List ℕ
variable {α : Type*}

def triangleSides (c : Vertex → Vertex → α) (a b d : Vertex) : Multiset α :=
  {c a b, c a d, c b d}

def FewTypes (c : Vertex → Vertex → α) : Prop :=
  ∃ T : Finset (Multiset α), T.card ≤ 4 ∧
    ∀ a b d, a ≠ b → a ≠ d → b ≠ d → triangleSides c a b d ∈ T

def NoMonoFour (c : Vertex → Vertex → α) : Prop :=
  ∀ a b d e, [a,b,d,e].Nodup → ¬(c a b = c a d ∧ c a b = c a e ∧
    c a b = c b d ∧ c a b = c b e ∧ c a b = c d e)

def TwoCenters (c : Vertex → Vertex → α) : Prop :=
  ∀ a b x y z, [a,b,x,y,z].Nodup → ¬(c a x = c a y ∧ c a x = c a z ∧
    c b x = c b y ∧ c b x = c b z)

private def edges : List (Vertex × Vertex) :=
  (List.finRange 7).flatMap fun b =>
    ((List.finRange 7).filter (· < b)).map fun a => (a,b)

def edgeIndex (a b : Vertex) : ℕ :=
  let j := max a.val b.val
  j * (j - 1) / 2 + min a.val b.val

def entry (s : Row) (i j : Vertex) : ℕ := s[edgeIndex i j]!

theorem entry_comm (s : Row) (i j : Vertex) : entry s i j = entry s j i := by
  simp only [entry, edgeIndex, max_comm i.val j.val, min_comm i.val j.val]

private def vector (c : Vertex → Vertex → α) (i : ℕ) : α :=
  let e := edges[i]!
  c e.1 e.2

private theorem vector_index (c : Vertex → Vertex → α) (sym : ∀ a b, c a b = c b a)
    {i j : Vertex} (ne : i ≠ j) : vector c (edgeIndex i j) = c i j := by
  have table : ∀ (a b : Vertex), a ≠ b →
      edges[edgeIndex a b]! = (a,b) ∨ edges[edgeIndex a b]! = (b,a) := by decide
  rcases table i j ne with h | h <;> simp only [vector, h]
  exact sym _ _

/-- The colors agree on exactly the same pairs of entries in this prefix. -/
private def Models (v : ℕ → α) (s : Row) : Prop :=
  ∀ i j, i < s.length → j < s.length → (v i = v j ↔ s[i]! = s[j]!)

private def high (s : Row) : ℕ := s.foldr max 0 + 1

private theorem lt_high {s : Row} {i : ℕ} (hi : i < s.length) : s[i]! < high s := by
  rw [getElem!_pos s i hi]
  suffices ∀ x ∈ s, x ≤ s.foldr max 0 from
    Nat.lt_succ_of_le (this _ (List.getElem_mem hi))
  clear hi i
  induction s with
  | nil => simp
  | cons a l ih =>
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · subst x; exact le_max_left _ _
    · exact le_trans (ih _ h) (le_max_right _ _)

private theorem models_extend {v : ℕ → α} {s : Row} (h : Models v s) :
    ∃ a < high s + 1, Models v (s ++ [a]) := by
  classical
  let t := s.length
  have aux (a : ℕ) (ha : ∀ i, i < t → (v i = v t ↔ s[i]! = a)) :
      Models v (s ++ [a]) := by
    intro i j hi hj
    simp only [List.length_append, List.length_cons, List.length_nil] at hi hj
    rcases Nat.lt_or_eq_of_le (show i ≤ t by omega) with hi' | rfl
    · rcases Nat.lt_or_eq_of_le (show j ≤ t by omega) with hj' | rfl
      · change i < s.length at hi'
        change j < s.length at hj'
        simpa [List.getElem?_append, hi', hj', t] using h i j hi' hj'
      · change i < s.length at hi'
        simpa [t, List.getElem?_append, hi'] using ha i hi'
    · rcases Nat.lt_or_eq_of_le (show j ≤ t by omega) with hj' | rfl
      · change j < s.length at hj'
        simpa [eq_comm, t, List.getElem?_append, hj'] using ha j hj'
      · simp
  by_cases he : ∃ i < t, v i = v t
  · obtain ⟨i,hi,he⟩ := he
    exact ⟨s[i]!, by have := lt_high hi; omega, aux _ fun j hj => by rw [← he]; exact h j i hj hi⟩
  · refine ⟨high s, Nat.lt_succ_self _, aux _ fun j hj => ?_⟩
    exact iff_of_false (fun eq => he ⟨j,hj,eq⟩) (Nat.ne_of_lt (lt_high hj))

private theorem models_encoder {v : ℕ → α} {s : Row} (h : Models v s) :
    ∃ f : α → ℕ, ∀ i < s.length, f (v i) = s[i]! := by
  classical
  let f (x : α) := if hx : ∃ i < s.length, v i = x then s[hx.choose]! else 0
  refine ⟨f, fun i hi => ?_⟩
  have hx : ∃ j < s.length, v j = v i := ⟨i,hi,rfl⟩
  simp only [f, dite_eq_left hx]
  exact (h _ _ hx.choose_spec.1 hi).mp hx.choose_spec.2

private abbrev Face := Vertex × Vertex × Vertex

private def allFaces : List Face :=
  (List.finRange 7).flatMap fun a => (List.finRange 7).flatMap fun b =>
    ((List.finRange 7).filter (fun d => a < b && b < d)).map fun d => (a,b,d)

private def faceEdges (t : Face) : ℕ × ℕ × ℕ :=
  (edgeIndex t.1 t.2.1, edgeIndex t.1 t.2.2, edgeIndex t.2.1 t.2.2)

private def knownFace (n : ℕ) (t : Face) : Bool :=
  let (i,j,k) := faceEdges t
  i < n && j < n && k < n

private def tripleOf (v : ℕ → α) (t : Face) : Multiset α :=
  let (i,j,k) := faceEdges t
  {v i, v j, v k}

private def kinds (s : Row) : Finset (Multiset ℕ) :=
  ((allFaces.filter (knownFace s.length)).map (tripleOf (fun i => s[i]!))).toFinset

private theorem kinds_bound {c : Vertex → Vertex → α} (sym : ∀ a b, c a b = c b a)
    (hf : FewTypes c) {s : Row} (hs : Models (vector c) s) : (kinds s).card ≤ 4 := by
  classical
  obtain ⟨f,hf'⟩ := models_encoder hs
  obtain ⟨T,hT,hmem⟩ := hf
  have sub : kinds s ⊆ T.image (Multiset.map f) := by
    intro m hm
    obtain ⟨⟨a,b,d⟩,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    obtain ⟨ht,hk⟩ := List.mem_filter.mp ht
    have ordered : ∀ t ∈ allFaces, t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by decide
    obtain ⟨ab,bd⟩ := ordered _ ht
    have ad := ab.trans bd
    simp only [knownFace, faceEdges, Bool.and_eq_true] at hk
    refine Finset.mem_image.mpr ⟨_, hmem a b d ab.ne ad.ne bd.ne, ?_⟩
    simp only [tripleOf, faceEdges, triangleSides]
    rw [← hf' _ (of_decide_eq_true hk.1.1), ← hf' _ (of_decide_eq_true hk.1.2), ← hf' _ (of_decide_eq_true hk.2)]
    rw [vector_index c sym ab.ne, vector_index c sym ad.ne, vector_index c sym bd.ne]
    rfl
  exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans hT)

/-- Each row lists triangles completed by the last edge of a prefix of that length. -/
private def lastFaces : Array (List (ℕ × ℕ × ℕ)) := #[
  [],
  [],
  [],
  [(0,1,2)],
  [],
  [(0,3,4)],
  [(1,3,5),(2,4,5)],
  [],
  [(0,6,7)],
  [(1,6,8),(2,7,8)],
  [(3,6,9),(4,7,9),(5,8,9)],
  [],
  [(0,10,11)],
  [(1,10,12),(2,11,12)],
  [(3,10,13),(4,11,13),(5,12,13)],
  [(6,10,14),(7,11,14),(8,12,14),(9,13,14)],
  [],
  [(0,15,16)],
  [(1,15,17),(2,16,17)],
  [(3,15,18),(4,16,18),(5,17,18)],
  [(6,15,19),(7,16,19),(8,17,19),(9,18,19)],
  [(10,15,20),(11,16,20),(12,17,20),(13,18,20),(14,19,20)]]

/-- The base-four digits give the multiplicities of the three edge colors. -/
private def kindCode (m : Multiset ℕ) : ℕ := (m.map (4 ^ ·)).sum

private def colorSet (s : Row) : Finset ℕ := (kinds s).image kindCode

private def newKinds (s : Row) : Finset ℕ :=
  ((lastFaces[s.length]!).map (fun (i,j,k) => 4 ^ s[i]! + 4 ^ s[j]! + 4 ^ s[k]!)).toFinset

private theorem newKinds_sub (s : Row) : newKinds s ⊆ colorSet s := by
  have cache : ∀ n : Fin 22, ∀ t ∈ lastFaces[n.val]!,
      t ∈ ((allFaces.filter (knownFace n.val)).map faceEdges) := by decide +kernel
  by_cases hn : s.length < 22
  · intro value hv
    obtain ⟨⟨i,j,k⟩,hjk,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (cache ⟨_,hn⟩ _ hjk)
    refine Finset.mem_image.mpr ⟨tripleOf (fun a => s[a]!) t,
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩), ?_⟩
    simp [kindCode, tripleOf, he, add_assoc]
  · have bound : lastFaces.size = 22 := by decide
    have out : ¬s.length < lastFaces.size := by omega
    change ((lastFaces[s.length]!).map _).toFinset ⊆ _
    rw [getElem!_neg lastFaces s.length out]
    exact Finset.empty_subset _

private theorem colorSet_extend (s : Row) (a : ℕ) : colorSet s ⊆ colorSet (s ++ [a]) := by
  apply Finset.image_mono
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  obtain ⟨hm,hk⟩ := List.mem_filter.mp ht
  have he : ∃ i j k, faceEdges t = (i,j,k) := ⟨_,_,_,rfl⟩
  obtain ⟨i,j,k,he⟩ := he
  simp only [knownFace, he, Bool.and_eq_true] at hk
  have hi := of_decide_eq_true hk.1.1
  have hj := of_decide_eq_true hk.1.2
  have hl := of_decide_eq_true hk.2
  apply List.mem_toFinset.mpr
  refine List.mem_map.mpr ⟨t,List.mem_filter.mpr ⟨hm,?_⟩,?_⟩
  · simp [knownFace, he, Nat.lt_add_one_of_le hi.le, Nat.lt_add_one_of_le hj.le, Nat.lt_add_one_of_le hl.le]
  · simp [tripleOf, he, List.getElem?_append, hi, hj, hl]

private inductive Veto
  | four (a b d e : Vertex)
  | centers (a b x y z : Vertex)

private def same (s : Row) (a b x y : Vertex) : Bool :=
  let i := edgeIndex a b
  let j := edgeIndex x y
  i < s.length && j < s.length && s[i]! == s[j]!

private def blocks (s : Row) : Veto → Bool
  | .four a b d e => decide [a,b,d,e].Nodup &&
    same s a b a d && same s a b a e && same s a b b d &&
    same s a b b e && same s a b d e
  | .centers a b x y z => decide [a,b,x,y,z].Nodup &&
    same s a x a y && same s a x a z && same s b x b y && same s b x b z

private theorem veto_false {c : Vertex → Vertex → α} (sym : ∀ a b, c a b = c b a)
    (hm : NoMonoFour c) (hp : TwoCenters c) {s : Row} (hs : Models (vector c) s)
    (w : Veto) : blocks s w = false := by
  have eq (a b x y : Vertex) (hab : a ≠ b) (hxy : x ≠ y) (h : same s a b x y) :
      c a b = c x y := by
    simp only [same, Bool.and_eq_true, beq_iff_eq] at h
    rw [← vector_index c sym hab, ← vector_index c sym hxy]
    exact (hs _ _ (of_decide_eq_true h.1.1) (of_decide_eq_true h.1.2)).mpr h.2
  apply Bool.eq_false_iff.mpr
  cases w with
  | four a b d e =>
    intro h
    simp only [blocks, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hn,h1⟩,h2⟩,h3⟩,h4⟩,h5⟩ := h
    have hn' := of_decide_eq_true hn
    apply hm _ _ _ _ hn'
    simp_all only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
      List.not_mem_nil, not_false_eq_true, and_true]
    exact ⟨eq _ _ _ _ (by tauto) (by tauto) h1, eq _ _ _ _ (by tauto) (by tauto) h2,
      eq _ _ _ _ (by tauto) (by tauto) h3, eq _ _ _ _ (by tauto) (by tauto) h4,
      eq _ _ _ _ (by tauto) (by tauto) h5⟩
  | centers a b x y z =>
    intro h
    simp only [blocks, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hn,h1⟩,h2⟩,h3⟩,h4⟩ := h
    have hn' := of_decide_eq_true hn
    apply hp _ _ _ _ _ hn'
    simp_all only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
      List.not_mem_nil, not_false_eq_true, and_true]
    exact ⟨eq _ _ _ _ (by tauto) (by tauto) h1, eq _ _ _ _ (by tauto) (by tauto) h2,
      eq _ _ _ _ (by tauto) (by tauto) h3, eq _ _ _ _ (by tauto) (by tauto) h4⟩

private def vertexMap (k : ℕ) (i : Vertex) : Vertex := ⟨k / 7 ^ i.val % 7, by omega⟩

private def reindex (k i : ℕ) : ℕ :=
  let (a,b) := edges[i]!
  edgeIndex (vertexMap k a) (vertexMap k b)

private def compatible (s t : Row) (k : ℕ) : Bool :=
  decide (Function.Injective (vertexMap k)) && decide (t.length ≤ 21) &&
    (List.range t.length).all fun i =>
      reindex k i < s.length && (List.range t.length).all fun j =>
        (s[reindex k i]! == s[reindex k j]!) == (t[i]! == t[j]!)

private def order (c : Vertex → Vertex → α) (p : Equiv.Perm Vertex) :
    Vertex → Vertex → α := fun i j => c (p i) (p j)

private theorem compatible_sound {c : Vertex → Vertex → α} (sym : ∀ a b, c a b = c b a)
    {s t : Row} (hs : Models (vector c) s) {k : ℕ} (hv : compatible s t k) :
    ∃ p : Equiv.Perm Vertex, Models (vector (order c p)) t := by
  simp only [compatible, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hv
  obtain ⟨⟨hin,hl⟩,he⟩ := hv
  have hin' := of_decide_eq_true hin
  have hl' := of_decide_eq_true hl
  let p := Equiv.ofBijective (vertexMap k) ⟨hin', Finite.surjective_of_injective hin'⟩
  have diag : ∀ i ∈ List.range 21, edges[i]!.1 ≠ edges[i]!.2 := by decide
  have cast (i : ℕ) (hi : i < t.length) :
      vector (order c p) i = vector c (reindex k i) := by
    have ne := diag i (List.mem_range.mpr (hi.trans_le hl'))
    exact (vector_index c sym (hin'.ne ne)).symm
  refine ⟨p, fun i j hi hj => ?_⟩
  rw [cast i hi, cast j hj, hs _ _ (of_decide_eq_true (he i hi).1)
    (of_decide_eq_true (he j hj).1)]
  have hh := (he i hi).2 j hj
  simpa using congrArg (fun b : Bool => b = true) hh

private def packed (s : Row) : ℕ := s.foldl (fun z a => 16 * z + a) 0

/-- Look up a candidate certificate. Every returned certificate is checked by `finish`. -/
private def proposal (h : Hints) (s : Row) : ℕ :=
  let k := packed s
  let d := h.offsets[(k % h.first) % h.offsets.size]!
  h.values[(k % h.second + d) % h.values.size]!

private def unpackVeto (k : ℕ) : Veto :=
  let p n := vertexMap k n
  let q n := vertexMap (k-2401) n
  if k < 2401 then .four (p 0) (p 1) (p 2) (p 3)
  else .centers (q 0) (q 1) (q 2) (q 3) (q 4)

/-- A terminal certificate specifies a forbidden configuration or a permutation to a listed row. -/
private def finish (targets : List Row) (hints : Hints) (s : Row) : Bool :=
  let w := proposal hints s
  if w < 32768 then blocks s (unpackVeto w)
  else match targets[(w-32768) % 32]? with
    | some t => compatible s t ((w-32768) / 32)
    | none => false

private def Reaches (c : Vertex → Vertex → α) (targets : List Row) : Prop :=
  ∃ p : Equiv.Perm Vertex, ∃ t ∈ targets, Models (vector (order c p)) t

private theorem finish_sound {c : Vertex → Vertex → α} (sym : ∀ a b, c a b = c b a)
    (hm : NoMonoFour c) (hp : TwoCenters c) {s : Row} (hs : Models (vector c) s)
    {R : List Row} {H : Hints} (h : finish R H s) : Reaches c R := by
  unfold finish at h
  dsimp only at h
  split at h
  · simp [veto_false sym hm hp hs] at h
  · split at h
    · rename_i t ht
      obtain ⟨p,hp'⟩ := compatible_sound sym hs h
      exact ⟨p,t,List.mem_of_getElem? ht,hp'⟩
    · contradiction

/-- Test every old color and one fresh color on the next edge. -/
private def checkTree (R : List Row) (H : Hints) : ℕ → Row → Finset ℕ → Bool
  | 0, s, P => (4 < P.card) || finish R H s
  | k + 1, s, P => (4 < P.card) ||
      (List.range (high s + 1)).all fun a => checkTree R H k (s ++ [a]) (P ∪ newKinds (s ++ [a]))

private theorem tree_sound {c : Vertex → Vertex → α} (sym : ∀ a b, c a b = c b a)
    (hf : FewTypes c) (hm : NoMonoFour c) (hp : TwoCenters c) {R : List Row}
    {H : Hints} {k : ℕ} {s : Row} (hs : Models (vector c) s)
    {P : Finset ℕ} (hP : P ⊆ colorSet s) (h : checkTree R H k s P) : Reaches c R := by
  induction k generalizing s P with
  | zero =>
    have ht := (Finset.card_le_card hP).trans (Finset.card_image_le.trans (kinds_bound sym hf hs))
    have hf' : finish R H s := by simpa [checkTree, Nat.not_lt.mpr ht] using h
    exact finish_sound sym hm hp hs hf'
  | succ k ih =>
    have ht := (Finset.card_le_card hP).trans (Finset.card_image_le.trans (kinds_bound sym hf hs))
    simp only [checkTree, Nat.not_lt.mpr ht, decide_false, Bool.false_or,
      List.all_eq_true, List.mem_range] at h
    obtain ⟨a,ha,has⟩ := models_extend hs
    exact ih has (Finset.union_subset (hP.trans (colorSet_extend s a)) (newKinds_sub _)) (h a ha)

private def stage (n : ℕ) (S R : List Row) (H : Hints) : Bool :=
  S.all fun s => checkTree R H (n-1) s (colorSet s)

private theorem advance {c : Vertex → Vertex → α} (sym : ∀ a b, c a b = c b a)
    (hf : FewTypes c) (hm : NoMonoFour c) (hp : TwoCenters c)
    {n : ℕ} {S R : List Row} {H : Hints} (test : stage n S R H) (hs : Reaches c S) :
    Reaches c R := by
  obtain ⟨p,s,hs,hmod⟩ := hs
  obtain ⟨T,hT,hmem⟩ := hf
  have hf' : FewTypes (order c p) :=
    ⟨T,hT,fun a b d ab ad bd => hmem _ _ _ (p.injective.ne ab) (p.injective.ne ad) (p.injective.ne bd)⟩
  have hm' : NoMonoFour (order c p) := fun a b d e h =>
    hm _ _ _ _ (by simpa [List.nodup_cons] using h)
  have hp' : TwoCenters (order c p) := fun a b x y z h =>
    hp _ _ _ _ _ (by simpa [List.nodup_cons] using h)
  obtain ⟨q,t,ht,hmq⟩ := tree_sound (c := order c p) (fun _ _ => sym _ _) hf' hm' hp' hmod
    (Finset.Subset.refl _) (List.all_eq_true.mp test _ hs)
  exact ⟨q.trans p,t,ht,hmq⟩

private theorem stage_cons {n : ℕ} {R : List Row} {H : Hints} {s : Row} {rest : List Row}
    (h : checkTree R H (n-1) s (colorSet s)) (tail : stage n rest R H) :
    stage n (s :: rest) R H := by
  change (_ && _) = true
  simp only [Bool.and_eq_true]
  exact ⟨h,tail⟩

section
set_option maxHeartbeats 0
set_option Elab.async false

private theorem stage3 : stage 3 rows2 rows3 hints3 := by decide +kernel

private theorem stage4 : stage 4 rows3 rows4 hints4 := by
  iterate 3
    apply stage_cons
    · decide +kernel
  rfl

-- Check each predecessor row in a separate kernel declaration.
private theorem stage5 : stage 5 rows4 rows5 hints5 := by
  iterate 24
    apply stage_cons
    · decide +kernel
  rfl

private theorem stage6 : stage 6 rows5 rows6 hints6 := by
  iterate 32
    apply stage_cons
    · decide +kernel
  rfl

private theorem stage7 : stage 7 rows6 patterns hints7 := by
  iterate 31
    apply stage_cons
    · decide +kernel
  rfl

end

/-- Every admissible seven-vertex edge coloring has one of the six listed equality patterns. -/
theorem classify_seven (c : Vertex → Vertex → α) (sym : ∀ a b, c a b = c b a)
    (hf : FewTypes c) (hm : NoMonoFour c) (hp : TwoCenters c) :
    ∃ p : Equiv.Perm Vertex, ∃ s ∈ patterns, ∀ i j k l : Vertex, i < j → k < l →
      (c (p i) (p j) = c (p k) (p l) ↔ entry s i j = entry s k l) := by
  have h2 : Reaches c rows2 := by
    refine ⟨Equiv.refl _,[0],by decide,fun i j hi hj => ?_⟩
    have ei : i = 0 := by simpa using hi
    have ej : j = 0 := by simpa using hj
    simp [ei,ej]
  have h3 := advance sym hf hm hp stage3 h2
  have h4 := advance sym hf hm hp stage4 h3
  have h5 := advance sym hf hm hp stage5 h4
  have h6 := advance sym hf hm hp stage6 h5
  obtain ⟨p,s,hs,hmod⟩ := advance sym hf hm hp stage7 h6
  have lens : ∀ s ∈ patterns, s.length = 21 := by decide
  have bound : ∀ (a b : Vertex), a < b → edgeIndex a b < 21 := by decide
  refine ⟨p,s,hs,fun i j k l hij hkl => ?_⟩
  have hs' : ∀ a b : Vertex, order c p a b = order c p b a := fun _ _ => sym _ _
  have h := hmod (edgeIndex i j) (edgeIndex k l) (by rw [lens _ hs]; exact bound _ _ hij)
    (by rw [lens _ hs]; exact bound _ _ hkl)
  rwa [vector_index _ hs' hij.ne, vector_index _ hs' hkl.ne] at h

theorem classify_seven_ne (c : Vertex → Vertex → α) (sym : ∀ a b, c a b = c b a)
    (hf : FewTypes c) (hm : NoMonoFour c) (hp : TwoCenters c) :
    ∃ p : Equiv.Perm Vertex, ∃ s ∈ patterns, ∀ i j k l : Vertex, i ≠ j → k ≠ l →
      (c (p i) (p j) = c (p k) (p l) ↔ entry s i j = entry s k l) := by
  obtain ⟨p,s,hs,h⟩ := classify_seven c sym hf hm hp
  refine ⟨p,s,hs,fun i j k l hij hkl => ?_⟩
  rcases lt_or_gt_of_ne hij with ij | ji <;> rcases lt_or_gt_of_ne hkl with kl | lk
  · exact h _ _ _ _ ij kl
  · rw [sym (p k) (p l), entry_comm s k l]
    exact h _ _ _ _ ij lk
  · rw [sym (p i) (p j), entry_comm s i j]
    exact h _ _ _ _ ji kl
  · rw [sym (p i) (p j), entry_comm s i j, sym (p k) (p l), entry_comm s k l]
    exact h _ _ _ _ ji lk

/-- info: 'PalssonYu.classify_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms classify_seven

end PalssonYu
