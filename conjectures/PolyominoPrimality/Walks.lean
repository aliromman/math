module

public import conjectures.PolyominoPrimality.Example

public section
namespace PolyominoPrimality

private theorem listed {t : Side} {rs : List Rect} (h : t.rect ∈ rs) :
    t ∈ rs.flatMap sides := by
  refine List.mem_flatMap.mpr ⟨t.rect,h,?_⟩
  obtain ⟨r,x,y,d⟩ := t
  cases x <;> cases y <;> cases d <;> simp [sides]

private def nextSides (rs : List Rect) (s : Side) : List Side :=
  let x := !(s.right != !s.vertical)
  let y := !(s.top != s.vertical)
  (rs.filter fun r => r.corner x y == s.w).flatMap fun r =>
    [⟨r,x,y,false⟩, ⟨r,x,y,true⟩]

private theorem mem_next {rs : List Rect} {s t : Side} (hr : t.rect ∈ rs)
    (h : s.follows t = true) : t ∈ nextSides rs s := by
  obtain ⟨r,x,y,v⟩ := t
  simp only [Side.follows,Bool.and_eq_true_iff,beq_iff_eq] at h
  obtain ⟨⟨eq,hx⟩,hy⟩ := h
  change x = _ at hx
  change y = _ at hy
  subst x
  subst y
  apply List.mem_flatMap.mpr
  refine ⟨r,List.mem_filter.mpr ⟨hr,?_⟩,?_⟩
  · exact beq_iff_eq.mpr eq.symm
  · cases v <;> simp

/-- Accept a closure, or a path that reaches the search limit. -/
private def testPath (rs : List Rect) (first current : Side)
    (marked : List Side) : ℕ → Bool
  | 0 => true
  | fuel+1 => current.follows first || (nextSides rs current).any fun t =>
      marked.all (fun s => separateMarks rs s t) &&
        testPath rs first t (t::marked) fuel

private theorem accepts (rs : List Rect) (first : Side) (fuel : ℕ)
    (current : Side) (rest marked : List Side)
    (mem : ∀ t ∈ rest, t.rect ∈ rs)
    (pw : rest.Pairwise (fun a b => separateMarks rs a b = true))
    (free : ∀ a ∈ marked, ∀ b ∈ rest, separateMarks rs a b = true)
    (chain : (current :: rest ++ [first]).IsChain (fun a b => a.follows b = true)) :
    testPath rs first current marked fuel = true := by
  induction fuel generalizing current rest marked with
  | zero => rfl
  | succ fuel ih =>
    cases rest with
    | nil => simpa [testPath] using Or.inl (List.isChain_cons_cons.mp chain).1
    | cons t ts =>
      obtain ⟨next,chain⟩ := List.isChain_cons_cons.mp chain
      obtain ⟨good,pw⟩ := List.pairwise_cons.mp pw
      apply Bool.or_eq_true_iff.mpr
      right
      apply List.any_eq_true.mpr
      refine ⟨t,mem_next (mem t (by simp)) next,?_⟩
      apply Bool.and_eq_true_iff.mpr
      refine ⟨List.all_eq_true.mpr (fun a ha => free a ha t (by simp)),?_⟩
      apply ih t ts (t::marked) (fun b hb => mem b (by simp [hb])) pw _ chain
      intro a ha b hb
      rcases List.mem_cons.mp ha with rfl | ha
      · exact good b hb
      · exact free a ha b (by simp [hb])

private def possible (cells : List Point) : Bool :=
  let rs := innerIntervals cells
  let all := rs.flatMap sides
  all.any fun s => testPath rs s s [s] 5

private theorem possible_of_walk {cells : List Point} (h : Zigzag cells) : possible cells = true := by
  obtain ⟨s,rest,hm,_,hp,hc⟩ := h
  unfold possible
  apply List.any_eq_true.mpr
  refine ⟨s,listed (hm s (by simp)),?_⟩
  apply accepts _ _ _ _ _ _ (fun t ht => hm t (by simp [ht]))
    (List.pairwise_cons.mp hp).2 _ hc
  intro a ha
  obtain rfl : a=s := by simpa using ha
  exact (List.pairwise_cons.mp hp).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked : possible exampleCells = false := by decide +kernel

theorem noZigzag : ¬ Zigzag exampleCells := by
  intro h
  have := possible_of_walk h
  simp [checked] at this

end PolyominoPrimality
