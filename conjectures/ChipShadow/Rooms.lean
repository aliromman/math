module

public import conjectures.ChipShadow.Runs

@[expose] public section
noncomputable section
namespace ChipShadow

theorem initial_rooms (n : ℕ) (i : Fin (n+1)) : room (initial n) i=n+i.val := by
  have := i.isLt
  unfold room initial
  omega

theorem adjacent_iff {n : ℕ} {w : State n} (i : Fin n) :
    room w i.succ=room w i.castSucc+1 ↔ suite w i.castSucc=suite w i.succ := by
  change w i.succ+2*(i.val+1)=w i.castSucc+2*i.val+1 ↔ w i.castSucc+i.val=w i.succ+(i.val+1)
  omega

private theorem unique_block {n : ℕ} {w : State n} {B C : Block n} (h : IsBlock w B)
    (g : IsBlock w C) {i : Fin (n+1)} (hb : B.1≤i ∧ i≤B.2) (hc : C.1≤i ∧ i≤C.2) : B=C := by
  have e := ((h.2 i).mpr hb).symm.trans ((g.2 i).mpr hc)
  have bin := (g.2 B.1).mp e
  have cin := (h.2 C.1).mp e.symm
  have endB := (g.2 B.2).mp (((h.2 B.2).mpr ⟨h.1.le,le_rfl⟩).trans e)
  have endC := (h.2 C.2).mp (((g.2 C.2).mpr ⟨g.1.le,le_rfl⟩).trans e.symm)
  exact Prod.ext (le_antisymm cin.1 bin.1) (le_antisymm endB.2 endC.2)

/-- Every adjacent occupied pair is represented by exactly one run and cut. -/
theorem legal_pair {n : ℕ} {w : State n} (g : Good w) (i : Fin n) :
    room w i.succ=room w i.castSucc+1 ↔
      ∃! move : Block n × ℕ,move.1∈blocks w ∧ move.2<span move.1 ∧
        move.1.2.val=i.val+1+move.2 := by
  constructor
  · intro eq
    obtain ⟨B,mem,lo,hi⟩ := has_block g.sorted i ((adjacent_iff i).mp eq)
    have lo' : B.1.val≤i.val := lo
    have hi' : i.val+1≤B.2.val := hi
    let r := B.2.val-(i.val+1)
    refine ⟨(B,r),⟨mem,by dsimp [r,span];omega,by dsimp [r];omega⟩,?_⟩
    rintro ⟨C,s⟩ ⟨m,hs,e⟩
    change s<C.2.val-C.1.val at hs
    change C.2.val=i.val+1+s at e
    have eq' := unique_block (mem_blocks.mp m) (mem_blocks.mp mem)
      (i:=i.castSucc) ⟨show C.1.val≤i.val by omega,show i.val≤C.2.val by omega⟩
      ⟨lo,show i.val≤B.2.val by omega⟩
    change C=B at eq'
    subst C
    exact Prod.ext rfl (show s=r by dsimp [r];omega)
  · rintro ⟨⟨B,r⟩,⟨mem,lt,eq⟩,_⟩
    change r<B.2.val-B.1.val at lt
    change B.2.val=i.val+1+r at eq
    have h := mem_blocks.mp mem
    apply (adjacent_iff i).mpr
    exact ((h.2 i.castSucc).mpr ⟨show B.1.val≤i.val by omega,show i.val≤B.2.val by omega⟩).trans
      (((h.2 i.succ).mpr ⟨show B.1.val≤i.val+1 by omega,show i.val+1≤B.2.val by omega⟩).symm)

/-- Every indexed cut is a physical adjacent pair. -/
theorem pair_of_cut {n : ℕ} {w : State n} {B : Block n} (h : IsBlock w B)
    {r : ℕ} (hr : r<span B) :
    ∃ i : Fin n, B.2.val=i.val+1+r ∧ room w i.succ=room w i.castSucc+1 := by
  have lt : r<B.2.val-B.1.val := hr
  let i : Fin n := ⟨B.2.val-r-1,by have := B.2.isLt;omega⟩
  have idx : i.val=B.2.val-r-1 := rfl
  refine ⟨i,by omega,(adjacent_iff i).mpr ?_⟩
  exact ((h.2 i.castSucc).mpr ⟨show B.1.val≤i.val by omega,show i.val≤B.2.val by omega⟩).trans
    (((h.2 i.succ).mpr ⟨show B.1.val≤i.val+1 by omega,show i.val+1≤B.2.val by omega⟩).symm)

/-- In the run the lower ranks move left and the upper ranks move right. All other rooms agree. -/
theorem push_rooms {n : ℕ} {w : State n} {B : Block n} (h : IsBlock w B)
    {r : ℕ} (hr : r<span B) (j : Fin (n+1)) :
    room (push w B r) j=
      if B.1≤j ∧ j≤B.2 then
        if j.val<B.2.val-r then room w j-1 else room w j+1
      else room w j := by
  by_cases mem : B.1≤j ∧ j≤B.2
  · have v := suite_in h mem
    have lt : r<B.2.val-B.1.val := hr
    simp only [room,push,ite_eq_left mem]
    split_ifs <;> omega
  · simp [room,push,mem]

end ChipShadow
end
