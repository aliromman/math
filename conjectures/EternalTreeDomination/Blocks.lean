module

public import conjectures.EternalTreeDomination.Tree

@[expose] public section
namespace EternalTreeDomination
open SimpleGraph
variable {I : Type*} [Fintype I] (B : SimpleGraph I)

private def depth : Fin 5 → ℕ | 0 => 3 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0

omit [Fintype I] in
private theorem far_leaf {i : I} {x : I×Fin 5} (h : (tree B).edist x (i,4)≤3) : x.1=i := by
  classical
  let f := fun v : I×Fin 5 ↦ if v.1=i then depth v.2 else 4
  have step {x y : I×Fin 5} (a : (tree B).Adj x y) : f y≤f x+1 := by
    rcases x with ⟨u,s⟩
    rcases y with ⟨v,t⟩
    change (u=v ∧ localAdj s t) ∨ (s=0 ∧ t=0 ∧ B.Adj u v) at a
    rcases a with ⟨rfl,e⟩|⟨rfl,rfl,_⟩
    · have local' : ∀ s t, localAdj s t → depth t≤depth s+1 := by decide
      by_cases eq : u=i <;> simp [f,eq,local' _ _ e]
    · by_cases u=i <;> by_cases v=i <;> simp_all [f, depth]
  rw [edist_comm] at h
  have low := grow_along_walk f step (k:=3) h
  by_contra e
  simp [f,e,depth] at low

private def side (s : Fin 5) : Bool := decide (s=3 ∨ s=4)
private def leaf (v : Bool) : Fin 5 := if v then 4 else 2

omit [Fintype I] in
private theorem close_leaf {i : I} {s : Bool} {p : I×Fin 5}
    (h : (tree B).edist p (i,leaf s)≤1) : (p.1,side p.2)=(i,s) := by
  have pair : ∀ (x : Fin 5) s, (localAdj x (leaf s) ∨ x=leaf s) → side x=s := by decide
  have nonzero : ∀ s, leaf s≠0 := by decide
  rcases edist_le_one_iff_adj_or_eq.mp h with a|rfl
  · rcases a with ⟨hi,hl⟩|⟨_,bad,_⟩
    · exact Prod.ext hi (pair p.2 s (Or.inl hl))
    · exact False.elim (nonzero s bad)
  · exact Prod.ext rfl (pair _ s (Or.inr rfl))

private theorem three_lower {r : ℕ} (h : domCount (tree B) 3 r) : Fintype.card I≤r := by
  obtain ⟨p,hp⟩ := h
  have sur : Function.Surjective (fun s : Fin r ↦ (p s).1) := by
    intro i
    obtain ⟨s,dist⟩ := hp (i,4)
    exact ⟨s,far_leaf B dist⟩
  simpa using Fintype.card_le_of_surjective _ sur

private theorem one_lower {r : ℕ} (h : domCount (tree B) 1 r) : 2*Fintype.card I≤r := by
  obtain ⟨p,hp⟩ := h
  have sur : Function.Surjective (fun s : Fin r ↦ ((p s).1,side (p s).2)) := by
    rintro ⟨i,x⟩
    obtain ⟨s,dist⟩ := hp (i,leaf x)
    exact ⟨s,close_leaf B dist⟩
  simpa [Nat.mul_comm] using Fintype.card_le_of_surjective _ sur

private theorem one_enough : domCount (tree B) 1 (2*Fintype.card I) := by
  let guard := fun x : I×Bool ↦ (x.1, if x.2 then (3 : Fin 5) else 1)
  have h : Dominates (tree B) 1 guard := by
    rintro ⟨i,s⟩
    refine ⟨(i,side s),?_⟩
    have atCenter : (if side s then (3:Fin 5) else 1)=center s := by simp [side,center]
    change (tree B).edist (i,if side s then 3 else 1) (i,s)≤1
    rw [atCenter,edist_comm]
    exact to_center _ _ _
  simpa [Nat.mul_comm] using domCount_of guard h

/-- One mobile guard in each block suffices, but a distance-one cover needs two. -/
theorem tree_numbers :
    gamma (tree B) 3=Fintype.card I ∧ eternal (tree B) 3=Fintype.card I ∧
      gamma (tree B) 1=2*Fintype.card I := by
  classical
  have enough := eternalCount_of (I:=I) (fun i ↦ (i,(1:Fin 5))) (block_defense 3 (tree B)
    (diameter_three B) (fun _ ↦ 1))
  exact ⟨min_eq (eternal_ge_dom enough) (fun _ ↦ three_lower B),
    min_eq enough (fun _ e ↦ three_lower B (eternal_ge_dom e)),min_eq (one_enough B) (fun _ ↦ one_lower B)⟩

end EternalTreeDomination
