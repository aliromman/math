module

public import conjectures.EternalTreeDomination.Blocks

public section
namespace EternalTreeDomination
open SimpleGraph

private theorem segment {n a : ℕ} (d : ℕ) (hb : a+d<n) :
    (pathGraph n).edist ⟨a,by omega⟩ ⟨a+d,hb⟩ ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    let b : Fin n := ⟨a+d,by omega⟩
    let c : Fin n := ⟨a+(d+1),hb⟩
    have edge : (pathGraph n).Adj b c := pathGraph_adj.mpr (Or.inl rfl)
    exact ((pathGraph n).edist_triangle (v:=b)).trans
      (add_le_add (ih (by omega)) (show (pathGraph n).edist b c≤1 from edist_le_one_iff_adj_or_eq.mpr (Or.inl edge)))

private theorem path_segment {n : ℕ} (a b : Fin n) (hab : a.val≤b.val) :
    (pathGraph n).edist a b ≤ (b.val-a.val : ℕ) := by
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  change a≤b at hab
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hab
  simpa using segment (a:=a) d hb

/-- The guard starts at the first vertex and moves to the most recent attack. -/
theorem odd_path_online (h : ℕ) :
    OnlineDefense (pathGraph (2*h+2)) (2*h+1)
      (fun _ : Fin 1 ↦ (⟨0, by omega⟩ : Fin (2*h+2))) := by
  let G := pathGraph (2*h+2)
  have dist (u v : Fin (2*h+2)) : G.edist u v≤(2*h+1 : ℕ) := by
    wlog huv : u.val≤v.val generalizing u v
    · rw [edist_comm]; exact this v u (by omega)
    refine (path_segment u v huv).trans ?_
    exact_mod_cast (show v.val-u.val≤2*h+1 by omega)
  refine ⟨fun history _ ↦ history.headD ⟨0, by omega⟩, rfl, ?_⟩
  exact fun history attack ↦ ⟨fun _ ↦ dist _ _, 0, rfl⟩

/-- At every odd radius, the path whose length equals that radius has the same obstruction. -/
theorem odd_path (h : ℕ) :
    let G := pathGraph (2*h+2)
    gamma G (2*h+1)=1 ∧ eternal G (2*h+1)=1 ∧ gamma G h=2 := by
  let G := pathGraph (2*h+2)
  let a : Fin (2*h+2) := ⟨0,by omega⟩
  let b : Fin (2*h+2) := ⟨2*h+1,by omega⟩
  have one : eternalCount G (2*h+1) 1 := ⟨fun _ ↦ a, (odd_path_online h).defends⟩
  have low {r k} : domCount G k r → 1≤r := by
    rintro ⟨_,hp⟩
    obtain ⟨s,_⟩ := hp a
    exact lt_of_le_of_lt (Nat.zero_le _) s.isLt
  let guards (s : Fin 2) := if s=0 then a else b
  have two : domCount G h 2 := by
    refine ⟨guards,fun v ↦ ?_⟩
    by_cases left : v.val≤h
    · refine ⟨0,(path_segment a v (by simp [a])).trans ?_⟩
      exact_mod_cast (show v.val-a.val≤h by simpa [a] using left)
    · refine ⟨1,?_⟩
      change G.edist b v≤h
      rw [edist_comm]
      refine (path_segment v b (by dsimp [b]; omega)).trans ?_
      exact_mod_cast (show b.val-v.val≤h by dsimp [b]; omega)
  have step {x y : Fin (2*h+2)} (e : G.Adj x y) : y.val≤x.val+1 := by
    rcases pathGraph_adj.mp e with e|e <;> omega
  have lowTwo {r} (D : domCount G h r) : 2≤r := by
    obtain ⟨p,cover⟩ := D
    obtain ⟨i,hi⟩ := cover a
    obtain ⟨j,hj⟩ := cover b
    have near := grow_along_walk Fin.val step (edist_comm ▸ hi)
    have far := grow_along_walk Fin.val step hj
    change (p i).val≤0+h at near
    change 2*h+1≤(p j).val+h at far
    have ne : i.val≠j.val := by
      intro ei
      have eq : i=j := Fin.ext ei
      subst j
      omega
    have := i.isLt
    have := j.isLt
    omega
  exact ⟨min_eq (eternal_ge_dom one) (fun _ ↦ low),min_eq one (fun _ e ↦ low (eternal_ge_dom e)),
    min_eq two (fun _ ↦ lowTwo)⟩

/-- The four-vertex path already refutes the proposed equality. -/
theorem path_four : gamma (pathGraph 4) 3=1 ∧ eternal (pathGraph 4) 3=1 ∧ gamma (pathGraph 4) 1=2 :=
  odd_path 1

/-- The additive gap takes every positive integer value. -/
theorem unbounded_gap (n : ℕ) (hn : 0<n) :
    let T := tree (pathGraph n)
    T.IsTree ∧ gamma T 3=n ∧ eternal T 3=n ∧ gamma T 1=2*n := by
  exact ⟨tree_isTree (isTree_pathGraph.mpr hn.ne'),by simpa using tree_numbers (pathGraph n)⟩

theorem resolution : ¬Conjecture := by
  intro conj
  obtain ⟨a,b,c⟩ := path_four
  have eq := conj (Fin 4) (pathGraph 4) (isTree_pathGraph_add_one 3) 3 (by decide) (a.trans b.symm)
  change eternal (pathGraph 4) 3=gamma (pathGraph 4) 1 at eq
  omega

/-- info: 'EternalTreeDomination.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'EternalTreeDomination.unbounded_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unbounded_gap

end EternalTreeDomination
