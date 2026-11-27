module

public import conjectures.WangLocalDensity.BranchAverage
import Mathlib.Tactic.Linarith

@[expose] public section
namespace WangLocalDensity
open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem split_disconnected {S : Finset V} (proper : S≠univ) (bad : ¬ Conn G Sᶜ) :
    ∃ A B : Finset V, S∪A∪B=univ ∧ Disjoint S A ∧ Disjoint S B ∧ Disjoint A B ∧
      A.Nonempty ∧ B.Nonempty ∧ ∀ a∈A,∀ b∈B,¬G.Adj a b := by
  classical
  let C := Sᶜ
  let H := G.induce (C : Set V)
  have hn : C.Nonempty := by
    by_contra! h
    have eq : S=univ := by
      ext x
      have hx : x∉C := by rw [h]; simp
      simpa [C] using hx
    exact proper eq
  obtain ⟨a,ha⟩ := hn
  let root : C := ⟨a,ha⟩
  have fail : ¬ ∀ b : C, H.Reachable root b := fun h =>
    bad ((SimpleGraph.connected_iff_exists_forall_reachable H).mpr ⟨root,h⟩)
  obtain ⟨b,hb⟩ := not_forall.mp fail
  let A := C.filter (fun x => ∃ hx : x∈C,H.Reachable root ⟨x,hx⟩)
  let B := C\A
  have inA : a∈A := mem_filter.mpr ⟨ha,ha,.rfl⟩
  have inB : b.val∈B := mem_sdiff.mpr ⟨b.property,fun e => by
    obtain ⟨_,h⟩ := (mem_filter.mp e).2
    exact hb h⟩
  refine ⟨A,B,?_,?_,?_,?_,⟨_,inA⟩,⟨_,inB⟩,?_⟩
  · ext x
    by_cases hs : x∈S <;> by_cases e : x∈A <;> simp [B,C,hs,e]
  · exact disjoint_left.mpr fun x hx h => (mem_compl.mp (mem_filter.mp h).1) hx
  · exact disjoint_left.mpr fun x hx h => (mem_compl.mp (mem_sdiff.mp h).1) hx
  · exact disjoint_left.mpr fun _ hx hb => (mem_sdiff.mp hb).2 hx
  · intro u hu v hv edge
    obtain ⟨hcu,⟨_,path⟩⟩ := mem_filter.mp hu
    obtain ⟨hcv,out⟩ := mem_sdiff.mp hv
    exact out (mem_filter.mpr ⟨hcv,hcv,path.trans
      ((show H.Adj ⟨u,hcu⟩ ⟨v,hcv⟩ from edge).reachable)⟩)

/-- Every proper connected set can be extended to one whose complement
    is connected, without decreasing its local density. -/
theorem connected_complement_extension (hc : G.Connected) {S : Finset V} (hS : Conn G S)
    (proper : S≠univ) : ∃ W : Finset V, S⊆W ∧ Conn G W ∧ W≠univ ∧ Conn G Wᶜ ∧
      density G S≤density G W := by
  classical
  let K := (univ : Finset (Finset V)).filter (fun W =>
    S⊆W ∧ Conn G W ∧ W≠univ ∧ density G S≤density G W)
  have start : S∈K := mem_filter.mpr ⟨mem_univ _,Subset.rfl,hS,proper,le_rfl⟩
  obtain ⟨W,hit,largest⟩ := K.exists_max_image Finset.card ⟨_,start⟩
  obtain ⟨sub,cw,pw,den⟩ := (mem_filter.mp hit).2
  refine ⟨W,sub,cw,pw,?_,den⟩
  by_contra bad
  obtain ⟨A,B,all,dWA,dWB,dAB,ha,hb,sep⟩ := split_disconnected pw bad
  have full : Conn G (W∪A∪B) := by
    rw [Conn,all,coe_univ]
    exact (induceUnivIso G).connected_iff.mpr hc
  obtain ⟨ca,cb⟩ := (connected_split cw sep).mp full
  have drop {X Y : Finset V} (dx : Disjoint W X) (dy : Disjoint W Y) (dxy : Disjoint X Y)
      (hx : X.Nonempty) (hy : Y.Nonempty) (cx : Conn G (W∪X)) :
      density G (W∪X)<density G W := by
    by_contra! notless
    have p : W∪X≠univ := by
      rintro eq
      obtain ⟨y,hy'⟩ := hy
      have mem : y∈W∪X := eq ▸ mem_univ _
      rcases mem_union.mp mem with wy | xy
      · exact disjoint_left.mp dy wy hy'
      · exact disjoint_left.mp dxy xy hy'
    have hit' : W∪X∈K := mem_filter.mpr ⟨mem_univ _,sub.trans subset_union_left,cx,p,den.trans notless⟩
    have impossible := largest _ hit'
    rw [card_union_of_disjoint dx] at impossible
    exact (Nat.not_le_of_lt (Nat.lt_add_of_pos_right hx.card_pos)) impossible
  have la := drop dWA dWB dAB ha hb ca
  have lb := drop dWB dWA dAB.symm hb ha cb
  have ap : 0<(A.card:ℚ) := by exact_mod_cast ha.card_pos
  have bp : 0<(B.card:ℚ) := by exact_mod_cast hb.card_pos
  have eq := branch_average hc cw all dWA dWB dAB ha hb sep
  linarith only [eq, mul_lt_mul_of_pos_left lb ap, mul_lt_mul_of_pos_left la bp]

end WangLocalDensity
