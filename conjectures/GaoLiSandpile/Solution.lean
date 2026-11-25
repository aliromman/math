module

public import conjectures.GaoLiSandpile.Statement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section
namespace GaoLiSandpile.Necklace
open SimpleGraph Matrix Finset

abbrev Slot (h : ℕ) := Bool ⊕ Fin h
abbrev Vertex (h : ℕ) := Fin 3 × Slot h
private abbrev left {h} : Slot h := .inl false
private abbrev right {h} : Slot h := .inl true
private abbrev middle {h} (j : Fin h) : Slot h := .inr j

def adjacent {h} (i j : Fin 3) : Slot h → Slot h → Prop
  | .inl false, .inl true => j+1=i
  | .inl true, .inl false => i+1=j
  | .inl _, .inl _ => False
  | .inr k, .inr l => i=j ∧ k≠l
  | _, _ => i=j

/-- Join three copies of a clique minus its terminal edge in a ring.
Each block has two terminals and h interior vertices. -/
def graph (h : ℕ) : SimpleGraph (Vertex h) where
  Adj v w := adjacent v.1 w.1 v.2 w.2
  symm := by
    constructor
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    rcases a with (_ | _) | k <;> rcases b with (_ | _) | l <;>
      simp_all [adjacent, eq_comm]
  loopless := by
    constructor
    rintro ⟨i,a⟩
    rcases a with (_ | _) | k <;> simp [adjacent]

instance (h) : DecidableRel (graph h).Adj := by
  rintro ⟨i,a⟩ ⟨j,b⟩
  rcases a with (_ | _) | k <;> rcases b with (_ | _) | l <;>
    dsimp [graph, adjacent] <;> infer_instance

/-- The neighbors of an interior vertex are the other vertices of its block.
A terminal sees its block's interior and the matching external terminal. -/
private def total {h} (f : Vertex h → ℤ) (v : Vertex h) : ℤ :=
  let i := v.1
  let s := ∑ k : Fin h, f (i,middle k)
  match v.2 with
  | .inl false => s + f (i-1,right)
  | .inl true => s + f (i+1,left)
  | .inr k => s - f (i,middle k) + f (i,left) + f (i,right)

private lemma except_one {h} (k : Fin h) (f : Fin h → ℤ) :
    (∑ j, if k=j then 0 else f j) = ∑ j, f j - f k := by
  have split : (∑ j, if k=j then f j else 0) + (∑ j, if k=j then 0 else f j) =
      ∑ j, f j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases e : k=j <;> simp [e]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at split
  omega

private lemma sum_total {h} (f : Vertex h → ℤ) (v : Vertex h) :
    (∑ w : Vertex h, if (graph h).Adj v w then f w else 0) = total f v := by
  obtain ⟨i,a⟩ := v
  rcases a with (_ | _) | k <;> fin_cases i <;>
    simp [Fintype.sum_prod_type, Fintype.sum_sum_type, Fin.sum_univ_three,
      graph, adjacent, total, except_one, Fin.reduceFinMk, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] <;> rfl

theorem degree {h : ℕ} (v : Vertex h) : (graph h).degree v = h+1 := by
  have row := (graph h).degree_eq_sum_if_adj (R:=ℤ) v
  rw [sum_total (fun _ => (1:ℤ))] at row
  obtain ⟨i,a⟩ := v
  rcases a with (_ | _) | k <;> simp [total] at row <;> omega

private lemma full_row {h} (f : Vertex h → ℤ) (v : Vertex h) :
    ((graph h).lapMatrix ℤ *ᵥ f) v = ((h:ℤ)+1)*f v - total f v := by
  rw [lapMatrix_mulVec_apply,degree,Nat.cast_add,Nat.cast_one,← sum_total]
  have hn : (graph h).neighborFinset v = univ.filter ((graph h).Adj v) := by ext; simp
  rw [hn,Finset.sum_filter]

private lemma reduced_row {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℤ)
    (s : V) (f : V → ℤ) (hs : f s=0) (v : Nonsinks s) :
    (A.submatrix Subtype.val Subtype.val *ᵥ fun w : Nonsinks s => f w.val) v =
      (A *ᵥ f) v.val := by
  change ∑ w : Nonsinks s, A v.val w.val * f w.val = ∑ w : V, A v.val w * f w
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun w => A v.val w * f w) s]
  simp [hs]

private def kind {h} : Slot h → Fin 3
  | .inl false => 0
  | .inl true => 2
  | .inr _ => 1

private def at3 (i : Fin 3) (x y z : ℤ) : ℤ := if i=0 then x else if i=1 then y else z

private def terminal (h : ℤ) (i k : Fin 3) : ℤ :=
  let d := h+2
  at3 i (at3 k 0 (2*d-2) (3*d-2))
    (at3 k (d^2) (d^2+d-2) (d^2+d-2))
    (at3 k (d^2) (d^2-2) (d^2-d-2))

private def interior (h : ℤ) (i k : Fin 3) : ℤ :=
  let d := h+2
  let x := h*(d+4)
  at3 i (at3 k (4*h) (3*h) (4*h)) (at3 k x (x+d-1) (x+d)) (at3 k (x+d) (x+d-1) x)

private def template {h} (s : Vertex h) (i k : Fin 3) : ℤ :=
  match s.2 with
  | .inl false => terminal h (i-s.1) k
  | .inl true => terminal h (s.1-i) (2-k)
  | .inr _ => interior h (i-s.1) k

/-- An integer solution of the Poisson equation off the sink. -/
private def potential {h} (s v : Vertex h) : ℤ :=
  template s v.1 (kind v.2) - if s=v then template s s.1 (kind s.2) else 0

private lemma middle_sum {h} (s : Vertex h) (i : Fin 3) :
    (∑ j : Fin h, potential s (i,middle j)) = (h:ℤ) * template s i 1 -
      (if i=s.1 ∧ kind s.2=1 then template s s.1 1 else 0) := by
  obtain ⟨a,t⟩ := s
  rcases t with (_ | _) | k <;> by_cases he : i=a <;>
    simp_all [potential,kind,Finset.sum_sub_distrib, middle, eq_comm]

private lemma poisson {h} (s v : Vertex h) (hne : s≠v) :
    ((graph h).lapMatrix ℤ *ᵥ potential s) v = h := by
  rw [full_row]
  obtain ⟨a,t⟩ := s
  obtain ⟨b,u⟩ := v
  rcases t with (_ | _) | k <;> rcases u with (_ | _) | j <;>
    simp only [total, middle_sum] <;>
    fin_cases a <;> fin_cases b <;>
    simp [Fin.reduceFinMk] at hne <;>
    simp_all (config := {decide := true}) [potential, template, terminal, interior, at3,
      kind, left, right, middle, Fin.reduceFinMk] <;> ring

theorem complete_maximal_identity (h : ℕ) : CompleteMaximalIdentity (graph h) := by
  intro s
  constructor
  · refine ⟨fun v => by simp [maximal,degree],?_⟩
    intro d hd
    refine ⟨fun v => h-d v,?_⟩
    have equal : (d + fun v => h - d v) = maximal (graph h) s := by
      funext v
      have hv := hd v
      rw [degree] at hv
      change d v+(h-d v)=(graph h).degree v.val-1
      rw [degree]
      omega
    rw [equal]
  · refine ⟨fun w => potential s w.val,?_⟩
    funext v
    rw [reduced_row _ s _ (by simp [potential]), poisson s v.val (Ne.symm v.property)]
    simp [maximal,degree]


private def project {h} (v : Vertex h) : Vertex 1 :=
  (v.1, match v.2 with | .inl b => .inl b | .inr _ => middle 0)

private def representative (h : ℕ) [NeZero h] (v : Vertex 1) : Vertex h :=
  (v.1, match v.2 with | .inl b => .inl b | .inr _ => middle 0)

private lemma project_rep (h : ℕ) [NeZero h] (v : Vertex 1) :
    project (representative h v) = v := by
  obtain ⟨i,b | j⟩ := v
  · rfl
  · fin_cases j
    rfl

private lemma projected_edge {h} {v w : Vertex h}
    (e : (graph 1).Adj (project v) (project w)) : (graph h).Adj v w := by
  obtain ⟨i,a⟩ := v
  obtain ⟨j,b⟩ := w
  rcases a with (_|_) | k <;> rcases b with (_|_) | l <;>
    simp_all [project, graph, adjacent, middle]

private lemma to_rep {h} [NeZero h] {v : Vertex h} {d : Vertex 1}
    (e : (graph 1).Adj (project v) d) : (graph h).Adj v (representative h d) := by
  apply projected_edge
  rwa [project_rep]

private lemma connected_by_descent {V : Type} (G : SimpleGraph V) (r : V)
    (height : V → ℕ) (h : ∀ v, v≠r → ∃ u, G.Adj v u ∧ height u < height v) :
    G.Connected := by
  have toward (v : V) : G.Reachable v r := by
    induction hv : height v using Nat.strong_induction_on generalizing v with
    | _ n ih =>
      by_cases hr : v=r
      · exact hr ▸ SimpleGraph.Reachable.rfl
      · obtain ⟨u,adj,lt⟩ := h v hr
        exact adj.reachable.trans (ih (height u) (lt.trans_eq hv) u rfl)
  exact (connected_iff_exists_forall_reachable G).mpr ⟨r, fun v => (toward v).symm⟩

private def index (v : Vertex 1) : ℕ := 3*v.1.val+(kind v.2).val

private lemma core_biconnected : Biconnected (graph 1) := by
  constructor
  · apply connected_by_descent _ (0,left) index
    decide
  · intro x
    have cert : ∀ x : Vertex 1, ∃ r, r≠x ∧ ∀ v, v≠x → v≠r →
        ∃ w, w≠x ∧ (graph 1).Adj v w ∧
          (index w+17-index x)%9 < (index v+17-index x)%9 := by decide
    obtain ⟨r,hr,step⟩ := cert x
    apply connected_by_descent _ (⟨r,hr⟩ : Nonsinks x) (fun v => (index v.val+17-index x)%9)
    intro v hv
    obtain ⟨w,hw,he,hl⟩ := step v.val v.property (fun e => hv (Subtype.ext e))
    exact ⟨⟨w,hw⟩,he,hl⟩

private lemma connected_from_core {C V : Type} {H : SimpleGraph C} {G : SimpleGraph V}
    (f : H →g G) (hc : H.Connected) (cover : ∀ v, ∃ c, G.Adj v (f c)) : G.Connected := by
  obtain ⟨r,hr⟩ := (connected_iff_exists_forall_reachable H).mp hc
  apply (connected_iff_exists_forall_reachable G).mpr
  refine ⟨f r,fun v => ?_⟩
  obtain ⟨c,edge⟩ := cover v
  exact ((hr c).map f).trans edge.symm.reachable

private lemma core_neighbor : ∀ y x : Vertex 1, ∃ d, d≠x ∧ (graph 1).Adj y d := by decide

/-- Retain one interior vertex per block to obtain a nine-vertex cycle.
Delete the position of the removed vertex on this cycle. Each remaining
vertex is adjacent to a surviving representative. -/
theorem biconnected (h : ℕ) [NeZero h] : Biconnected (graph h) := by
  constructor
  · let f : graph 1 →g graph h :=
      ⟨representative h,fun {a b} e => to_rep (by simpa only [project_rep] using e)⟩
    apply connected_from_core f core_biconnected.1
    intro v
    obtain ⟨w,_,e⟩ := core_neighbor (project v) (project v)
    exact ⟨w,to_rep e⟩
  · intro x
    let rep (c : Nonsinks (project x)) : Nonsinks x :=
      ⟨representative h c.val, fun eq => c.property ((project_rep h c.val).symm.trans (congrArg project eq))⟩
    let f : (graph 1).induce {c | c≠project x} →g (graph h).induce {v | v≠x} :=
      ⟨rep,by
        intro a b e
        change (graph h).Adj (representative h a.val) (representative h b.val)
        apply to_rep
        simpa only [project_rep] using (show (graph 1).Adj a.val b.val from e)⟩
    apply connected_from_core f (core_biconnected.2 (project x))
    intro v
    obtain ⟨w,hw,e⟩ := core_neighbor (project v.val) (project x)
    exact ⟨⟨w,hw⟩,to_rep e⟩

theorem order (h : ℕ) : Fintype.card (Vertex h) = 3*(h+2) := by
  simp [Vertex, Slot, Nat.add_comm]

private lemma cycle_degree {n : ℕ} (h : 3≤n) (v : Fin n) : (cycleGraph n).degree v=2 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le' h
  exact cycleGraph_degree_three_le

/-- Every odd interior count at least three gives an odd biconnected counterexample. -/
theorem odd_counterexamples (h : ℕ) (hh : 3≤h) (odd : Odd h) :
    Odd (Fintype.card (Vertex h)) ∧ Biconnected (graph h) ∧ CompleteMaximalIdentity (graph h) ∧
      ¬(Nonempty (graph h ≃g cycleGraph (Fintype.card (Vertex h))) ∨ graph h=⊤) := by
  let : NeZero h := ⟨by omega⟩
  have ho := order h
  refine ⟨?_,biconnected h,complete_maximal_identity h,?_⟩
  · obtain ⟨k,hk⟩ := odd
    exact ⟨3*k+4,by omega⟩
  · intro alternative
    rcases alternative with iso | top
    · obtain ⟨f⟩ := iso
      let v : Vertex h := (0,left)
      have d := f.degree_eq v
      rw [degree, cycle_degree (by omega)] at d
      omega
    · have edge : (graph h).Adj (0,left) (0,right) := by
        rw [top]
        simp [left,right]
      have absent : ¬(graph h).Adj (0,left) (0,right) := by
        change ¬ ((0 : Fin 3)+1=0)
        decide
      exact absent edge

end GaoLiSandpile.Necklace

namespace GaoLiSandpile

theorem not_conjecture : ¬ Conjecture := by
  intro claim
  obtain ⟨o,b,m,other⟩ := Necklace.odd_counterexamples 3 (by decide) (by decide)
  exact other (claim _ (Necklace.graph 3) o b m)

/-- info: 'GaoLiSandpile.Necklace.odd_counterexamples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Necklace.odd_counterexamples

/-- info: 'GaoLiSandpile.not_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_conjecture

end GaoLiSandpile
