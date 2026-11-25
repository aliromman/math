module

public import conjectures.GaoLiSandpile.Statement
import Mathlib.Data.Fin.VecNotation

@[expose] public section
namespace GaoLiSandpile
open SimpleGraph Matrix

/-- Each block of five vertices is a clique with the edge 0--4 removed.
The last vertex of each block is joined to the first of the next. -/
def bracelet : SimpleGraph (Fin 15) where
  Adj v w := v≠w ∧ ((v.val/5=w.val/5 ∧ ¬ ((v.val%5=0 ∧ w.val%5=4) ∨
    (v.val%5=4 ∧ w.val%5=0))) ∨ (v+1=w ∧ v.val%5=4) ∨ (w+1=v ∧ w.val%5=4))
  symm := by constructor; decide
  loopless := ⟨fun v h => h.1 rfl⟩

instance : DecidableRel bracelet.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem degree_four : ∀ v : Fin 15, bracelet.degree v=4 := by decide

private theorem connected_by_descent {V : Type} (G : SimpleGraph V) (r : V)
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

private theorem biconnected : Biconnected bracelet := by
  constructor
  · apply connected_by_descent bracelet 0 Fin.val
    decide
  · intro x
    have other : ∀ x : Fin 15, x+1≠x := by decide
    let root : Nonsinks x := ⟨x+1,other x⟩
    let height (v : Fin 15) := (v.val+29-x.val)%15
    apply connected_by_descent _ root (fun v => height v.val)
    have step : ∀ x v : Fin 15, v≠x → v≠x+1 → ∃ u, u≠x ∧ bracelet.Adj v u ∧
        (u.val+29-x.val)%15 < (v.val+29-x.val)%15 := by decide
    intro v hv
    obtain ⟨u,hu,adj,lt⟩ := step x v.val v.property (fun e => hv (Subtype.ext e))
    exact ⟨⟨u,hu⟩,adj,lt⟩

private def terminal : Fin 3 → Fin 5 → ℤ := ![![0,8,8,8,13],![25,28,28,28,28],![25,23,23,23,18]]
private def interior : Fin 3 → Fin 5 → ℤ := ![![12,0,9,9,12],![27,31,31,31,32],![32,31,31,31,27]]

/-- Rotate the sink's block to zero. Reflect a right terminal to the left,
or interchange two interior vertices to send an interior sink to position one. -/
private def potential (s v : Fin 15) : ℤ :=
  let block := (v.val/5+3-s.val/5)%3
  let i := v.val%5
  let j := s.val%5
  if j=0 then terminal (Fin.ofNat 3 block) (Fin.ofNat 5 i)
  else if j=4 then terminal (Fin.ofNat 3 (3-block)) (Fin.ofNat 5 (4-i))
  else
    let slot := if block=0 ∧ i=j then 1 else if block=0 ∧ i=1 then j else i
    interior (Fin.ofNat 3 block) (Fin.ofNat 5 slot)

private theorem recurrent_maximal (s : Fin 15) : Recurrent bracelet s (maximal bracelet s) := by
  refine ⟨fun v => by simp [maximal,degree_four],?_⟩
  intro d hd
  refine ⟨fun v => maximal bracelet s v - d v,?_⟩
  have equal : (d + fun v => maximal bracelet s v - d v) = maximal bracelet s := by
    funext v
    have h := hd v
    change d v+(bracelet.degree v.val-1-d v)=bracelet.degree v.val-1
    omega
  rw [equal]

private theorem to_zero : ∀ (s : Fin 15) (v : Nonsinks s),
    ((bracelet.lapMatrix ℤ).submatrix Subtype.val Subtype.val *ᵥ (fun w : Nonsinks s => potential s w.val)) v
      = (maximal bracelet s v:ℤ) := by decide

theorem not_conjecture : ¬ Conjecture := by
  intro claim
  have identity : CompleteMaximalIdentity bracelet := fun s =>
    ⟨recurrent_maximal s, fun w => potential s w.val, funext (to_zero s)⟩
  have result : Nonempty (bracelet ≃g cycleGraph 15) ∨ bracelet = ⊤ :=
    claim 15 bracelet (by decide) biconnected identity
  rcases result with h | h
  · obtain ⟨f⟩ := h
    have d := f.degree_eq 0
    rw [degree_four] at d
    have c : (cycleGraph 15).degree (f 0) = 2 := cycleGraph_degree_three_le (n:=12)
    exact (by decide : (2 : ℕ) ≠ 4) (c.symm.trans d)
  · have missing : ¬ bracelet.Adj 0 4 := by decide
    exact missing (h ▸ (show (⊤ : SimpleGraph (Fin 15)).Adj 0 4 by decide))

/-- info: 'GaoLiSandpile.not_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_conjecture

end GaoLiSandpile
