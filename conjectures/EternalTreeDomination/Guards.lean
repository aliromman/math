module

public import conjectures.EternalTreeDomination.Statement
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
namespace EternalTreeDomination
open SimpleGraph

variable {V I : Type*} {G : SimpleGraph V} {k r : ℕ}

theorem defends_relabel {I J : Type*} (e : I ≃ J) {p : J→V} {a : List V} :
    Defends G k p a → Defends G k (p∘e) a := by
  induction a generalizing p with
  | nil => exact id
  | cons x xs ih =>
    rintro ⟨q,moves,⟨j,atx⟩,rest⟩
    exact ⟨q∘e,fun i ↦ moves (e i),⟨e.symm j,by simpa using atx⟩,ih rest⟩

theorem eternal_ge_dom (h : eternalCount G k r) : domCount G k r := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p, fun a ↦ ?_⟩
  obtain ⟨q,moves,⟨i,hi⟩,_⟩ := hp [a]
  exact ⟨i,hi ▸ moves i⟩

theorem domCount_of [Fintype I] (p : I→V) (h : Dominates G k p) :
    domCount G k (Fintype.card I) := by
  let e := Fintype.equivFin I
  refine ⟨p∘e.symm,?_⟩
  intro v
  obtain ⟨i,hi⟩ := h v
  exact ⟨e i,by simpa using hi⟩

theorem eternalCount_of [Fintype I] (p : I→V) (h : ∀ w,Defends G k p w) :
    eternalCount G k (Fintype.card I) :=
  ⟨p∘(Fintype.equivFin I).symm,fun w ↦ defends_relabel _ (h w)⟩

theorem min_eq {P : ℕ→Prop} {d : ℕ} (hd : P d) (low : ∀ i,P i→d ≤ i) :
    sInf {i|P i}=d := by
  exact le_antisymm (Nat.sInf_le hd) (low _ (Nat.sInf_mem ⟨d,hd⟩))

/-- A function that grows by at most one on an edge grows by at most k in k moves. -/
theorem grow_along_walk {V : Type*} {G : SimpleGraph V} (f : V→ℕ)
    (edge : ∀ {x y}, G.Adj x y → f y≤f x+1) {x y : V} {k : ℕ} (h : G.edist x y≤k) :
    f y≤f x+k := by
  have reach := reachable_of_edist_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top k) h)
  obtain ⟨w,he⟩ := reach.exists_walk_length_eq_edist
  have len : w.length≤k := by exact_mod_cast he.trans_le h
  have bound {a b : V} (w : G.Walk a b) : f b≤f a+w.length := by
    induction w with
    | nil => simp
    | cons adj w ih => have := edge adj; simp only [Walk.length_cons]; omega
  exact (bound w).trans (Nat.add_le_add_left len _)

/-- A cover by diameter-k blocks supplies an online response to every attack. -/
theorem block_defense {S : Type*} [DecidableEq I] (k : ℕ) (T : SimpleGraph (I×S))
    (diam : ∀ (i : I) (s t : S), T.edist (i,s) (i,t)≤k) (a : I→S) (attacks : List (I×S)) :
    Defends T k (fun i ↦ (i,a i)) attacks := by
  induction attacks generalizing a with
  | nil => trivial
  | cons v vs ih =>
    let b := Function.update a v.1 v.2
    refine ⟨fun i ↦ (i,b i),fun i ↦ diam _ _ _,⟨v.1,?_⟩,ih b⟩
    simp [b]

end EternalTreeDomination
