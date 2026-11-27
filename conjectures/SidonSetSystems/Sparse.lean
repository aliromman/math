module

public import conjectures.SidonSetSystems.Normalized
import Mathlib.Data.Fin.VecNotation

public section
namespace SidonSetSystems
open Finset
open scoped Classical

private abbrev Key (d : ℕ) := Pattern d × Fin 4 × Fin 4

private def Link {d : ℕ} (key : Key d) (a b : Fin d→ℕ) : Prop :=
  Function.Injective (key.1.row key.2.1) ∧ ∃ x : key.1.solutions,
    key.1.row key.2.1 x=(fun i => (a i:ℚ)) ∧ key.1.row key.2.2 x=(fun i => (b i:ℚ))

private theorem Link.unique {d : ℕ} {key : Key d} {a b c : Fin d→ℕ} (hb : Link key a b)
    (hc : Link key a c) : b=c := by
  obtain ⟨inj,x,hx,bx⟩ := hb
  obtain ⟨_,y,hy,cy⟩ := hc
  have e := inj (hx.trans hy.symm)
  subst y
  funext i
  exact_mod_cast congrFun (bx.symm.trans cy) i

private theorem link_of_neighbor {d n : ℕ} {a b : Finset ℕ} (hb : b∈neighbors (good d n) a) :
    ∃ key : Key d, Link key (listing d a) (listing d b) := by
  classical
  obtain ⟨_,_,A,ha,B,hb,C,hc,D,hd,bad,as,bs⟩ := mem_filter.mp hb
  let F : Fin 4→Finset ℕ := ![A,B,C,D]
  have goodF (i : Fin 4) : F i∈good d n := by fin_cases i <;> assumption
  let v (i : Fin 4) := listing d (F i)
  have restore (i : Fin 4) : shape (v i)=F i := (normalized_spec (mem_filter.mp (goodF i)).1).1
  have badV : Bad (shape (v 0)) (shape (v 1)) (shape (v 2)) (shape (v 3)) := by
    simpa only [restore] using (show Bad (F 0) (F 1) (F 2) (F 3) from bad)
  obtain ⟨p,mem⟩ := realize_pattern v badV.1
  let x : p.solutions := ⟨rationalRows v,mem⟩
  have sur (i : Fin 4) : Function.Surjective (p.row i) :=
    (mem_filter.mp (goodF i)).2 p i ⟨x,rfl⟩
  have locate {z : Finset ℕ} (here : z∈({A,B,C,D}:Finset (Finset ℕ))) : ∃ i, F i=z := by
    simp only [mem_insert,mem_singleton] at here
    rcases here with rfl|rfl|rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  obtain ⟨i,ei⟩ := locate as
  obtain ⟨j,ej⟩ := locate bs
  refine ⟨(p,i,j),p.row_controls v mem sur badV i,x,?_,?_⟩
  · change (fun j => (listing d (F i) j : ℚ))=_
    rw [ei]
  · change (fun t => (listing d (F j) t : ℚ))=_
    rw [ej]

/-- A good shape can collide with only boundedly many other shapes, uniformly in n. -/
private theorem good_degree (d n : ℕ) (a : Finset ℕ) : (neighbors (good d n) a).card ≤ Fintype.card (Key d) := by
  classical
  let N := neighbors (good d n) a
  choose code spec using fun b : N => link_of_neighbor b.2
  have inj : Function.Injective code := by
    intro b c e
    apply Subtype.ext
    have cb := spec b
    rw [e] at cb
    have lists := Link.unique cb (spec c)
    have gb : b.val∈good d n := (mem_filter.mp b.2).1
    have gc : c.val∈good d n := (mem_filter.mp c.2).1
    have rb := (normalized_spec (mem_filter.mp gb).1).1
    have rc := (normalized_spec (mem_filter.mp gc).1).1
    exact rb.symm.trans ((congrArg shape lists).trans rc)
  simpa [N] using Fintype.card_le_of_injective code inj

theorem sparse_shapes (k : ℕ) (hk : 3≤k) : SparseShapes k := by
  obtain ⟨m,rfl⟩ : ∃ m, k=m+2 := ⟨k-2,by omega⟩
  let D := Fintype.card (Key (m+1))+Fintype.card (Pattern (m+1) × Fin 4)
  refine ⟨D,fun n => ⟨good (m+1) n,filter_subset ..,?_,fun a _ => (good_degree ..).trans (Nat.le_add_right ..)⟩⟩
  have poly : n^m≤(n+1)^m := Nat.pow_le_pow_left (by omega) _
  have des : Fintype.card (Pattern (m+1) × Fin 4)≤D := Nat.le_add_left ..
  simpa only [Nat.add_sub_cancel] using (count_good m n).trans (Nat.add_le_add_left (Nat.mul_le_mul des poly) _)

end SidonSetSystems
