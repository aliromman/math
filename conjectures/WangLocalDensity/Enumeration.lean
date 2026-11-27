module

public import conjectures.WangLocalDensity.Statement
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Lattice

@[expose] public section
namespace WangLocalDensity
open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
theorem singleton_connected (x : V) : (G.induce (({x} : Finset V) : Set V)).Connected := by
  rw [Finset.coe_singleton]
  exact ⟨.of_subsingleton⟩

omit [Fintype V] in
theorem insert_connected {A : Finset V} (hA : (G.induce (A : Set V)).Connected)
    {x p : V} (hp : p∈A) (hpx : G.Adj p x) : (G.induce (↑(insert x A) : Set V)).Connected := by
  have H := SimpleGraph.connected_induce_union hA.preconnected
    (singleton_connected (G:=G) x).preconnected hp (show x∈({x} : Finset V) by simp) hpx
  have eq : (↑(insert x A) : Set V) = (A : Set V) ∪ ↑({x} : Finset V) := by
    ext z
    simp
  rw [eq]
  exact H

/-- A family of connected sets is exhaustive if it contains the singletons and is closed
under adding a neighbour of a member. -/
theorem eq_subtrees_of_closed (F : Finset (Finset V))
    (sound : ∀ S∈F,(G.induce (S : Set V)).Connected)
    (single : ∀ v, {v}∈F)
    (closed : ∀ A∈F, ∀ x∈A, ∀ y, G.Adj x y → insert y A ∈ F) : subtrees G = F := by
  classical
  ext S
  simp only [subtrees, mem_filter, mem_powerset, subset_univ, true_and]
  constructor
  · intro hS
    obtain ⟨v,hv⟩ := hS.nonempty
    let K := F.filter (fun A => A⊆S)
    have hit : {v}∈K := mem_filter.mpr ⟨single _,singleton_subset_iff.mpr hv⟩
    obtain ⟨B,hB,big⟩ := K.exists_max_image Finset.card ⟨_,hit⟩
    have Bin := (mem_filter.mp hB).2
    have bf := (mem_filter.mp hB).1
    have bn : B.Nonempty := Finset.card_pos.mp ((by simp : 0<({v}:Finset V).card).trans_le (big {v} hit))
    obtain ⟨b,hb⟩ := bn
    have hs : S ⊆ B := by
      intro w hw
      have path := hS.preconnected ⟨b,Bin hb⟩ ⟨w,hw⟩
      have reach := (SimpleGraph.reachable_iff_reflTransGen ..).mp path
      have keep (y : S) (h : Relation.ReflTransGen (G.induce (S:Set V)).Adj ⟨b,Bin hb⟩ y) : y.val∈B := by
        induction h with
        | refl => exact hb
        | @tail x y _ step ih =>
          by_contra outside
          have atK : insert y.val B∈K := mem_filter.mpr
            ⟨closed B bf x.val ih y.val step,insert_subset y.property Bin⟩
          have imp := big _ atK
          simp [card_insert_of_notMem outside] at imp
      exact keep _ reach
    simpa only [Subset.antisymm Bin hs] using bf
  · exact sound S

end WangLocalDensity
