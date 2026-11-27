module

public import conjectures.AscoliDihedralDominance.Orbits
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

open Equiv Finset SimpleGraph
namespace AscoliDihedral

variable {X : Type*} [Fintype X]

/-- A regular graph of degree two has at most seven independent colorings per
four vertices. This includes disconnected graphs. -/
theorem independent_fourth_bound (G : SimpleGraph X)
    (hdeg : ∀ x, (G.neighborSet x).ncard = 2) :
    (Nat.card {f : X → Bool // ∀ x y, G.Adj x y → (!(f x && f y)) = true})^4 ≤
      7^(Fintype.card X) := by
  classical
  let C := G.ConnectedComponent
  let _ : Fintype C := Fintype.ofFinite _
  let v (c : C) := c.nonempty_supp.choose
  have hv (c : C) : v c ∈ c.supp := c.nonempty_supp.choose_spec
  have edge (x : X) : (G.neighborSet x).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hdeg]; decide
  have cyc : G.IsCycles := fun _ _ => hdeg _
  choose p hp hs using fun c : C =>
    cyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (hv c) (edge (v c))
  have point (c : C) (i : Fin (p c).length) : (p c).getVert i ∈ c.supp := by
    rw [← hs c, Walk.mem_verts_toSubgraph]
    exact (p c).getVert_mem_support _
  let e (c : C) : Fin (p c).length ≃ c :=
    Equiv.ofBijective (fun i => ⟨(p c).getVert i,point c i⟩) (by
      constructor
      · intro i j h
        apply Fin.ext
        exact (hp c).getVert_injOn' (by change i.val ≤ _; omega)
          (by change j.val ≤ _; omega) (congrArg Subtype.val h)
      · intro y
        have hy : y.val ∈ c.supp := y.property
        rw [← hs c, Walk.mem_verts_toSubgraph, Walk.mem_support_iff_exists_getVert] at hy
        obtain ⟨i,hy,hi⟩ := hy
        by_cases h : i < (p c).length
        · exact ⟨⟨i,h⟩,Subtype.ext hy⟩
        · have hl := (hp c).three_le_length
          have eh : i = (p c).length := by omega
          exact ⟨⟨0,by omega⟩,Subtype.ext (by simpa [eh] using hy)⟩)
  have total : ∑ c : C, (p c).length = Fintype.card X := by
    have he : (Σ c : C, Fin (p c).length) ≃ X :=
      (Equiv.sigmaCongrRight e).trans G.verticesEquivSigmaConnectedComponent.symm
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr he
  have adj (c : C) (i : Fin (p c).length) :
      G.Adj (p c |>.getVert i) (p c |>.getVert (next i)) := by
    have h := (p c).adj_getVert_succ i.isLt
    by_cases hi : i.val+1 < (p c).length
    · simpa [next, Nat.mod_eq_of_lt hi] using h
    · have eq : i.val+1 = (p c).length := by omega
      simpa [next,eq] using h
  let send (f : {f : X → Bool // ∀ x y, G.Adj x y → (!(f x && f y)) = true})
      (c : C) : {h : Fin (p c).length → Bool // coloringOK next h} :=
    ⟨fun i => f.val ((e c i).val),fun i => f.property _ _ (adj c i)⟩
  have inj : Function.Injective send := by
    intro f g h
    apply Subtype.ext
    funext x
    let c := G.connectedComponentMk x
    obtain ⟨i,hi⟩ := (e c).surjective (⟨x,rfl⟩ : c)
    have he : (e c i).val = x := congrArg Subtype.val hi
    have hi' : f.val (e c i).val = g.val (e c i).val := congrFun (congrArg Subtype.val (congrFun h c)) i
    simpa only [he] using hi'
  have bound := Nat.card_le_card_of_injective send inj
  have hcard : Nat.card ((c : C) → {h : Fin (p c).length → Bool // coloringOK next h}) =
      ∏ c : C, lucas (p c).length := by
    rw [Nat.card_pi]
    apply prod_congr rfl
    intro c _
    exact card_coloring_next _ (by have := (hp c).three_le_length; omega)
  rw [hcard] at bound
  refine (Nat.pow_le_pow_left bound 4).trans ?_
  rw [← Finset.prod_pow, ←total, ←prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun c _ => lucas_fourth_le _ (hp c).three_le_length)

end AscoliDihedral
