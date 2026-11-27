module

public import conjectures.EternalTreeDomination.Guards
import Mathlib.Data.Fintype.Prod

@[expose] public section
namespace EternalTreeDomination
open SimpleGraph Set
variable {I : Type*}

/-- The five positions of one block: attachment, near center, near leaf, far center, far leaf. -/
def localEdge : Fin 4 → Fin 5 × Fin 5
  | 0 => (0,1)
  | 1 => (1,2)
  | 2 => (1,3)
  | 3 => (3,4)

def localAdj (x y : Fin 5) : Prop :=
  ∃ e : Fin 4, localEdge e=(x,y) ∨ localEdge e=(y,x)

instance : DecidableRel localAdj := fun _ _ ↦ inferInstanceAs (Decidable (∃ _ : Fin 4, _))

def piece : SimpleGraph (Fin 5) where
  Adj := localAdj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

def tree (B : SimpleGraph I) : SimpleGraph (I×Fin 5) where
  Adj x y := (x.1=y.1 ∧ localAdj x.2 y.2) ∨ (x.2=0 ∧ y.2=0 ∧ B.Adj x.1 y.1)
  symm := by
    constructor
    rintro x y (⟨eq,a⟩|⟨x0,y0,a⟩)
    · exact Or.inl ⟨eq.symm,piece.symm.symm _ _ a⟩
    · exact Or.inr ⟨y0,x0,a.symm⟩
  loopless := ⟨fun x ↦ by
    rintro (⟨_,a⟩|⟨_,_,a⟩)
    · exact piece.loopless.irrefl _ a
    · exact B.loopless.irrefl _ a⟩

private def rootHom (B : SimpleGraph I) : B →g tree B :=
  ⟨fun i ↦ (i,0),fun h ↦ Or.inr ⟨rfl,rfl,h⟩⟩

/-- Each spot is within one edge of its chosen center. -/
def center (s : Fin 5) : Fin 5 := if s=3 ∨ s=4 then 3 else 1

theorem to_center (B : SimpleGraph I) (i : I) (s : Fin 5) :
    (tree B).edist (i,s) (i,center s)≤1 := by
  apply edist_le_one_iff_adj_or_eq.mpr
  have r : ∀ s : Fin 5, localAdj s (center s) ∨ s=center s := by decide
  rcases r s with h|h
  · exact Or.inl (Or.inl ⟨rfl,h⟩)
  · exact Or.inr (congrArg (Prod.mk i) h)

theorem diameter_three (B : SimpleGraph I) (i : I) (x y : Fin 5) :
    (tree B).edist (i,x) (i,y)≤3 := by
  have near : (tree B).edist (i,center x) (i,center y)≤1 := by
    apply edist_le_one_iff_adj_or_eq.mpr
    have pair : ∀ x y : Fin 5, localAdj (center x) (center y) ∨ center x=center y := by decide
    rcases pair x y with h|h
    · exact Or.inl (Or.inl ⟨rfl,h⟩)
    · exact Or.inr (congrArg (Prod.mk i) h)
  have a := to_center B i x
  have b := to_center B i y
  rw [edist_comm] at b
  exact ((tree B).edist_triangle (v:=(i,center x))).trans <| (add_le_add a
    (((tree B).edist_triangle (v:=(i,center y))).trans (add_le_add near b))).trans (by decide)

private theorem treeConnected {B : SimpleGraph I} (h : B.Connected) : (tree B).Connected := by
  let ⟨i⟩ := h.nonempty
  have : Nonempty (I×Fin 5) := ⟨(i,0)⟩
  have within (i : I) (x y : Fin 5) : (tree B).Reachable (i,x) (i,y) :=
    reachable_of_edist_ne_top (ne_top_of_le_ne_top (by decide : (3:ℕ∞)≠⊤) (diameter_three B i x y))
  constructor
  rintro ⟨i,x⟩ ⟨j,y⟩
  exact (within i x 0).trans (((h i j).map (rootHom B)).trans (within j 0 y))

theorem tree_isTree [Finite I] {B : SimpleGraph I} (h : B.IsTree) : (tree B).IsTree := by
  classical
  let root := fun i : I ↦ (i,(0:Fin 5))
  let edge := fun (e : I×Fin 4) ↦ s((e.1,(localEdge e.2).1),(e.1,(localEdge e.2).2))
  have sub : (tree B).edgeSet⊆(Sym2.map root '' B.edgeSet)∪Set.range edge := by
    intro e
    induction e using Sym2.inductionOn with
    | hf p q =>
      rcases p with ⟨i,x⟩
      rcases q with ⟨j,y⟩
      change ((i=j ∧ localAdj x y) ∨ (x=0 ∧ y=0 ∧ B.Adj i j)) → _
      rintro (⟨rfl,⟨a,v|v⟩⟩|⟨rfl,rfl,adj⟩)
      · apply Or.inr
        refine ⟨(i,a),?_⟩
        simp [edge,v]
      · apply Or.inr
        refine ⟨(i,a),?_⟩
        simp [edge,v,Sym2.eq_swap]
      · exact Or.inl ⟨s(i,j),adj,rfl⟩
  have ed := (Set.ncard_le_ncard sub).trans (Set.ncard_union_le _ _)
  have trunk := Set.ncard_image_le (s:=B.edgeSet) (f:=Sym2.map root)
  have sides : (Set.range edge).ncard≤Nat.card I*4 := by
    rw [←Set.image_univ]
    simpa using (Set.ncard_image_le (s:=(Set.univ : Set (I×Fin 4))) (f:=edge))
  have conn := treeConnected h.connected
  apply isTree_iff_connected_and_card.mpr ⟨conn,le_antisymm ?_ conn.card_vert_le_card_edgeSet_add_one⟩
  have base := h.ncard_edgeSet_add_one
  simp only [Nat.card_prod,Nat.card_fin]
  rw [Nat.card_coe_set_eq]
  omega

end EternalTreeDomination
