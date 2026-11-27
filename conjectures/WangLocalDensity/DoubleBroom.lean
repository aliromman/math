module

public import conjectures.WangLocalDensity.Masks
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace WangLocalDensity
open Finset SimpleGraph
open scoped BigOperators
namespace DoubleBroom

abbrev V := Fin 17
abbrev Mask := BitVec 17

/-- The spine has vertices 0 to 10. Three leaves attach to each end. -/
def parent (j : V) : V :=
  if j.val ≤ 10 then ⟨j.val-1,by have := j.isLt; omega⟩ else if j.val < 14 then 0 else 10

def graph : SimpleGraph V where
  Adj i j := (i.val < j.val ∧ parent j=i) ∨ (j.val < i.val ∧ parent i=j)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by simp⟩

instance : DecidableRel graph.Adj := fun i j ↦
  inferInstanceAs (Decidable ((i.val < j.val ∧ parent j=i) ∨ (j.val < i.val ∧ parent i=j)))

def vertices : List V := (List.finRange 17).tail

def attach (F : Finset Mask) (x : V) : Finset Mask :=
  insert (oneBit x) (F ∪ ((F.filter (fun a => a.getLsbD (parent x).val)).image (fun a => oneBit x ||| a)))

def masks : Finset Mask := vertices.foldl attach {oneBit 0}

def onMasks (p : Mask → Prop) : Prop := ∀ a∈masks,p a

instance (p : Mask → Prop) [DecidablePred p] : Decidable (onMasks p) :=
  @Finset.decidableDforallFinset _ masks (fun a _ => p a) (fun _ _ => inferInstance)

private theorem attach_sound {F : Finset Mask} {x : V} (hx : graph.Adj (parent x) x)
    (h : ∀ a∈F,(graph.induce (decode a : Set V)).Connected) :
    ∀ a∈attach F x,(graph.induce (decode a : Set V)).Connected := by
  intro a ha
  simp only [attach,mem_insert,mem_union,mem_image,mem_filter] at ha
  rcases ha with rfl | old | ⟨b,⟨hb,hp⟩,rfl⟩
  · rw [decode_one]
    exact singleton_connected x
  · exact h a old
  · rw [decode_or,decode_one,singleton_union]
    exact insert_connected (h b hb) (mem_decode.mpr hp) hx

private theorem masks_sound : ∀ a∈masks,(graph.induce (decode a : Set V)).Connected := by
  have valid : ∀ x∈vertices, graph.Adj (parent x) x := by decide +kernel
  have go (xs : List V) (hs : ∀ x∈xs,graph.Adj (parent x) x) (F : Finset Mask)
      (hF : ∀ a∈F,(graph.induce (decode a : Set V)).Connected) :
      ∀ a∈xs.foldl attach F,(graph.induce (decode a : Set V)).Connected := by
    induction xs generalizing F with
    | nil => exact hF
    | cons x xs ih =>
      exact ih (fun y hy => hs y (by simp [hy])) _ (attach_sound (hs x (by simp)) hF)
  apply go vertices valid
  intro a ha
  obtain rfl := mem_singleton.mp ha
  rw [decode_one]
  exact singleton_connected (0 : V)

set_option maxHeartbeats 2500000 in
theorem exhaustive : subtrees graph = masks.image decode := by
  apply eq_subtrees_of_closed
  · intro S h
    obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact masks_sound a ha
  · have test : ∀ x : V,oneBit x∈masks := by decide +kernel
    intro x
    exact mem_image.mpr ⟨oneBit x,test x,decode_one x⟩
  · have test : onMasks (fun a ↦ ∀ j : V, j.val ≠ 0 →
          ((a.getLsbD (parent j).val → ¬a.getLsbD j.val → oneBit j ||| a ∈ masks) ∧
           (a.getLsbD j.val → ¬a.getLsbD (parent j).val → oneBit (parent j) ||| a ∈ masks))) := by
      decide +kernel
    intro S hS x hx y hy
    by_cases already : y∈S
    · rwa [insert_eq_of_mem already]
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hS
    have yy := mt mem_decode.mpr already
    have inside : oneBit y ||| a ∈ masks := by
      rcases hy with ⟨lt,hp⟩ | ⟨lt,hp⟩
      · subst x
        exact (test a ha y (by omega)).1 (mem_decode.mp hx) yy
      · subst y
        exact (test a ha x (by omega)).2 (mem_decode.mp hx) yy
    exact mem_image.mpr ⟨oneBit y ||| a,inside,by simp⟩

theorem tree : graph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · have h : (65535+65536 : Mask) ∈ masks := by decide +kernel
    have e : decode (65535+65536 : Mask) = (univ : Finset V) := by decide +kernel
    have hc := masks_sound _ h
    rw [e,coe_univ] at hc
    exact (SimpleGraph.induceUnivIso graph).connected_iff.mp hc
  · have num := graph.two_mul_card_edgeFinset
    have cert : (univ.filter fun z : V × V => graph.Adj z.1 z.2).card = 32 := by decide +kernel
    rw [cert] at num
    rw [Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card,Nat.card_eq_fintype_card,Fintype.card_fin]
    omega

end DoubleBroom
end WangLocalDensity
