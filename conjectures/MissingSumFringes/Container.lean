module

public import conjectures.MissingSumFringes.Window
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

@[expose] public section
namespace MissingSumFringes
open Finset
open scoped Classical Pointwise

/-- Neighbours of x for the equations x+y∈S on the interval [0,s). -/
def nbr (s : ℕ) (S : Finset ℕ) (x : ℕ) := (range s).filter (fun y => x+y∈S)

def covered (s : ℕ) (S F : Finset ℕ) := F.biUnion (nbr s S)

def box (s h : ℕ) (S F : Finset ℕ) :=
  ((range s) \ covered s S F).filter fun x => (nbr s S x \ covered s S F).card≤h

private theorem covered_sub (s : ℕ) (S F : Finset ℕ) : covered s S F⊆range s := by
  intro v hv
  obtain ⟨x,_,hx⟩ := mem_biUnion.mp hv
  exact (mem_filter.mp hx).1

theorem box_sub (s h : ℕ) (S F : Finset ℕ) : box s h S F⊆range s :=
  (filter_subset ..).trans sdiff_subset

/-- A bounded fingerprint determines a set containing all possible occupied positions. -/
theorem fingerprint {s h : ℕ} {S A : Finset ℕ} (small : A⊆range s)
    (avoids : ∀ x∈A, ∀ y∈A, x+y∉S) :
    ∃ F⊆A, F.card*h≤s ∧ A⊆box s h S F := by
  let score (F : Finset ℕ) : ℤ := ((covered s S F).card : ℤ)-(F.card:ℤ)*h
  obtain ⟨F,hF,peak⟩ := A.powerset.exists_max_image score ⟨∅,by simp⟩
  have sub := mem_powerset.mp hF
  have zero := peak ∅ (by simp)
  have nonneg : (F.card:ℤ)*h≤(covered s S F).card := by simpa [score,covered] using zero
  have cost : F.card*h≤(covered s S F).card := by exact_mod_cast nonneg
  refine ⟨F,sub,cost.trans (by simpa using card_mono (covered_sub s S F)),?_⟩
  intro x hx
  have clear : x∉covered s S F := by
    intro bad
    obtain ⟨y,hy,e⟩ := mem_biUnion.mp bad
    exact avoids y (sub hy) x hx (mem_filter.mp e).2
  apply mem_filter.mpr ⟨mem_sdiff.mpr ⟨small hx,clear⟩,?_⟩
  by_cases old : x∈F
  · have included : nbr s S x ⊆ covered s S F := fun _ hy => mem_biUnion.mpr ⟨x,old,hy⟩
    simp [sdiff_eq_empty_iff_subset.mpr included]
  have best := peak (insert x F) (mem_powerset.mpr (insert_subset hx sub))
  have count := card_sdiff_add_card (nbr s S x) (covered s S F)
  simp only [score,covered,biUnion_insert,card_insert_of_notMem old,Nat.cast_add,Nat.cast_one] at best
  unfold covered at count ⊢
  have arithmetic : (F.biUnion (nbr s S) ∪ nbr s S x).card ≤ (F.biUnion (nbr s S)).card+h := by
    rw [union_comm]
    exact_mod_cast (show (((nbr s S x ∪ F.biUnion (nbr s S)).card : ℕ):ℤ)≤(F.biUnion (nbr s S)).card+h by linarith)
  rw [union_comm] at arithmetic
  omega

private theorem degree_upper (S T : Finset ℕ) (x : ℕ) :
    (T.filter fun y => x+y∈S).card≤S.card :=
  card_le_card_of_injOn (fun y => x+y) (fun _ hy => (mem_filter.mp hy).2)
    (fun _ _ _ _ eq => Nat.add_left_cancel eq)

private theorem degree_lower {s w x : ℕ} {S : Finset ℕ} (band : S⊆Ico (s-w) s) (hx : x<s-w) :
    S.card≤(nbr s S x).card := by
  apply card_le_card_of_injOn (fun z => z-x)
  · intro z hz
    have ⟨lo,hi⟩ := mem_Ico.mp (band hz)
    change z-x∈nbr s S x
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), by simpa [show x+(z-x)=z by omega] using hz⟩
  · intro z hz v hv eq
    have lz := (mem_Ico.mp (band hz)).1
    have lv := (mem_Ico.mp (band hv)).1
    change z-x=v-x at eq
    omega

/-- Near-regularity of the reflection graph bounds the number of free coordinates. -/
theorem box_size {s w h : ℕ} {S : Finset ℕ} (band : S⊆Ico (s-w) s) (F : Finset ℕ) :
    2*(box s h S F).card*S.card ≤ (s+w)*S.card+s*h := by
  let C := box s h S F
  let B := covered s S F
  let G := C ∩ range (s-w)
  let r := fun (x y : ℕ) => x+y∈S
  have csub : C⊆range s := box_sub ..
  have cb : C.card+B.card≤s := by
    have bound := card_mono (show C⊆range s \ B from filter_subset ..)
    have split := card_sdiff_add_card_eq_card (covered_sub s S F)
    change (range s \ B).card+B.card=(range s).card at split
    simp only [card_range] at split
    omega
  have gsub : G⊆C := inter_subset_left
  have gs : G.card≤s := by simpa using card_mono (gsub.trans csub)
  have lost : C.card≤G.card+w := by
    have outside : C \ range (s-w)⊆range s \ range (s-w) := sdiff_subset_sdiff_left _ csub
    have count := card_mono outside
    rw [card_sdiff_of_subset (range_mono (Nat.sub_le s w)),card_range,card_range] at count
    have split := card_sdiff_add_card_inter C (range (s-w))
    change (C \ range (s-w)).card+G.card=C.card at split
    omega
  have edge := Finset.card_mul_le_card_mul (s:=G) (t:=B) r (m:=S.card-h) (n:=S.card) (by
    intro x hx
    have hxC := gsub hx
    have full := degree_lower band (mem_range.mp (mem_inter.mp hx).2)
    have gap := (mem_filter.mp hxC).2
    change (nbr s S x \ B).card≤h at gap
    have split := card_sdiff_add_card_inter (nbr s S x) B
    have incl : nbr s S x ∩ B ⊆ B.bipartiteAbove r x := by
      intro z hz
      exact (mem_bipartiteAbove r).mpr ⟨(mem_inter.mp hz).2,(mem_filter.mp (mem_inter.mp hz).1).2⟩
    have larger := card_mono incl
    omega) (by
    intro y _
    simpa [bipartiteBelow,r,Nat.add_comm] using degree_upper S G y)
  have dg := Nat.mul_le_mul_left G.card (show S.card≤S.card-h+h by omega)
  have hg := Nat.mul_le_mul_right h gs
  have lose := Nat.mul_le_mul_right S.card lost
  have cbprod := Nat.mul_le_mul_right S.card cb
  nlinarith only [edge,dg,hg,lose,cbprod]

end MissingSumFringes
