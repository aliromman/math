module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace SplitMatroidFlags

open Finset

abbrev G := Fin 11

/-- Record the elements of a set as bits of a natural number. -/
def mask (S : Finset G) : ℕ := S.fold (· ||| ·) 0 (fun i => 2^i.val)

lemma mask_bit (S : Finset G) (n : ℕ) : (mask S).testBit n = true ↔ ∃ i ∈ S, i.val = n := by
  induction S using Finset.induction_on with
  | empty => simp [mask]
  | insert i S hs ih =>
    simp only [mask,Finset.fold_insert hs,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow]
    change (decide (i.val = n) = true ∨ (mask S).testBit n = true) ↔ _
    rw [ih]
    simp [eq_comm]

@[simp] lemma mem_mask (S : Finset G) (i : G) : (mask S).testBit i.val = true ↔ i ∈ S := by
  rw [mask_bit]
  exact ⟨fun ⟨j,h,e⟩ => (Fin.ext e) ▸ h,fun h => ⟨_,h,rfl⟩⟩

lemma mask_inj : Function.Injective mask := by
  intro S T h
  ext i
  rw [← mem_mask,← mem_mask,h]

lemma mask_and (S T : Finset G) : mask (S ∩ T) = mask S &&& mask T := by
  apply Nat.eq_of_testBit_eq
  intro n
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_and,Bool.and_eq_true,mask_bit,mask_bit,mask_bit]
  constructor
  · rintro ⟨i,h,rfl⟩
    exact ⟨⟨i,(mem_inter.mp h).1,rfl⟩,i,(mem_inter.mp h).2,rfl⟩
  · rintro ⟨⟨i,hi,rfl⟩,j,hj,e⟩
    replace e : j = i := Fin.ext e
    exact ⟨i,mem_inter.mpr ⟨hi,e ▸ hj⟩,rfl⟩

lemma mask_or (S T : Finset G) : mask (S ∪ T) = mask S ||| mask T := by
  apply Nat.eq_of_testBit_eq
  intro n
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_or,Bool.or_eq_true,mask_bit,mask_bit,mask_bit]
  simp only [mem_union,or_and_right,exists_or]

lemma mask_zero {S : Finset G} : mask S = 0 ↔ S = ∅ := by
  change mask S = mask ∅ ↔ _
  exact mask_inj.eq_iff


def exceptMask (S T : ℕ) := S ^^^ (S &&& T)

lemma mask_diff (S T : Finset G) : mask (S \ T) = exceptMask (mask S) (mask T) := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases nn : n < 11
  · let i : G := ⟨n,nn⟩
    change (mask (S \ T)).testBit i.val = (exceptMask (mask S) (mask T)).testBit i.val
    have bit (V : Finset G) : (mask V).testBit i.val = decide (i ∈ V) :=
      Bool.eq_iff_iff.mpr (by simp)
    simp only [exceptMask,Nat.testBit_xor,Nat.testBit_and,bit]
    by_cases si : i ∈ S <;> by_cases ti : i ∈ T <;> simp [si,ti]
  · have hz (U : Finset G) : (mask U).testBit n = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨i,_,rfl⟩ := (mask_bit _ _).mp h
      exact nn i.isLt
    simp [exceptMask,hz]

structure Three (α : Type) where
  x : α
  y : α
  z : α
deriving DecidableEq, Repr, Inhabited

namespace Three

def map {α β} (f : α → β) (a : Three α) : Three β := ⟨f a.x,f a.y,f a.z⟩

def coords {α} [DecidableEq α] (a : Three α) : Finset α := {a.x,a.y,a.z}

def disjointCoords {α} (a : Three α) : Prop := a.x ≠ a.y ∧ a.x ≠ a.z ∧ a.y ≠ a.z

instance {α : Type} [DecidableEq α] (a : Three α) : Decidable a.disjointCoords :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def edges (a : Three G) (R : Three (Finset G)) : Finset (G × G) :=
  R.x.image (a.x,·) ∪ R.y.image (a.y,·) ∪ R.z.image (a.z,·)

lemma mem_edges {a : Three G} {R : Three (Finset G)} (i j : G) :
    (i,j) ∈ edges a R ↔ (a.x = i ∧ j ∈ R.x) ∨ (a.y = i ∧ j ∈ R.y) ∨ (a.z = i ∧ j ∈ R.z) := by
  simp [edges,and_comm]

def masks (R : Three (Finset G)) := R.map mask

def restrict (R : Three ℕ) (T : ℕ) := R.map (· &&& T)

def restrictSets (R : Three (Finset G)) (T : Finset G) := R.map (· ∩ T)

lemma masks_restrict (R : Three (Finset G)) (T : Finset G) :
    (R.restrictSets T).masks = R.masks.restrict (mask T) := by simp [restrictSets,restrict,masks,map,mask_and]

def unionCols (R : Three (Finset G)) := R.x ∪ R.y ∪ R.z

end Three

end SplitMatroidFlags
