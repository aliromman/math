module

public import conjectures.SplitMatroidFlags.Enumeration
import Mathlib.Tactic

@[expose] public section

namespace SplitMatroidFlags

open Finset

/-- Cell zero counts vertex–4-face incidences. Cell d+1 counts d-dimensional faces. -/
def pushTag (a : Array ℕ) (t : ℕ × Bool) :=
  let b := if t.1 = 4 then a.modify 0 (· + 1) else a
  if t.2 then b.modify (t.1 + 1) (· + 1) else b

def bin (i : ℕ) (t : ℕ × Bool) :=
  if i = 0 then accepts false 4 t else accepts true (i-1) t

@[simp] private lemma size_pushTag (a : Array ℕ) (t : ℕ × Bool) : (pushTag a t).size = a.size := by
  simp only [pushTag]
  split <;> split <;> simp

private lemma value_pushTag (a : Array ℕ) (t : ℕ × Bool) (i : ℕ) (h : i < a.size) :
    (pushTag a t)[i]'(by simpa using h) = a[i] + (bin i t).toNat := by
  obtain ⟨d,b⟩ := t
  cases i with
  | zero =>
    cases b <;> by_cases eq : d = 4 <;> simp [pushTag,bin,eq,accepts,Array.getElem_modify]
  | succ j =>
    cases b <;> by_cases eq : d = 4 <;> by_cases hj : d = j <;>
      simp_all [pushTag,bin,accepts,Array.getElem_modify]
    have hn : j ≠ 4 := Ne.symm hj
    simp [hn,hj]

def tally (tags : List (ℕ × Bool)) (a : Array ℕ) := tags.foldl pushTag a

@[simp] lemma tally_size (l : List (ℕ × Bool)) (a : Array ℕ) : (tally l a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons q l ih => exact (ih _).trans (size_pushTag a q)

lemma tally_value (l : List (ℕ × Bool)) (a : Array ℕ) (i : ℕ) (hi : i < a.size) :
    (tally l a)[i]'(by simpa using hi) = a[i] + l.countP (bin i) := by
  induction l generalizing a with
  | nil => simp [tally]
  | cons t l ih =>
    change (tally l (pushTag a t))[i]'(by simpa using hi) = _
    rw [ih _ (by simpa using hi),value_pushTag _ _ _ hi]
    cases e : bin i t <;> simp [e]; omega

abbrev BasisData := Three G × Three ℕ

def basisData (H : Lines) : List BasisData := (chartList H).map fun a => (a,(rows H a).masks)

def basisTags (b : BasisData) := tags (rowList b.2) (lowRows b.1) (outside b.1)

def accumulate (D : List BasisData) (a : Array ℕ) := D.foldl (fun v b => tally (basisTags b) v) a

@[simp] lemma accumulate_size (D : List BasisData) (a : Array ℕ) : (accumulate D a).size = a.size := by
  induction D generalizing a with
  | nil => rfl
  | cons b D ih => exact (ih _).trans (tally_size _ _)

lemma accumulate_value (D : List BasisData) (a : Array ℕ) (i : ℕ) (hi : i < a.size) :
    (accumulate D a)[i]'(by simpa using hi) = a[i] + (D.map fun b => (basisTags b).countP (bin i)).sum := by
  induction D generalizing a with
  | nil => simp [accumulate]
  | cons b D ih =>
    change (accumulate D (tally (basisTags b) a))[i]'(by simpa using hi) = _
    rw [ih _ (by simpa using hi),tally_value _ _ _ hi]
    simp [Nat.add_assoc]

def census (D : List BasisData) := accumulate D (Array.replicate 12 0)

lemma census_value (H : Lines) (i : Fin 12) :
    (census (basisData H))[i.val]'(by simp [census]) =
      if i = 0 then table H false 4 else table H true (i.val - 1) := by
  refine (accumulate_value (basisData H) (Array.replicate 12 0) i.val (by simp)).trans ?_
  simp only [Array.getElem_replicate,zero_add,basisData,List.map_map]
  by_cases hz : i = 0
  · subst i
    simp only [ite_true]
    unfold table
    rw [← chartList_set H,List.sum_toFinset _ (chartList_nodup _)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    exact tags_count H a false 4
  · rw [ite_eq_right hz]
    have pos : i.val ≠ 0 := fun e => hz (Fin.ext e)
    unfold table
    rw [← chartList_set H,List.sum_toFinset _ (chartList_nodup _)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    have ok : bin i.val = accepts true (i.val-1) := by funext t; simp [bin,pos]
    simpa [Function.comp_def,basisTags,ok] using tags_count H a true (i.val-1)

lemma table_above {H : Lines} {k : ℕ} (hk : 10 < k) (first : Bool) : table H first k = 0 := by
  apply sum_eq_zero
  intro b hb
  unfold localTable
  apply sum_eq_zero
  intro T hT
  have n := card_le_card (mem_powerset.mp hT)
  have z := (mem_bases.mp (chart_base hb)).1
  rw [card_sdiff_of_subset (subset_univ _)] at n
  have size : (univ : Finset G).card = 11 := by decide
  rw [size,z] at n
  rw [ite_eq_right (by omega)]

end SplitMatroidFlags
