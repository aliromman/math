module

public import conjectures.SplitMatroidFlags.Enumeration

@[expose] public section

namespace SplitMatroidFlags

open Finset

/-- During kernel replay, update the cell with one traversal of the list. -/
def incrementBin (a : Array ℕ) (i : ℕ) := (a.toList.modify i (· + 1)).toArray

private lemma increment_eq (a : Array ℕ) (i : ℕ) : incrementBin a i = a.modify i (· + 1) := by
  simp only [incrementBin, ← Array.toList_modify, Array.toArray_toList]

/-- Cell zero counts vertex–4-face incidences. Cell d+1 counts d-dimensional faces. -/
def pushTag (a : Array ℕ) (t : ℕ × Bool) :=
  let b := if t.1 = 4 then incrementBin a 0 else a
  if t.2 then incrementBin b (t.1 + 1) else b

def bin (i : ℕ) (t : ℕ × Bool) :=
  if i = 0 then accepts false 4 t else accepts true (i-1) t

@[simp] private lemma size_pushTag (a : Array ℕ) (t : ℕ × Bool) : (pushTag a t).size = a.size := by
  simp only [pushTag, increment_eq]
  split <;> split <;> simp

private lemma value_pushTag (a : Array ℕ) (t : ℕ × Bool) (i : ℕ) (h : i < a.size) :
    (pushTag a t)[i]'(by simpa using h) = a[i] + (bin i t).toNat := by
  obtain ⟨d,b⟩ := t
  cases i with
  | zero =>
    cases b <;> by_cases eq : d = 4 <;> simp [pushTag,increment_eq,bin,eq,accepts,Array.getElem_modify]
  | succ j =>
    cases b <;> by_cases eq : d = 4 <;> by_cases hj : d = j <;>
      simp_all [pushTag,increment_eq,bin,accepts,Array.getElem_modify]
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

/-- Fold each subset directly into the histogram, without building the list of all tags. -/
def tallyBasis (a : Array ℕ) (b : BasisData) :=
  let codes := rowList b.2
  let low := lowRows b.1
  (subsets (outside b.1)).foldl (fun counts t =>
    (sliceList codes t.1).foldl (fun v r =>
      pushTag v (t.2 + overlapCount r, ascending low r)) counts) a

private lemma tallyBasis_eq (a : Array ℕ) (b : BasisData) : tallyBasis a b = tally (basisTags b) a := by
  simp only [tallyBasis, tally, basisTags, tags, List.foldl_flatMap, List.foldl_map]

def accumulate (D : List BasisData) (a : Array ℕ) := D.foldl tallyBasis a

private lemma accumulate_cons (b : BasisData) (D : List BasisData) (a : Array ℕ) :
    accumulate (b :: D) a = accumulate D (tally (basisTags b) a) := by
  simp only [accumulate, List.foldl_cons, tallyBasis_eq]

@[simp] lemma accumulate_size (D : List BasisData) (a : Array ℕ) : (accumulate D a).size = a.size := by
  induction D generalizing a with
  | nil => rfl
  | cons b D ih => rw [accumulate_cons, ih, tally_size]

lemma accumulate_value (D : List BasisData) (a : Array ℕ) (i : ℕ) (hi : i < a.size) :
    (accumulate D a)[i]'(by simpa using hi) = a[i] + (D.map fun b => (basisTags b).countP (bin i)).sum := by
  induction D generalizing a with
  | nil => simp [accumulate]
  | cons b D ih =>
    simp only [accumulate_cons]
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
