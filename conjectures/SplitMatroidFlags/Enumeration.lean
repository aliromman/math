module

public import conjectures.SplitMatroidFlags.Tables
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Dedup
import Mathlib.Tactic

@[expose] public section

namespace SplitMatroidFlags

open Finset

def triples (n : ℕ) : List (Three (Fin n)) :=
  let I := List.finRange n
  (I ×ˢ (I ×ˢ I)).map fun t => ⟨t.1,t.2.1,t.2.2⟩

private lemma triples_nodup (n : ℕ) : (triples n).Nodup := by
  apply List.Nodup.map (fun ⟨x,y,z⟩ ⟨a,b,c⟩ h => by simpa using h)
  exact (List.nodup_finRange _).product ((List.nodup_finRange _).product (List.nodup_finRange _))

private lemma triples_mem {n : ℕ} (a : Three (Fin n)) : a ∈ triples n := by
  apply List.mem_map.mpr
  exact ⟨(a.x,a.y,a.z),by simp [List.mem_finRange],rfl⟩

def chartList (H : Lines) := (triples 11).filter (fun a => decide (sorted a ∧ allowed H a.coords))

lemma chartList_nodup (H : Lines) : (chartList H).Nodup := (triples_nodup _).filter _

lemma chartList_set (H : Lines) : (chartList H).toFinset = charts H := by
  ext a
  simp [chartList,triples_mem,chart_in]

def outside (a : Three G) := (List.finRange 11).filter fun i => decide (i ≠ a.x ∧ i ≠ a.y ∧ i ≠ a.z)

private lemma outside_set (a : Three G) : (outside a).toFinset = univ \ a.coords := by
  ext i
  simp [outside,Three.coords]

/-- Enumerate a subset by its bit mask and its size. -/
def subsets : List G → List (ℕ × ℕ)
  | [] => [(0,0)]
  | i :: L =>
    let a := subsets L
    a ++ a.map fun t => (2^i.val ||| t.1,t.2+1)

private lemma subset_sum {L : List G} (hn : L.Nodup) (v : ℕ × ℕ → ℕ) :
    ((subsets L).map v).sum = ∑ T ∈ L.toFinset.powerset, v (mask T,T.card) := by
  induction L generalizing v with
  | nil => simp [subsets,mask]
  | cons i L ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp hn
    have free : i ∉ L.toFinset := by simpa using fresh
    have ab {T : Finset G} (ht : T ∈ L.toFinset.powerset) := fun (h : i ∈ T) => free (mem_powerset.mp ht h)
    have dis : Disjoint L.toFinset.powerset (L.toFinset.powerset.image (insert i)) := by
      apply disjoint_left.mpr
      intro T ht h
      obtain ⟨S,_,rfl⟩ := mem_image.mp h
      exact ab ht (mem_insert_self _ _)
    have inj : Set.InjOn (insert i) (↑L.toFinset.powerset : Set (Finset G)) :=
      fun S hS T hT e => by
        have h := congrArg (·.erase i) e
        simpa [erase_eq_of_notMem (ab hS),erase_eq_of_notMem (ab hT)] using h
    simp only [subsets,List.map_append,List.map_map,List.sum_append,List.toFinset_cons,
      powerset_insert,sum_union dis,sum_image inj,ih nd]
    congr 1
    apply sum_congr rfl
    intro T ht
    have ht' := ab ht
    simp [mask,fold_insert ht',card_insert_of_notMem ht']

def same (r s : Three ℕ) := r.x == s.x && r.y == s.y && r.z == s.z

private lemma same_iff (r s : Three ℕ) : same r s = true ↔ r = s := by
  cases r; cases s; simp [same,and_assoc]

def unique : List (Three ℕ) → List (Three ℕ)
  | [] => []
  | r :: list =>
    let u := unique list
    if u.any (same r) then u else r :: u

private lemma unique_any (list : List (Three ℕ)) (r : Three ℕ) :
    (unique list).any (same r) = true ↔ r ∈ unique list := by simp [same_iff]

private lemma unique_mem {r : Three ℕ} {list : List (Three ℕ)} : r ∈ unique list ↔ r ∈ list := by
  induction list with
  | nil => simp [unique]
  | cons s list ih =>
    simp only [unique]
    split
    · rename_i hit
      rw [List.mem_cons,← ih]
      exact ⟨Or.inr,fun h => h.elim (fun he => he ▸ (unique_any _ _).mp hit) id⟩
    · simp [ih]

private lemma unique_nodup (list : List (Three ℕ)) : (unique list).Nodup := by
  induction list with
  | nil => simp [unique]
  | cons r list ih =>
    simp only [unique]
    split
    · exact ih
    · rename_i h
      exact List.nodup_cons.mpr ⟨fun hr => h ((unique_any _ _).mpr hr),ih⟩

def rowList (N : Three ℕ) := unique ((triples 3).map (fullCode N))

def sliceList (C : List (Three ℕ)) (m : ℕ) := unique (C.map fun r => r.restrict m)

private lemma rowList_set (H : Lines) (a : Three G) : (rowList (rows H a).masks).toFinset = codes H a := by
  ext r
  simp [rowList,unique_mem,codes,triples_mem,mem_tuples]

private lemma sliceList_set (C : List (Three ℕ)) (m : ℕ) :
    (sliceList C m).toFinset = C.toFinset.image (fun r => r.restrict m) := by
  ext r
  simp [sliceList,unique_mem]

/-- A tag gives the face dimension and indicates whether this basis is its first vertex. -/
def tags (C : List (Three ℕ)) (low : Three ℕ) (out : List G) : List (ℕ × Bool) :=
  (subsets out).flatMap fun t => (sliceList C t.1).map fun r => (t.2 + overlapCount r,ascending low r)

def accepts (first : Bool) (d : ℕ) (tag : ℕ × Bool) := tag.1 == d && (!first || tag.2)

private lemma slice_count (C : List (Three ℕ)) (m n : ℕ) (low : Three ℕ) (first : Bool) (d : ℕ) :
    ((sliceList C m).map fun r => (n + overlapCount r,ascending low r)).countP (accepts first d) =
      (((C.toFinset.image fun r => r.restrict m).filter fun r =>
        n + overlapCount r = d ∧ (first = true → ascending low r = true))).card := by
  rw [List.countP_map,List.countP_eq_length_filter,← sliceList_set]
  have nd : (sliceList C m).Nodup := unique_nodup _
  rw [← List.toFinset_card_of_nodup (nd.filter _)]
  apply congrArg Finset.card
  ext r
  cases first <;> simp [accepts,Function.comp_def,sliceList]

lemma tags_count (H : Lines) (a : Three G) (first : Bool) (d : ℕ) :
    (tags (rowList (rows H a).masks) (lowRows a) (outside a)).countP (accepts first d) = localTable H a first d := by
  dsimp only [tags]
  have nd : (outside a).Nodup := (List.nodup_finRange _).filter _
  rw [List.countP_flatMap,subset_sum nd,outside_set]
  unfold localTable
  apply sum_congr rfl
  intro T _
  dsimp only [Function.comp_apply]
  rw [slice_count,rowList_set]
  split
  · rfl
  · rename_i impossible
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro r h
    have eq := (mem_filter.mp h).2.1
    have le : overlapCount r ≤ 2 := min_le_left ..
    omega

end SplitMatroidFlags
