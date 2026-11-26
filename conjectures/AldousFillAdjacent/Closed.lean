module

public import conjectures.AldousFillAdjacent.Statement
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Embedding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace AldousFillAdjacent
open Finset Filter

def wordProduct {m k : ℕ} (w : Fin k → Option (Fin m)) : Deck m :=
  ((List.ofFn w).map move).prod

private def next {m : ℕ} (i : Fin m) : Fin m :=
  ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- The two selected edges separate the two colors around the circle. -/
private def color {m : ℕ} (j e x : Fin m) : Prop :=
  min j.val e.val < x.val ∧ x.val ≤ max j.val e.val

private theorem crosses {m : ℕ} {j e x : Fin m} (ne : j≠e) :
    (color j e x ↔ color j e (next x)) ↔ x≠j ∧ x≠e := by
  have jlt := j.isLt
  have elt := e.isLt
  have xlt := x.isLt
  have jne : j.val≠e.val := fun h ↦ ne (Fin.ext h)
  simp only [color,next,←Fin.val_ne_iff]
  by_cases wrap : x.val+1<m
  · rw [Nat.mod_eq_of_lt wrap]
    rcases le_total j.val e.val with h|h
    · rw [min_eq_left h,max_eq_right h];omega
    · rw [min_eq_right h,max_eq_left h];omega
  · rw [show x.val+1=m by omega,Nat.mod_self]
    rcases le_total j.val e.val with h|h
    · rw [min_eq_left h,max_eq_right h];omega
    · rw [min_eq_right h,max_eq_left h];omega

private theorem keeps {m : ℕ} {j e : Fin m} (ne : j≠e)
    (l : List (Option (Fin m))) (hj : some j∉l) (he : some e∉l) (v : Fin m) :
    color j e (((l.map move).prod) v) ↔ color j e v := by
  induction l generalizing v with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons,not_or] at hj he
    rw [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    cases a with
    | none => exact ih hj.2 he.2 v
    | some x =>
      let y := ((l.map move).prod) v
      have same := (crosses (x:=x) ne).mpr
        ⟨fun h ↦ hj.1 (congrArg some h.symm),fun h ↦ he.1 (congrArg some h.symm)⟩
      change color j e (Equiv.swap x (next x) y) ↔ color j e v
      apply Iff.trans _ (ih hj.2 he.2 v)
      change color j e (Equiv.swap x (next x) y) ↔ color j e y
      by_cases h : y=x
      · rw [h,Equiv.swap_apply_left];exact same.symm
      by_cases h' : y=next x
      · rw [h',Equiv.swap_apply_right];exact same
      rw [Equiv.swap_apply_of_ne_of_ne h h']

private theorem twice {m : ℕ} {j e : Fin m} (l : List (Option (Fin m)))
    (hj : some j∈l) (he : some e∉l) (closed : (l.map move).prod=1) :
    2≤l.count (some j) := by
  have ne : j≠e := fun h ↦ he (h ▸ hj)
  have positive := List.count_pos_iff.mpr hj
  by_contra! small
  obtain ⟨a,b,rfl⟩ := List.append_of_mem hj
  simp only [List.count_append,List.count_cons_self] at small
  have aj : some j∉a := fun h ↦ by have := List.count_pos_iff.mpr h;omega
  have bj : some j∉b := fun h ↦ by have := List.count_pos_iff.mpr h;omega
  have ae : some e∉a := fun h ↦ he (List.mem_append_left _ h)
  have be : some e∉b := fun h ↦ he (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  let A := (a.map move).prod
  let B := (b.map move).prod
  have eq : A * (Equiv.swap j (next j) * B)=1 := by
    simpa only [A,B,move,next,List.map_append,List.prod_append,List.map_cons,List.prod_cons] using closed
  have val := congrArg (fun π : Deck m ↦ π (B.symm j)) eq
  change A (Equiv.swap j (next j) (B (B.symm j)))= B.symm j at val
  rw [Equiv.apply_symm_apply,Equiv.swap_apply_left] at val
  have qa := keeps ne a aj ae (next j)
  have qb := keeps ne b bj be (B.symm j)
  change color j e (B (B.symm j)) ↔ _ at qb
  rw [Equiv.apply_symm_apply] at qb
  change color j e (A (next j)) ↔ _ at qa
  rw [val] at qa
  exact ((crosses (x:=j) ne).mp (qb.trans qa)).1 rfl

private def letters {m k : ℕ} (w : Fin k → Option (Fin m)) :=
  (List.ofFn w).toFinset.erase none

private theorem few_letters {m k : ℕ} (w : Fin k→Option (Fin m))
    (large : k<m) (closed : wordProduct w=1) : (letters w).card≤k/2 := by
  classical
  let l := List.ofFn w
  have missing : ∃ e : Fin m, some e∉l := by
    by_contra! all
    have every (e : Fin m) : ∃ i, w i=some e := by simpa [l,List.mem_ofFn] using all e
    choose f hf using every
    have inj : Function.Injective f := by
      intro a b eq
      exact Option.some.inj ((hf a).symm.trans (eq ▸ hf b))
    have h := Fintype.card_le_of_injective f inj
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨e,he⟩ := missing
  have bound (a) (ha : a∈letters w) : 2≤l.count a := by
    have h := mem_erase.mp ha
    cases a with
    | none => exact (h.1 rfl).elim
    | some j => exact twice l (List.mem_toFinset.mp h.2) he closed
  have le : 2*(letters w).card≤k := calc
    2*(letters w).card = ∑ _ ∈ letters w, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ letters w,l.count a := sum_le_sum bound
    _ ≤ ∑ a ∈ l.toFinset,l.count a := sum_le_sum_of_subset_of_nonneg (erase_subset ..)
      (fun _ _ _ ↦ Nat.zero_le _)
    _ = l.length := by
      have beq (x y : Option (Fin m)) : @BEq.beq _ instBEqOfDecidableEq x y = (x == y) := by
        apply Bool.eq_iff_iff.mpr
        simp
      simpa only [List.count_eq_countP,beq] using List.sum_toFinset_count_eq_length l
    _ = k := List.length_ofFn
  omega

private def expand {k m : ℕ} (v : (Fin (k/2)→Option (Fin m)) × (Fin k→Option (Fin (k/2)))) :
    Fin k → Option (Fin m) := fun i ↦ (v.2 i).bind v.1

private theorem encodes {m k : ℕ} (w : Fin k→Option (Fin m)) (h : (letters w).card≤k/2) :
    ∃ v, expand v=w := by
  classical
  let S := letters w
  have hs : Fintype.card S ≤ k/2 := by simpa [S] using h
  let e : S ↪ Fin (k/2) := (Fintype.equivFin S).toEmbedding.trans (Fin.castLEEmb hs)
  let label := Function.extend e (fun x : S ↦ x.val) (fun _ ↦ none)
  let code (i : Fin k) := if hi : w i ∈ S then some (e ⟨w i,hi⟩) else none
  refine ⟨(label,code),funext fun i ↦ ?_⟩
  by_cases hi : w i∈S
  · simpa [expand,code,hi,label] using e.injective.extend_apply (fun x : S ↦ x.val)
      (fun _ ↦ none) (⟨w i,hi⟩ : S)
  · have present : w i∈(List.ofFn w).toFinset := by simp [List.mem_ofFn]
    have eq : w i=none := by
      by_contra ne
      exact hi (mem_erase.mpr ⟨ne,present⟩)
    simpa only [expand,code,dite_eq_right hi,Option.bind_none] using eq.symm

/-- Every fixed length admits a uniform bound of order m to the power floor(k/2). -/
theorem closed_count (k : ℕ) : ∃ C : ℕ, ∀ᶠ m in atTop,
    (univ.filter (fun w : Fin k→Option (Fin m) ↦ wordProduct w=1)).card≤C*(m+1)^(k/2) := by
  classical
  refine ⟨(k/2+1)^k,eventually_atTop.mpr ⟨k+1,fun m large ↦ ?_⟩⟩
  have incl : univ.filter (fun w : Fin k→Option (Fin m) ↦ wordProduct w=1) ⊆
      univ.image (expand (k:=k) (m:=m)) := by
    intro w hw
    obtain ⟨v,hv⟩ := encodes w (few_letters w (by omega) (mem_filter.mp hw).2)
    exact mem_image.mpr ⟨v,mem_univ _,hv⟩
  have le := (card_le_card incl).trans card_image_le
  simpa [Fintype.card_prod,Fintype.card_option,Fintype.card_fun,Nat.mul_comm] using le

end AldousFillAdjacent
