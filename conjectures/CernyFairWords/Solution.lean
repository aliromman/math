module

public import conjectures.CernyFairWords.Statement
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.List.Induction
import Mathlib.Order.Setoid.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace CernyFairWords
noncomputable section
open Polynomial

section

variable {α : Type*} [DecidableEq α]

@[simp] theorem pairs_nil (a b : α) : pairs a b [] = 0 := rfl

private theorem pairs_append (a b : α) (v w : List α) :
    pairs a b (v++w) = pairs a b v + pairs a b w + v.count a * w.count b := by
  induction v with
  | nil => simp
  | cons x v ih =>
    simp only [List.cons_append,pairs,List.count_append,ih,List.count_cons]
    split <;> simp_all
    ring

@[simp] theorem pairs_reverse (a b : α) (w : List α) : pairs a b w.reverse = pairs b a w := by
  induction w with
  | nil => rfl
  | cons x w ih => simp [List.reverse_cons,pairs_append,pairs,ih,List.count_cons,add_comm]

theorem fair_pal {w : List α} (hp : w.reverse = w) : Fair w :=
  fun a b => by nth_rw 1 [← hp]; exact pairs_reverse _ _ _

private theorem pair_product {a b : α} (hab : a ≠ b) (w : List α) :
    pairs a b w + pairs b a w = w.count a * w.count b := by
  induction w with
  | nil => simp
  | cons x w ih =>
    by_cases ha : x=a <;> by_cases hb : x=b <;> simp_all [pairs,add_mul,mul_add] <;> omega

private theorem peel (a : α) (w : List α) (h : Fair (a :: w ++ [a])) : Fair w := by
  intro x y
  have H := h x y
  simp only [pairs_append,List.count_cons,pairs,List.count_nil,
    zero_add,mul_ite, mul_one,mul_zero] at H
  by_cases hx : a=x <;> by_cases hy : a=y <;> simp_all <;> omega

private theorem endpoints (a b : α) (w : List α) (hab : a ≠ b)
    (hc : ∀ x, (a :: w ++ [b]).count x ≤ 2) : ¬ Fair (a :: w ++ [b]) := by
  intro h
  have ca := hc a
  have cb := hc b
  have diff := h a b
  have total := pair_product hab w
  simp [hab,hab.symm,pairs,pairs_append] at ca cb diff
  nlinarith [Nat.mul_le_mul (show w.count a ≤ 1 by omega) (show w.count b ≤ 1 by omega)]

/-- A fair word with at most two copies of each letter must read the same in both directions. -/
theorem palindrome_of_counts {w : List α} (hf : Fair w) (hc : ∀ x, w.count x ≤ 2) :
    w.reverse = w := by
  induction w using List.bidirectionalRec with
  | nil => rfl
  | singleton a => rfl
  | cons_append a w b ih =>
    by_cases hab : a=b
    · subst b
      have inner := ih (peel a w hf) (fun x => by have := hc x; simp [List.count_cons] at this; omega)
      simp [List.reverse_cons,inner]
    · exact (endpoints a b w hab hc hf).elim

/-- A fair word that is not a palindrome uses strictly fewer than half its length, rounded up, in distinct letters. -/
theorem support_strict [Fintype α] {w : List α} (hf : Fair w) (hs : ∀ a, a ∈ w)
    (hn : w.reverse ≠ w) : Fintype.card α < (w.length+1)/2 := by
  classical
  let c (a : α) := w.count a
  have pos a : 0 < c a := List.count_pos_iff.mpr (hs a)
  have large : ∃ a, 2 < c a := by
    by_contra! H
    exact hn (palindrome_of_counts hf H)
  have parity (a b : α) (hab : a ≠ b) : 2 ∣ c a * c b := by
    use pairs a b w
    have H := pair_product hab w
    rw [← hf a b] at H
    change w.count a * w.count b = _
    omega
  have odd : ∑ a, c a % 2 ≤ 1 := by
    by_cases h : ∃ a, c a % 2 = 1
    · obtain ⟨a,ha⟩ := h
      have zero (b) (hb : b ≠ a) : c b % 2 = 0 := by
        rcases Nat.prime_two.dvd_mul.mp (parity a b hb.symm) with h | h
        · omega
        · omega
      rw [Finset.sum_eq_single a (fun b _ hb => zero b hb) (by simp),ha]
    · have z (a) : c a % 2 = 0 := by have := not_exists.mp h a; omega
      simp [z]
  have total : ∑ a, c a = w.length := by
    have eq : w.toFinset = Finset.univ := by ext a; simp [hs a]
    simpa only [eq] using w.sum_toFinset_count_eq_length
  have split (a) : c a = 2*(c a/2) + c a%2 := by omega
  have sumsplit := Finset.sum_congr (s₁ := Finset.univ) rfl fun a _ => split a
  rw [total,Finset.sum_add_distrib,← Finset.mul_sum] at sumsplit
  have more : Fintype.card α < ∑ a, (c a/2+c a%2) := by
    obtain ⟨a,ha⟩ := large
    simpa using Finset.sum_lt_sum (s := Finset.univ) (f := fun _ => 1)
      (g := fun a => c a/2+c a%2) (fun i _ => by have := pos i; omega)
      ⟨a,Finset.mem_univ _,by omega⟩
  rw [Finset.sum_add_distrib] at more
  omega

end

private theorem pairs_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (a b : α) (w : List α) :
    pairs (e a) (e b) (w.map e) = pairs a b w := by
  induction w with
  | nil => rfl
  | cons x w ih => simp [pairs,e.injective.eq_iff,List.count_map_of_injective _ _ e.injective,ih]

private theorem pairs_absent {α : Type*} [DecidableEq α] (a b : α) (w : List α)
    (h : a ∉ w ∨ b ∉ w) : pairs a b w = 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rcases h with h | h <;> simp only [List.mem_cons,not_or] at h
    · simp [pairs,Ne.symm h.1,ih (Or.inl h.2)]
    · simp [pairs,List.count_eq_zero.mpr h.2,ih (Or.inr h.2)]

private theorem fair_map {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ↪ β) (w : List α) :
    Fair (w.map e) ↔ Fair w := by
  constructor
  · intro h a b
    simpa only [pairs_map] using h (e a) (e b)
  · intro h a b
    by_cases ha : a ∈ w.map e
    · by_cases hb : b ∈ w.map e
      · obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
        obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb
        simpa only [pairs_map] using h a b
      · rw [pairs_absent _ _ _ (Or.inr hb),pairs_absent _ _ _ (Or.inl hb)]
    · rw [pairs_absent _ _ _ (Or.inl ha),pairs_absent _ _ _ (Or.inr ha)]

def Exceptional {α : Type*} [DecidableEq α] {n : ℕ} (w : Fin n → α) : Prop :=
  Fair (List.ofFn w) ∧ (List.ofFn w).reverse ≠ List.ofFn w

/-- An equality pattern fixes the positions occupied by each letter.
Restrict to fair patterns whose word is not a palindrome. -/
def Shapes (n : ℕ) := {s : Setoid (Fin n) // by classical exact Exceptional (Quotient.mk s)}

instance (n : ℕ) : Fintype (Shapes n) := by
  classical
  let : Fintype (Setoid (Fin n)) := Fintype.ofInjective (fun s : Setoid (Fin n) => s.r)
    fun x y h => Setoid.ext fun a b => Iff.of_eq (congrFun (congrFun h a) b)
  exact Subtype.fintype _

def rank {n : ℕ} (s : Shapes n) : ℕ := Nat.card (Quotient s.val)

theorem rank_lt {n : ℕ} (s : Shapes n) : rank s < (n+1)/2 := by
  classical
  let w := List.ofFn (Quotient.mk s.val)
  have h (a : Quotient s.val) : a ∈ w := List.mem_ofFn.mpr (Quotient.mk_surjective a)
  simpa [rank,w,Nat.card_eq_fintype_card] using support_strict s.prop.1 h s.prop.2

private theorem relabel {n : ℕ} {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (w : Fin n → α) : Exceptional (e ∘ w) ↔ Exceptional w := by
  simp only [Exceptional,← List.map_ofFn,fair_map,← List.map_reverse]
  exact and_congr_right' (not_congr (List.map_injective_iff.mpr e.injective).eq_iff)

private def paint {n k : ℕ} (s : Shapes n) (e : Quotient s.val ↪ Fin k) :
    {w : Fin n → Fin k // Exceptional w} := by
  classical exact ⟨e ∘ Quotient.mk s.val, (relabel e _).2 s.prop⟩

private theorem paint_kernel {n k : ℕ} (s : Shapes n) (e : Quotient s.val ↪ Fin k) :
    Setoid.ker (paint s e).val = s.val :=
  Setoid.ext fun _ _ => e.injective.eq_iff.trans Quotient.eq

private def shapeEquiv (k n : ℕ) : (Σ s : Shapes n, Quotient s.val ↪ Fin k) ≃
    {w : Fin n → Fin k // Exceptional w} := by
  classical
  apply Equiv.ofBijective (fun p => paint p.1 p.2)
  constructor
  · rintro ⟨s,e⟩ ⟨t,f⟩ H
    have st : s = t := Subtype.ext <| (paint_kernel s e).symm.trans
      ((congrArg (fun w => Setoid.ker w.val) H).trans (paint_kernel t f))
    subst t
    have ef : e = f := by
      apply DFunLike.ext
      intro q
      induction q using Quotient.inductionOn with
      | _ i => exact congrFun (congrArg Subtype.val H) i
    cases ef
    rfl
  · intro w
    let s := Setoid.ker w.val
    let e : Quotient s ↪ Fin k := ⟨Setoid.kerLift w.val,Setoid.kerLift_injective w.val⟩
    have h : Exceptional (e ∘ Quotient.mk s) := w.prop
    exact ⟨⟨⟨s,(relabel e _).1 h⟩,e⟩,Subtype.ext rfl⟩

theorem count_exceptional (k n : ℕ) : Nat.card {w : Fin n → Fin k // Exceptional w} =
    ∑ s : Shapes n, k.descFactorial (rank s) := by
  classical
  rw [← Nat.card_congr (shapeEquiv k n),Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  simp [rank,Nat.card_eq_fintype_card]


private theorem reverse_word {α : Type*} {n : ℕ} (w : Fin n → α) :
    (List.ofFn w).reverse = List.ofFn (w ∘ Fin.rev) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [List.getElem_reverse,Fin.rev]
  congr 1
  apply Fin.ext
  dsimp
  omega

private def foldPos {n : ℕ} (i : Fin n) : Fin ((n+1)/2) :=
  ⟨min i.val (n-1-i.val),by have := i.isLt; omega⟩

private def firstPos {n : ℕ} (i : Fin ((n+1)/2)) : Fin n :=
  ⟨i.val,by have := i.isLt; omega⟩

private theorem fold_first {n : ℕ} (i : Fin ((n+1)/2)) : foldPos (firstPos i) = i := by
  apply Fin.ext
  have := i.isLt
  change min _ _ = _
  dsimp [firstPos]
  omega

private def palindromeEquiv (k n : ℕ) : (Fin ((n+1)/2) → Fin k) ≃
    {w : Fin n → Fin k // (List.ofFn w).reverse = List.ofFn w} where
  toFun f := ⟨f ∘ foldPos,by
    rw [reverse_word,List.ofFn_inj]
    funext i
    apply congrArg f (Fin.ext ?_)
    have := i.isLt
    dsimp [foldPos,Fin.rev]
    omega⟩
  invFun w := w.val ∘ firstPos
  left_inv f := funext fun i => congrArg f (fold_first i)
  right_inv w := by
    apply Subtype.ext
    funext i
    have h := w.prop
    rw [reverse_word,List.ofFn_inj] at h
    have e : firstPos (foldPos i) = i ∨ firstPos (foldPos i) = i.rev := by
      have := i.isLt
      simp only [Fin.ext_iff, firstPos,foldPos,Fin.rev]
      omega
    rcases e with e | e
    · exact congrArg w.val e
    · exact (congrArg w.val e).trans (congrFun h i)

private def splitWords (k n : ℕ) : {w : Fin n → Fin k // Fair (List.ofFn w)} ≃
    {w : Fin n → Fin k // (List.ofFn w).reverse = List.ofFn w} ⊕
    {w : Fin n → Fin k // Exceptional w} where
  toFun w := if h : (List.ofFn w.val).reverse = List.ofFn w.val then
    .inl ⟨_,h⟩ else .inr ⟨_,w.prop,h⟩
  invFun := Sum.elim (fun w => ⟨w.val,fair_pal w.prop⟩) (fun w => ⟨w.val,w.prop.1⟩)
  left_inv w := by dsimp; split <;> rfl
  right_inv w := by
    cases w with
    | inl w => simp [w.prop]
    | inr w => simp [w.prop.2]

/-- Each nonpalindromic pattern can be colored by any injection of its letters
into the alphabet. A palindrome is determined by its first half. -/
theorem expansion (k n : ℕ) : count k n = k^((n+1)/2) + ∑ s : Shapes n, k.descFactorial (rank s) := by
  rw [count,Nat.card_congr (splitWords k n),Nat.card_sum,← Nat.card_congr (palindromeEquiv k n),
    count_exceptional,Nat.card_fun]
  simp

private theorem rank_two {n : ℕ} (s : Shapes n) : 2 ≤ rank s := by
  classical
  by_contra! h
  have H : Subsingleton (Quotient s.val) := Fintype.card_le_one_iff_subsingleton.mp
    (by simpa only [rank,Nat.card_eq_fintype_card] using (show rank s ≤ 1 by omega))
  apply s.prop.2
  exact List.ext_getElem (by simp) fun _ _ _ => Subsingleton.elim _ _

private def term {n : ℕ} (s : Shapes n) : ℤ[X] :=
  (descPochhammer ℤ (rank s - 1)).comp (X - 1)

private theorem degree_term {n : ℕ} (s : Shapes n) : (term s).natDegree + 2 ≤ (n+1)/2 := by
  have h := rank_lt s
  have h₂ := rank_two s
  have hd : (X-1:ℤ[X]).natDegree = 1 := natDegree_X_sub_C (1:ℤ)
  simpa [term,natDegree_comp,hd] using (show rank s - 1 + 2 ≤ (n+1)/2 by omega)

private theorem term_one {n : ℕ} (s : Shapes n) : (term s).eval 1 = 0 := by
  have h := rank_two s
  simp [term,eval_comp,show rank s - 1 ≠ 0 by omega]

private theorem term_eval {n : ℕ} (s : Shapes n) (k : ℕ) : (k.descFactorial (rank s) : ℤ) = k*(term s).eval (k:ℤ) := by
  have rank_pos := rank_two s
  have h := descPochhammer_succ_left ℤ (rank s-1)
  rw [show rank s - 1 + 1 = rank s by omega] at h
  have ev := congrArg (fun p : ℤ[X] => p.eval (k:ℤ)) h
  simpa [term,descPochhammer_eval_eq_descFactorial] using ev

theorem resolution : Conjecture := by
  classical
  intro n hn
  let p := ∑ s : Shapes n, term s
  refine ⟨p,?_,?_,?_⟩
  · rcases isEmpty_or_nonempty (Shapes n) with h | h
    · exact Or.inl (by simp [p])
    · right
      obtain ⟨s⟩ := h
      have hs := degree_term s
      have hd := natDegree_sum_le_of_forall_le (Finset.univ : Finset (Shapes n)) term (n := (n+1)/2-2)
        (fun i _ => by have := degree_term i; omega)
      dsimp [p]
      omega
  · simp [p,eval_finsetSum,term_one]
  · intro k _
    have hd : 0 < (n+1)/2 := by omega
    have add := expansion k n
    rw [add]
    push_cast
    rw [mul_add,← pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ (n+1)/2)]
    congr 1
    simp [p,eval_finsetSum,Finset.mul_sum,term_eval]

/-- info: 'CernyFairWords.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end
end CernyFairWords
