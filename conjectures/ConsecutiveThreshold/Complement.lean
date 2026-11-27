module

public import conjectures.ConsecutiveThreshold.Statement
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
namespace ConsecutiveThreshold
open Equiv Finset
open scoped BigOperators Classical

/-- Reverse the values and keep the positions fixed. -/
def complement {n : ℕ} (σ : Perm (Fin n)) : Perm (Fin n) := σ.trans Fin.revPerm

@[simp] theorem complement_apply {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) :
    complement σ i = (σ i).rev := rfl

@[simp] theorem complement_complement {n : ℕ} (σ : Perm (Fin n)) :
    complement (complement σ) = σ := by ext i; simp

theorem inversions_add_complement {n : ℕ} (σ : Perm (Fin n)) :
    inversions σ + inversions (complement σ) = n.choose 2 := by
  rw [inversions,inversions,←sum_add_distrib]
  have row (i : Fin n) :
      (univ.filter fun j ↦ i<j ∧ σ j<σ i).card +
      (univ.filter fun j ↦ i<j ∧ complement σ j<complement σ i).card = (Ioi i).card := by
    have fwd : (univ.filter fun j ↦ i<j ∧ σ j<σ i) = (Ioi i).filter fun j ↦ σ j<σ i := by
      ext j; simp
    have rev : (univ.filter fun j ↦ i<j ∧ complement σ j<complement σ i) =
        (Ioi i).filter fun j ↦ ¬σ j<σ i := by
      ext j
      simp only [mem_filter,mem_univ,true_and,mem_Ioi,complement_apply,Fin.rev_lt_rev]
      apply and_congr_right
      intro ord
      exact ⟨fun lt ↦ not_lt_of_ge lt.le,fun neg ↦
        lt_of_le_of_ne (le_of_not_gt neg) (fun eq ↦ ord.ne (σ.injective eq))⟩
    rw [fwd,rev,card_filter_add_card_filter_not]
  calc _ = ∑ i : Fin n, (Ioi i).card := sum_congr rfl fun i _ ↦ row i
       _ = ∑ i : Fin n, (i.rev : ℕ) := by
         apply sum_congr rfl
         intro i _
         rw [Fin.card_Ioi]
         change n-1-i.val=n-(i.val+1)
         omega
       _ = ∑ i : Fin n, i.val := Equiv.sum_comp Fin.revPerm (fun i : Fin n ↦ i.val)
       _ = n.choose 2 := by
         have tri := Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) n
         exact tri.trans ((Finset.sum_range_id n).trans (Nat.choose_two_right n).symm)

theorem inversions_complement {n : ℕ} (σ : Perm (Fin n)) :
    inversions (complement σ) = n.choose 2 - inversions σ := by
  have := inversions_add_complement σ
  omega

theorem contains_complement {k n : ℕ} (π : Perm (Fin k)) (σ : Perm (Fin n)) :
    contains (complement π) (complement σ) ↔ contains π σ := by
  constructor <;> rintro ⟨s,room,h⟩ <;> refine ⟨s,room,fun i j ↦ ?_⟩ <;> simpa using h j i

private theorem filter_count {n : ℕ} (P Q : Perm (Fin n) → Prop) (h : ∀σ, P σ ↔ Q (complement σ)) :
    (univ.filter P).card = (univ.filter Q).card := by
  apply card_bij fun σ _ ↦ complement σ
  · intro σ hσ
    exact mem_filter.mpr ⟨mem_univ _,(h σ).mp (mem_filter.mp hσ).2⟩
  · intro σ _ τ _ eq
    simpa only [complement_complement] using congrArg complement eq
  · intro τ hτ
    exact ⟨complement τ,mem_filter.mpr ⟨mem_univ _,(h _).mpr (by
      simpa only [complement_complement] using (mem_filter.mp hτ).2)⟩,complement_complement τ⟩

theorem occurrence_complement {k : ℕ} (π : Perm (Fin k)) (n m : ℕ) (hm : m≤n.choose 2) :
    occurrence π n m = occurrence (complement π) n (n.choose 2-m) := by
  have layer (σ : Perm (Fin n)) :
      inversions σ=m ↔ inversions (complement σ)=n.choose 2-m := by
    have := inversions_add_complement σ
    omega
  have den := filter_count (n:=n) (fun σ ↦ inversions σ=m) (fun σ ↦ inversions σ=n.choose 2-m) layer
  have num := filter_count (n:=n) (fun σ ↦ inversions σ=m ∧ contains π σ)
    (fun σ ↦ inversions σ=n.choose 2-m ∧ contains (complement π) σ) (fun σ : Perm (Fin n) ↦
    and_congr (layer σ) (contains_complement π σ).symm)
  unfold occurrence
  simp only [filter_filter]
  apply congrArg₂ (fun x y : ℕ ↦ (x : ℝ) / y)
  · convert! num using 2 <;> ext σ <;> simp
  · convert! den using 2 <;> ext σ <;> simp

/-- info: 'ConsecutiveThreshold.occurrence_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms occurrence_complement

end ConsecutiveThreshold
