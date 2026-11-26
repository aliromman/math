module

public import conjectures.AldousFillAdjacent.Green
public import conjectures.AldousFillAdjacent.Closed
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace AldousFillAdjacent
open Finset Filter
open scoped BigOperators

variable {m : ℕ}

private def afterSlot (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

private theorem after_val (i : Fin m) :
    (afterSlot i).val=i.val+1 ∨ ((afterSlot i).val=0 ∧ i.val+1=m) := by
  change (i.val+1)%m=i.val+1 ∨ _
  by_cases h : i.val+1<m
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · have eq : i.val+1=m := by have := i.isLt;omega
    exact Or.inr ⟨by simp [afterSlot,eq],eq⟩

private theorem move_injective (hm : 3≤m) : Function.Injective (@move m) := by
  have ne (i : Fin m) : afterSlot i≠i := by
    intro h; have := congrArg Fin.val h; rcases after_val i with a|⟨a,b⟩ <;> omega
  have sw (i : Fin m) : Equiv.swap i (afterSlot i) ≠ 1 :=
    fun h ↦ ne i (Equiv.swap_eq_refl_iff.mp h).symm
  intro a b eq
  cases a with
  | none => cases b with
    | none => rfl
    | some j => exact False.elim (sw j eq.symm)
  | some i => cases b with
    | none => exact False.elim (sw i eq)
    | some j =>
      congr 1
      change Equiv.swap i (afterSlot i)=Equiv.swap j (afterSlot j) at eq
      by_contra ij
      have act := congrArg (fun σ : Deck m ↦ σ i) eq
      simp only [Equiv.swap_apply_left,Equiv.swap_apply_def,ij,↓reduceIte] at act
      by_cases h : i=afterSlot j
      · simp only [h,↓reduceIte] at act
        have e := congrArg Fin.val h
        have d := congrArg Fin.val act
        rw [←h] at d
        rcases after_val i with u|⟨u,v⟩ <;> rcases after_val j with w|⟨w,z⟩ <;> omega
      · simp only [h,↓reduceIte] at act
        exact ne i act

theorem first_returns (hm : 3≤m) : returnProb m 0=1 ∧
    returnProb m 1=1/((m:ℝ)+1) ∧ returnProb m 2=1/((m:ℝ)+1) := by
  have one (i : Option (Fin m)) : move i=1 ↔ i=none := by
    change move i=move (none : Option (Fin m)) ↔ _
    exact (move_injective hm).eq_iff
  have two (i j : Option (Fin m)) : move i*move j=1 ↔ j=i := by
    constructor
    · intro h
      apply move_injective hm
      simpa [←mul_assoc,move_square] using congrArg (fun x ↦ move i*x) h
    · rintro rfl; exact move_square _
  have inner (i : Option (Fin m)) : (𝔼 j, δ m (move i*move j))=1/((m:ℝ)+1) := by
    simp [delta_value,two,Fintype.card_option]
  constructor
  · simp [returnProb,evolve_zero,delta_value]
  constructor
  · simp [returnProb,evolve_succ,evolve_zero,P_apply,delta_value,
      one,Fintype.card_option]
  · simp [returnProb,evolve_succ,evolve_zero,P_apply,inner]

private theorem product_avg {k : ℕ} (f : (Fin (k+1) → Option (Fin m)) → ℝ) :
    (𝔼 w, f w)=𝔼 i, 𝔼 u, f (Fin.cons i u) := by
  let E := Fin.consEquiv (fun _ : Fin (k+1) ↦ Option (Fin m))
  rw [←Fintype.expect_equiv E (fun p ↦ f (Fin.cons p.1 p.2)) f (fun _ ↦ rfl)]
  exact (by simpa only [univ_product_univ] using
    (expect_product' univ univ (fun a b ↦ f (Fin.cons a b))))

theorem return_count (m k : ℕ) :
    returnProb m k =
      ((univ.filter (fun w : Fin k→Option (Fin m) ↦ wordProduct w=1)).card:ℝ)/((m:ℝ)+1)^k := by
  have dist (j : ℕ) (x : Deck m) :
      evolve m j (δ m) x = 𝔼 w, δ m (x*wordProduct (k:=j) w) := by
    induction j generalizing x with
    | zero => simp [evolve_zero,wordProduct]
    | succ j ih =>
      rw [evolve_succ,P_apply,product_avg]
      apply expect_congr rfl
      intro i _
      rw [ih]
      simp only [wordProduct,List.ofFn_cons,List.map_cons,List.prod_cons,mul_assoc]
  simp only [returnProb,dist,one_mul,delta_value,Fintype.expect_eq_sum_div_card,sum_boole]
  simp [Fintype.card_option]

end AldousFillAdjacent
