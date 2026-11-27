module

public import conjectures.ConsecutiveThreshold.MahonianRatio
public import conjectures.ConsecutiveThreshold.Pairing
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
namespace ConsecutiveThreshold
open Finset
open scoped BigOperators Classical

noncomputable def mono (q : ℝ) (m : ℕ) : Series := AddMonoidAlgebra.single (m:ℤ) (q^m)

private theorem mono_add (q : ℝ) (j k : ℕ) : mono q (j+k)=mono q j*mono q k := by
  simp [mono,AddMonoidAlgebra.single_mul_single,pow_add]

private theorem mono_sum {I : Type*} (q : ℝ) (d : I → ℕ) (S : Finset I) :
    mono q (∑ i∈S,d i)=∏ i∈S,mono q (d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mono]; rfl
  | insert x S hx ih => rw [sum_insert hx,prod_insert hx,mono_add,ih]

/-- The generating function for a box of independent bounded digits. -/
theorem weight_all (q : ℝ) {I : Type*} [DecidableEq I] [Fintype I] (d : I → ℕ) :
    (∑ e : ∀ i, Fin (d i), mono q (∑ i,(e i).val))=∏ i,geom q (d i) := by
  classical
  simp_rw [mono_sum]
  rw [← Fintype.prod_sum (fun (i : I) (j : Fin (d i)) => mono q j.val)]
  apply prod_congr rfl
  intro i _
  exact Fin.sum_univ_eq_sum_range (mono q) (d i)

noncomputable def eventSeries {n : ℕ} (q : ℝ) (B : Code n → Prop) : Series :=
  ∑ e : Code n, if B e then mono q (∑ i,(e i).val) else 0

theorem event_atOne {n : ℕ} (q : ℝ) (B : Code n → Prop) :
    atOne (eventSeries q B)=∑ e ∈ univ.filter B, q^(∑ i,(e i).val) := by
  classical
  simp [eventSeries,map_sum,sum_filter,apply_ite,mono]

theorem event_coeff {n : ℕ} (q : ℝ) (B : Code n → Prop) (m : ℕ) :
    (eventSeries q B).coeff (m:ℤ)=(((codeLayer n m).filter B).card:ℝ)*q^m := by
  classical
  unfold eventSeries
  rw [coeff_sum]
  have term (e : Code n) :
      (if B e then mono q (∑ i,(e i).val) else 0).coeff (m:ℤ)=
        if (∑ i,(e i).val)=m ∧ B e then q^m else 0 := by
    by_cases h : B e
    · simp only [h,ite_true,and_true,mono,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,
        Nat.cast_inj]
      split <;> simp_all
    · simp [h]
  simp_rw [term]
  rw [←sum_filter]
  have setEq : univ.filter (fun e : Code n => (∑ i,(e i).val)=m ∧ B e)=(codeLayer n m).filter B := by
    ext e
    simp [codeLayer]
  rw [setEq]
  simp

private theorem positive_mono {q : ℝ} (hq : 0≤q) (m : ℕ) : positiveSeries (mono q m) := by
  intro j
  simp only [mono,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split <;> first | exact pow_nonneg hq _ | exact le_rfl

/-- Restricting an event on S leaves the remaining digit generating function as an exact factor. -/
theorem event_factor {n : ℕ} {q : ℝ} (hq : 0≤q) (S : Finset (Fin n)) (B : Code n → Prop)
    (depends : ∀ e f : Code n, (∀ i∈S,e i=f i) → (B e ↔ B f)) :
    ∃ E : Series, positiveSeries E ∧ eventSeries q B=E*(∏ i∈Sᶜ,geom q (n-i.val)) := by
  classical
  let L := (i : {i : Fin n // i∈S}) → Fin (n-i.val.val)
  let R := (i : {i : Fin n // i∉S}) → Fin (n-i.val.val)
  let splitCode : Code n ≃ L × R := Equiv.piEquivPiSubtypeProd (· ∈ S) (fun i : Fin n => Fin (n-i.val))
  let zeroR : R := fun i => ⟨0,by have := i.val.isLt; omega⟩
  let admiss (v : L) := B (splitCode.symm (v,zeroR))
  let left (v : L) : Series := if admiss v then mono q (∑ i,(v i).val) else 0
  let right (v : R) : Series := mono q (∑ i,(v i).val)
  have coord (e : Code n) : (B e ↔ admiss (splitCode e).1) := by
    apply depends
    intro i hi
    have hr := congrArg Prod.fst (splitCode.apply_symm_apply ((splitCode e).1,zeroR))
    exact (congrFun hr ⟨i,hi⟩).symm
  have wt (e : Code n) : (∑ i,(e i).val)=
      (∑ i : {i : Fin n // i∈S},(e i.val).val)+ (∑ i : {i : Fin n // i∉S},(e i.val).val) := by
    exact (sum_add_sum_compl S (fun i => (e i).val)).symm.trans (congrArg₂ Nat.add
      (sum_subtype S (fun _ => Iff.rfl) (fun i => (e i).val))
      (sum_subtype Sᶜ (fun x => mem_compl (s:=S) (a:=x)) (fun i => (e i).val)))
  refine ⟨∑ l : L,left l,?_,?_⟩
  · intro j
    rw [coeff_sum]
    apply sum_nonneg
    intro l _
    dsimp only [left]
    split
    · exact positive_mono hq _ _
    · simp
  · have rest : (∑ v : R,right v)=∏ i∈Sᶜ,geom q (n-i.val) := by
      change (∑ v : (i : {i : Fin n // i∉S}) → Fin (n-i.val.val),
        mono q (∑ i,(v i).val))=_
      exact (weight_all q (fun i : {i : Fin n // i∉S} => n-i.val.val)).trans
        (prod_subtype Sᶜ (fun x => mem_compl (s:=S) (a:=x)) (fun i => geom q (n-i.val))).symm
    rw [←rest]
    calc
      eventSeries q B = ∑ z : L × R, left z.1 * right z.2 := by
        unfold eventSeries
        apply Fintype.sum_equiv splitCode
        intro e
        by_cases h : B e
        · have yes := (coord e).mp h
          simp only [h,ite_true,left,yes,right]
          rw [wt,mono_add]
          rfl
        · have no := (coord e).not.mp h
          simp [h,left,no]
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp_rw [←mul_sum]
        rw [←sum_mul]

end ConsecutiveThreshold
