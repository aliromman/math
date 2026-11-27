module

public import conjectures.ConsecutiveThreshold.Lehmer
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace ConsecutiveThreshold
open Finset
open scoped BigOperators Classical

def codeLayer (n m : ℕ) : Finset (Code n) := univ.filter fun e => ∑ i, (e i).val = m

private def lowerDigit {n : ℕ} (i : Fin n) (e : Code n) : Code n :=
  fun j => ⟨if j=i then (e j).val-1 else (e j).val,
    by split <;> first | exact (Nat.sub_le _ _).trans_lt (e j).isLt | exact (e j).isLt⟩

private theorem lower_self {n : ℕ} (i : Fin n) (e : Code n) :
    (lowerDigit i e i).val = (e i).val-1 := by simp [lowerDigit]

private theorem lower_other {n : ℕ} {i j : Fin n} (ne : j≠i) (e : Code n) :
    lowerDigit i e j = e j := Fin.ext (by simp [lowerDigit,ne])

private theorem lower_mass {n : ℕ} (i : Fin n) {e : Code n} (hi : 0 < (e i).val) :
    (∑ j, (lowerDigit i e j).val) + 1 = ∑ j,(e j).val := by
  have outside : ∑ j ∈ univ.erase i, (lowerDigit i e j).val = ∑ j ∈ univ.erase i,(e j).val := by
    exact sum_congr rfl fun j hj => by rw [lower_other (mem_erase.mp hj).1]
  have a := sum_erase_add univ (fun j => (lowerDigit i e j).val) (mem_univ i)
  have b := sum_erase_add univ (fun j => (e j).val) (mem_univ i)
  rw [outside,lower_self] at a
  omega

private theorem lower_count (n m : ℕ) (i : Fin n) :
    ∑ e ∈ codeLayer n (m+1), (e i).val ≤ ∑ e ∈ codeLayer n m, ((e i).val+1) := by
  let P := (codeLayer n (m+1)).filter fun e => 0 < (e i).val
  have restrict : ∑ e ∈ P,(e i).val = ∑ e ∈ codeLayer n (m+1),(e i).val := by
    unfold P
    rw [sum_filter]
    apply sum_congr rfl
    intro e _
    split <;> omega
  rw [←restrict]
  apply sum_le_sum_of_injOn (lowerDigit i)
  · intro e he f hf h
    funext j
    by_cases hj : j=i
    · subst j
      have v := congrArg (fun a : Code n => (a i).val) h
      have p := (mem_filter.mp (show e ∈ P from he)).2
      have q := (mem_filter.mp (show f ∈ P from hf)).2
      change (lowerDigit i e i).val=(lowerDigit i f i).val at v
      simp only [lower_self] at v
      exact Fin.ext (by omega)
    · simpa only [lower_other hj] using congrFun h j
  · rintro _ hy
    obtain ⟨e,he,rfl⟩ := mem_image.mp hy
    obtain ⟨h,p⟩ := mem_filter.mp he
    have m₁ := (mem_filter.mp h).2
    have m₂ := lower_mass i p
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  · intro e he
    have hi := (mem_filter.mp he).2
    rw [lower_self]
    omega
  · intros; exact Nat.zero_le _

/-- Lowering a marked digit bounds the ratio of adjacent Mahonian numbers. -/
theorem mahonian_ratio (n m : ℕ) :
    (m+1)*(codeLayer n (m+1)).card ≤ (m+n)*(codeLayer n m).card := by
  calc
    (m+1)*(codeLayer n (m+1)).card =
        ∑ e ∈ codeLayer n (m+1),∑ i,(e i).val := by
          have v (e : Code n) (h : e ∈ codeLayer n (m+1)) : (∑ i,(e i).val)=m+1 := (mem_filter.mp h).2
          rw [sum_congr rfl v]
          simp [Nat.mul_comm]
    _ = ∑ i,∑ e ∈ codeLayer n (m+1),(e i).val := sum_comm
    _ ≤ ∑ i,∑ e ∈ codeLayer n m,((e i).val+1) := sum_le_sum fun i _ => lower_count n m i
    _ = ∑ e ∈ codeLayer n m,∑ i : Fin n,((e i).val+1) := sum_comm
    _ = (m+n)*(codeLayer n m).card := by
      have eq (e) (he : e ∈ codeLayer n m) : (∑ i : Fin n,((e i).val+1))=m+n := by
        rw [sum_add_distrib,(mem_filter.mp he).2]
        simp
      rw [sum_congr rfl eq]
      simp [Nat.mul_comm]

end ConsecutiveThreshold
