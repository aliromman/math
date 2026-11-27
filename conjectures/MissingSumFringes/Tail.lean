module

public import conjectures.MissingSumFringes.Cylinder
public import conjectures.MissingSumFringes.Reflection
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Pointwise Classical Topology

noncomputable def decay : ℝ := (2:ℝ)^(-(1/8:ℝ))

theorem decay_pos : 0<decay := Real.rpow_pos_of_pos (by norm_num) _
theorem decay_lt : decay<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem miss_prefix {x n : ℕ} (h : x<n) (A : Finset ℕ) :
    x∉(A∩range n)+(A∩range n) ↔ x∉A+A := by
  have e := Finset.ext_iff.mp (missing_restrict n A) x
  simpa [missing,h] using e

theorem miss_prob {x n : ℕ} (h : x<n) : prob (range n) (fun A ↦ x∉A+A) ≤ decay^x := by
  have eq : prob (range n) (fun A ↦ x∉A+A)=prob (range (x+1)) (fun A ↦ x∉A+A) := by
    rw [←restrict_prob (range_mono (show x+1≤n by omega)) (fun A ↦ x∉A+A)]
    apply prob_congr
    intro A _
    exact (miss_prefix (by omega) A).symm
  rw [eq,prob_count,card_range]
  have raw := reflected_card (t := x+1) (C := range (x+1)) (Subset.rfl)
  simp only [reflected,Nat.add_sub_cancel,card_range,Nat.cast_add,Nat.cast_one] at raw
  rw [div_le_iff₀ (by positivity)]
  convert raw using 1
  · congr 2
    ext A
    simp
  · unfold decay
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
    rw [←Real.rpow_natCast (2:ℝ) (x+1),←Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring

theorem extent_sizes {q n : ℕ} {A : Finset ℕ} (hq : q≤n) (ex : extent n A≤q) :
    missing n A=missing q A := by
  ext x
  constructor
  · intro hx
    have b := le_sup (f := fun i : ℕ ↦ i+1) hx
    change x+1≤extent n A at b
    exact mem_sdiff.mpr ⟨mem_range.mpr (by omega),(mem_sdiff.mp hx).2⟩
  · intro hx
    exact mem_sdiff.mpr ⟨range_mono hq (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩

theorem extent_restrict (q : ℕ) (A : Finset ℕ) : extent q (A∩range q)=extent q A := by
  rw [extent,missing_restrict]; rfl

theorem avg_sum {ι : Type*} (s : Finset ℕ) (a : Finset ι) (v : ι → Finset ℕ → ℝ) :
    avg s (fun A ↦ ∑ i∈a,v i A) = ∑ i∈a,avg s (v i) := by
  simp only [avg,expect_eq_sum_div_card,div_eq_mul_inv,←Finset.sum_mul]
  rw [sum_comm]

theorem prob_any {ι : Type*} (s : Finset ℕ) (I : Finset ι) (p : ι → Finset ℕ → Prop) :
    prob s (fun A ↦ ∃ i∈I,p i A) ≤ ∑ i∈I,prob s (p i) := by
  unfold prob
  rw [←avg_sum s I (fun i A ↦ if p i A then 1 else 0)]
  apply avg_mono
  intro A _
  split
  · next hit =>
      obtain ⟨i,hi,good⟩ := hit
      have h := single_le_sum (fun j (_ : j∈I) ↦ show (0:ℝ) ≤ (if p j A then 1 else 0) by
        split <;> norm_num) hi
      simpa [good] using h
  · exact sum_nonneg fun i _ ↦ by split <;> norm_num

theorem prob_far (q n : ℕ) :
    prob (range n) (fun A ↦ q<extent n A) ≤ decay^q/(1-decay) := by
  let I := (range n).filter (q≤·)
  calc
    _ ≤ prob (range n) (fun A ↦ ∃ x∈I,x∉A+A) := by
      apply prob_mono
      intro A _ h
      have ex := below_extent (n := n) (A := A) (by omega)
      exact ⟨_,mem_filter.mpr ⟨(mem_sdiff.mp ex).1,by omega⟩,(mem_sdiff.mp ex).2⟩
    _ ≤ _ := prob_any _ I _
    _ ≤ ∑ x∈I,decay^x := sum_le_sum fun x hx ↦ miss_prob (mem_range.mp (mem_filter.mp hx).1)
    _ ≤ ∑ x∈range n, decay^(q+x) := by
      refine sum_le_sum_of_injOn (fun x ↦ x-q) ?_ ?_ ?_ (fun _ _ _ ↦ pow_nonneg decay_pos.le _)
      · intro x hx y hy e
        have ax : q≤x := (mem_filter.mp hx).2
        have ay : q≤y := (mem_filter.mp hy).2
        change x-q=y-q at e
        omega
      · intro y hy
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
        exact mem_range.mpr ((Nat.sub_le ..).trans_lt (mem_range.mp (mem_filter.mp hx).1))
      · intro x hx
        rw [Nat.add_sub_of_le (mem_filter.mp hx).2]
    _ ≤ _ := by
      simp_rw [pow_add,←mul_sum]
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg decay_pos.le _)
      rw [←tsum_geometric_of_lt_one decay_pos.le decay_lt]
      exact (summable_geometric_of_lt_one decay_pos.le decay_lt).sum_le_tsum _ (fun _ _ ↦ pow_nonneg decay_pos.le _)

end MissingSumFringes
