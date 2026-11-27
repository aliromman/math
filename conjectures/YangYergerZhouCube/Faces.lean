module

public import conjectures.YangYergerZhouCube.Chung
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section
namespace YangYergerZhouCube

open Finset
variable {ι : Type*} [DecidableEq ι]

def weight {ι : Type*} (s : Finset ι) (p : Finset ι → ℕ) : ℚ :=
  ∑ x ∈ s.powerset, (p x : ℚ) / (x.card + 1)

def fold (i : ι) (p : Finset ι → ℕ) (x : Finset ι) := p x + p (insert i x)/2

private def contribution (p : Finset ι → ℕ) (i : ι) (x : Finset ι) : ℚ :=
  if i∈x then ((p x/2 : ℕ) : ℚ) / x.card else (p x : ℚ)/(x.card+1)

private theorem one_face (s : Finset ι) {i : ι} (hi : i∈s) (p : Finset ι → ℕ) :
    weight (s.erase i) (fold i p) = ∑ x ∈ s.powerset, contribution p i x := by
  have split := Finset.sum_powerset_insert (Finset.notMem_erase i s) (contribution p i)
  rw [Finset.insert_erase hi] at split
  rw [weight,split,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have ni : i∉x := fun h => Finset.notMem_erase i s ((Finset.mem_powerset.mp hx) h)
  simp [fold,contribution,ni,Finset.card_insert_of_notMem,add_div]

private theorem all_directions (s x : Finset ι) (hx : x⊆s) (p : Finset ι → ℕ) (h0 : p ∅≤1) :
    (∑ i ∈ s, contribution p i x) + (((p x+1)/2 : ℕ):ℚ) =
      (s.card+1:ℚ) * ((p x:ℚ)/(x.card+1)) := by
  have far : (∑ i ∈ s\x, contribution p i x) = ((s.card:ℚ)-x.card) * ((p x:ℚ)/(x.card+1)) := by
    calc
      _ = ∑ _i ∈ s\x, (p x:ℚ)/(x.card+1) := Finset.sum_congr rfl fun i hi => by
        simp [contribution,(Finset.mem_sdiff.mp hi).2]
      _ = _ := by simp [Finset.card_sdiff_of_subset hx,Nat.cast_sub (Finset.card_le_card hx)]
  have near : (∑ i ∈ x, contribution p i x) = (x.card:ℚ) * (((p x/2 : ℕ):ℚ)/x.card) := by
    calc
      _ = ∑ _i ∈ x, ((p x/2 : ℕ):ℚ)/x.card := Finset.sum_congr rfl fun i hi => by simp [contribution,hi]
      _ = _ := by simp
  rw [← Finset.sum_sdiff hx, far, near]
  by_cases empty : x=∅
  · subst x
    have cases : p ∅=0 ∨ p ∅=1 := by omega
    rcases cases with h|h <;> simp [h]
  · have k : (x.card:ℚ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    have k' : (x.card:ℚ) + 1 ≠ 0 := by exact_mod_cast (show x.card+1≠0 by omega)
    have sum : ((p x/2:ℕ):ℚ) + (((p x+1)/2:ℕ):ℚ) = (p x:ℚ) := by
      exact_mod_cast (show p x/2+(p x+1)/2 = p x by omega)
    rw [← sum]
    field_simp [k,k']
    ring

/-- Sum the weights after pushing all available pairs toward one coordinate face. -/
theorem face_balance (s : Finset ι) (p : Finset ι → ℕ) (h0 : p ∅≤1) :
    (∑ i ∈ s, weight (s.erase i) (fold i p)) + (ceilingMass s p : ℚ) =
      (s.card+1:ℚ) * weight s p := by
  have rewriteFaces : (∑ i ∈ s, weight (s.erase i) (fold i p)) =
      ∑ i ∈ s, ∑ x ∈ s.powerset, contribution p i x := Finset.sum_congr rfl fun _ hi => one_face s hi p
  rw [rewriteFaces,Finset.sum_comm,ceilingMass,Nat.cast_sum,←Finset.sum_add_distrib,weight,Finset.mul_sum]
  exact Finset.sum_congr rfl fun x hx => all_directions s x (Finset.mem_powerset.mp hx) p h0

end YangYergerZhouCube
