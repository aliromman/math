module

public import conjectures.SunCircularDifferences.Statement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic

public section
namespace SunCircularDifferences

private theorem sum_odd_group {G : Type} [AddCommGroup G] [Fintype G]
    (h : Odd (Fintype.card G)) : ∑ x : G, x = 0 := by
  obtain ⟨k, hk⟩ := h
  apply Finset.sum_ninvolution (fun x : G => -x) (by simp) _ (by simp) (by simp)
  intro x hx hneg
  apply hx
  have hx₂ : (2 : ℕ) • x = 0 := by simpa only [two_nsmul, hneg] using (neg_add_cancel x)
  have hz : Fintype.card G • x = 0 := card_nsmul_eq_zero
  rw [hk, add_nsmul, mul_nsmul, hx₂, nsmul_zero, one_nsmul, zero_add] at hz
  exact hz

/-- Omitting two vertices makes distinct cyclic differences impossible in any odd-order group. -/
theorem missing_two {G : Type} [AddCommGroup G] [Fintype G]
    (ho : Odd (Fintype.card G)) {A : Finset G}
    (ha : 2 < A.card) (hc : A.card + 2 = Fintype.card G) : ¬ HasCircle A (· - ·) := by
  classical
  rintro ⟨f, _, hf, hd⟩
  let d := fun i => f i - f (finRotate A.card i)
  let D := Finset.univ.image d
  let S : Finset G := Finset.univ.erase 0
  have hDS : D ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hzero
    have heq := hf (sub_eq_zero.mp hzero)
    have : NeZero A.card := ⟨by omega⟩
    rw [finRotate_apply] at heq
    have hone : (1 : Fin A.card) = 0 := by simpa using (add_eq_left.mp heq.symm)
    have := Fin.one_eq_zero_iff.mp hone
    omega
  have hnD : D.card = A.card := by
    rw [Finset.card_image_of_injective _ hd, Finset.card_univ, Fintype.card_fin]
  have hcard : (S \ D).card = 1 := by
    rw [Finset.card_sdiff_of_subset hDS, hnD, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hxmem : x ∈ S \ D := hx.symm ▸ Finset.mem_singleton_self x
  have hxne := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hxmem).1).1
  have hsumD : ∑ t ∈ D, t = 0 := by
    rw [Finset.sum_image hd.injOn]
    change ∑ i, (f i - f (finRotate A.card i)) = 0
    rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate A.card) f, sub_self]
  have hsumS : ∑ t ∈ S, t = 0 := by
    change ∑ t ∈ Finset.univ.erase (0 : G), t = 0
    rw [Finset.sum_erase _ (f := fun t => t) rfl]
    exact sum_odd_group ho
  have hsum := Finset.sum_sdiff (f := id) hDS
  rw [hx] at hsum
  simp [hsumD, hsumS, hxne] at hsum

/-- No ordering of 0, 1 and 2 modulo 5 has three distinct cyclic differences. -/
theorem counterexample : ¬ Conjecture := by
  intro claim
  let A : Finset (ZMod 5) := {0, 1, 2}
  have hodd : Odd (Fintype.card (ZMod 5)) := ⟨2, by decide⟩
  have existsCircle := (claim (ZMod 5) hodd A (by decide)).2 (by decide)
  exact missing_two hodd (by decide : 2 < A.card) (by decide) existsCircle

/-- info: 'SunCircularDifferences.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample

end SunCircularDifferences
