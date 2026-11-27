module

public import conjectures.ConsecutiveThreshold.Lehmer
import Mathlib.Data.Finset.Sort

@[expose] public section
namespace ConsecutiveThreshold
open Equiv Finset

/-- Two permutations with the same initial Lehmer digits have the same initial values. -/
private theorem prefix_values (n : ℕ) (σ τ : Perm (Fin n)) (r : ℕ)
    (h : ∀ i : Fin n, i.val < r → digit σ i = digit τ i) :
    ∀ i : Fin n, i.val < r → σ i = τ i := by
  induction n using Nat.twoStepInduction generalizing r with
  | zero => intro i; exact Fin.elim0 i
  | one => intro i _; exact Subsingleton.elim _ _
  | more n _ ih =>
    obtain ⟨⟨p,S⟩,rfl⟩ := (Perm.decomposeFin' (n := n)).symm.surjective σ
    obtain ⟨⟨q,T⟩,rfl⟩ := (Perm.decomposeFin' (n := n)).symm.surjective τ
    simp only [Perm.decomposeFin'_symm] at *
    intro i hi
    have h0 := h 0 (by simpa using Nat.zero_lt_of_lt hi)
    obtain rfl : p=q := Fin.ext (by simpa only [digit_zero,Perm.decomposeFin'Symm_zero] using h0)
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [Perm.decomposeFin'Symm_succ]
      apply congrArg
      apply ih S T (r-1)
      · intro j hj
        have he := h j.succ (by simp only [Fin.val_succ]; omega)
        simpa only [digit_succ] using he
      · simp only [Fin.val_succ] at hi
        omega

/-- The relative order within an interval depends only on the digits at its positions. -/
theorem interval_comparison (n r k : ℕ) (σ τ : Perm (Fin n))
    (h : ∀ i : Fin n, r ≤ i.val → i.val < r+k → digit σ i = digit τ i)
    (i j : Fin n) (hi : r ≤ i.val) (hi' : i.val < r+k)
    (hj : r ≤ j.val) (hj' : j.val < r+k) : σ i < σ j ↔ τ i < τ j := by
  induction n using Nat.twoStepInduction generalizing r with
  | zero => exact Fin.elim0 i
  | one => have eq : i = j := Subsingleton.elim _ _; rw [eq]; simp
  | more n _ ih =>
    cases r with
    | zero =>
      simp only [zero_add] at h hi' hj'
      have H := prefix_values _ σ τ k (fun i h' ↦ h i (Nat.zero_le _) h')
      rw [H i hi', H j hj']
    | succ r =>
      obtain ⟨⟨p,S⟩,rfl⟩ := (Perm.decomposeFin' (n := n)).symm.surjective σ
      obtain ⟨⟨q,T⟩,rfl⟩ := (Perm.decomposeFin' (n := n)).symm.surjective τ
      simp only [Perm.decomposeFin'_symm] at *
      induction i using Fin.cases with
      | zero => simp at hi
      | succ i =>
        induction j using Fin.cases with
        | zero => simp at hj
        | succ j =>
          simp only [Perm.decomposeFin'Symm_succ, Fin.succAbove_lt_succAbove_iff]
          apply ih r S T
          · intro l hl hl'
            have he := h l.succ (by simpa only [Fin.val_succ, Nat.succ_le_succ_iff] using hl)
              (by simp only [Fin.val_succ]; omega)
            simpa only [digit_succ] using he
          all_goals simp only [Fin.val_succ] at *; omega

/-- Positions in a consecutive block in their natural order. -/
def blockPos {n k : ℕ} (r : ℕ) (room : r+k≤n) (i : Fin k) : Fin n :=
  ⟨r+i.val, by have := i.isLt; omega⟩

theorem blockPos_strict {n k : ℕ} (r : ℕ) (room : r+k≤n) : StrictMono (blockPos r room) := by
  intro i j h
  change r+i.val < r+j.val
  omega

def blockHit {k n : ℕ} (π : Perm (Fin k)) (r : ℕ) (room : r+k≤n) (σ : Perm (Fin n)) : Prop :=
  ∀ i j : Fin k, π i < π j ↔ σ (blockPos r room i) < σ (blockPos r room j)

theorem blockHit_local {k n : ℕ} (π : Perm (Fin k)) (r : ℕ) (room : r+k ≤ n)
    (σ τ : Perm (Fin n)) (h : ∀ i : Fin n, r ≤ i.val → i.val < r+k → digit σ i=digit τ i) :
    blockHit π r room σ ↔ blockHit π r room τ := by
  have eq (i j : Fin k) := interval_comparison _ r k σ τ h (blockPos r room i)
    (blockPos r room j) (by simp [blockPos]) (by simp [blockPos])
    (by simp [blockPos]) (by simp [blockPos])
  constructor
  · exact fun h i j ↦ (h i j).trans (eq i j)
  · exact fun h i j ↦ (h i j).trans (eq i j).symm

end ConsecutiveThreshold
