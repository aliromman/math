module

public import conjectures.ConsecutiveThreshold.BlockReorder
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

@[expose] public section
namespace ConsecutiveThreshold
open Equiv Finset
open scoped BigOperators Classical

noncomputable def permMass {n : ℕ} (q : ℝ) (P : Perm (Fin n) → Prop) : ℝ :=
  ∑ σ, if P σ then q^inversions σ else 0

/-- At least q^s / k! of the mass of each invariant event has the requested pattern in the block. -/
theorem step_mass {n k : ℕ} (π : Perm (Fin k)) (r : ℕ) (room : r+k ≤ n)
    (q : ℝ) (hq : 0 < q) (hq' : q ≤ 1) (P : Perm (Fin n) → Prop)
    (invP : ∀ σ ρ, P σ → P (σ * blockReorder r room ρ)) :
    permMass q (fun σ ↦ P σ ∧ ¬blockHit π r room σ) ≤
      (1-q^inversions π/(k.factorial : ℝ))*permMass q P := by
  classical
  let hit := blockHit π r room
  let gain (σ : Perm (Fin n)) : ℝ := if P σ ∧ hit σ then q^inversions σ else 0
  have nonneg (σ) : 0 ≤ gain σ := by dsimp [gain]; split <;> positivity
  have transfer (σ : Perm (Fin n)) :
      q^inversions π * (if P σ then q^inversions σ else 0) ≤
        ∑ ρ : Perm (Fin k), gain (σ * blockReorder r room ρ) := by
    by_cases hP : P σ
    · obtain ⟨ρ, hh⟩ := can_force_pattern π σ r room
      have cost := force_cost π σ r room ρ hh
      have hpow := pow_le_pow_of_le_one hq.le hq' (cost.trans_eq (Nat.add_comm _ _))
      have one := Finset.single_le_sum (s := Finset.univ)
        (f := fun ρ : Perm (Fin k) ↦ gain (σ * blockReorder r room ρ))
        (fun _ _ ↦ nonneg _) (Finset.mem_univ ρ)
      change blockHit π r room _ at hh
      rw [pow_add] at hpow
      simp only [hP, ↓reduceIte]
      exact hpow.trans (by simpa [gain,hit,hh,invP σ ρ hP] using one)
    · simp only [hP, ↓reduceIte, mul_zero]
      exact Finset.sum_nonneg (fun _ _ ↦ nonneg _)
  have key : q^inversions π * permMass q P ≤
      (k.factorial : ℝ) * permMass q (fun σ ↦ P σ ∧ hit σ) := by
    calc
      _ = ∑ σ, q^inversions π * (if P σ then q^inversions σ else 0) := Finset.mul_sum ..
      _ ≤ ∑ σ, ∑ ρ : Perm (Fin k), gain (σ * blockReorder r room ρ) :=
        Finset.sum_le_sum (fun σ _ ↦ transfer σ)
      _ = ∑ ρ : Perm (Fin k), ∑ σ, gain (σ * blockReorder r room ρ) := Finset.sum_comm
      _ = ∑ _ : Perm (Fin k), ∑ σ, gain σ := by
        apply Finset.sum_congr rfl
        intro ρ _
        exact Equiv.sum_comp (Equiv.mulRight (blockReorder r room ρ)) gain
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro σ _
        by_cases he : P σ ∧ hit σ <;> simp [gain,he]
  have split : permMass q (fun σ ↦ P σ ∧ ¬hit σ) + permMass q (fun σ ↦ P σ ∧ hit σ) = permMass q P := by
    simp only [permMass, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases h : P σ <;> by_cases hh : hit σ <;> simp [h,hh]
  have facpos : 0 < (k.factorial : ℝ) := by positivity
  have bound : q^inversions π / (k.factorial : ℝ) * permMass q P ≤ permMass q (fun σ ↦ P σ ∧ hit σ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ facpos]
    linarith
  change permMass q (fun σ ↦ P σ ∧ ¬hit σ) ≤ _
  rw [sub_mul, one_mul]
  linarith

end ConsecutiveThreshold
