module

public import conjectures.ErdosSuranyi708.Envelope
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708
open Finset

private theorem lift_signed {A : Finset ℕ} {x : ℤ} {M : ℕ} {C : ℝ}
    (hc : 1 ≤ C)
    (h : ∀ y : ℕ, ∃ S ⊆ window y M, Covers A S ∧ (S.card : ℝ) ≤ C) :
    ∃ B ⊆ Ioc x (x + (M : ℤ)),
      (B.card : ℝ) ≤ C ∧ (∏ a ∈ A, (a : ℤ)) ∣ ∏ b ∈ B, b := by
  classical
  by_cases hx : 0 ≤ x
  · obtain ⟨S, hS, hy, hcard⟩ := h x.toNat
    let f : ℕ ↪ ℤ := ⟨Nat.cast, Int.ofNat_injective⟩
    refine ⟨S.map f, ?_, by simpa using hcard, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hb
      obtain ⟨h1,h2⟩ := mem_Ioc.mp (hS ha)
      apply mem_Ioc.mpr
      change x < (a : ℤ) ∧ (a : ℤ) ≤ x + M
      omega
    · change (∏ a ∈ A, a) ∣ (∏ b ∈ S, b) at hy
      have hh := Int.natCast_dvd_natCast.mpr hy
      simpa [f, Nat.cast_prod] using hh
  by_cases hz : 0 ≤ x + M
  · exact ⟨{0}, singleton_subset_iff.mpr (mem_Ioc.mpr ⟨by omega, hz⟩), by simpa using hc, by simp⟩
  let y := (-(x + M) - 1).toNat
  obtain ⟨S, hS, hy, hcard⟩ := h y
  let f : ℕ ↪ ℤ := ⟨fun a ↦ -(a : ℤ), fun a b hh ↦ Int.ofNat_injective (neg_injective hh)⟩
  refine ⟨S.map f, ?_, by simpa using hcard, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hb
    obtain ⟨h1, h2⟩ := mem_Ioc.mp (hS ha)
    apply mem_Ioc.mpr
    change x < -(a : ℤ) ∧ -(a : ℤ) ≤ x + M
    dsimp [y] at h1 h2
    omega
  · rw [prod_map]
    change (∏ a ∈ A, (a : ℤ)) ∣ ∏ b ∈ S, -(b : ℤ)
    rw [prod_neg]
    apply dvd_mul_of_dvd_right
    change (∏ a ∈ A, a) ∣ (∏ b ∈ S, b) at hy
    simpa [Nat.cast_prod] using Int.natCast_dvd_natCast.mpr hy

/-- Reduction of the signed selection statement to the bounded-height transfer. -/
theorem signed_of_transfer (h : TransferBound) {lower : ℕ} (hl : 0 < lower) :
    IntegerIntervalBound lower := by
  intro ε hε
  obtain ⟨N,hN⟩ := positive_of_transfer h ε hε
  refine ⟨N, ?_⟩
  intro A hA hN' hp x
  apply lift_signed (M := A.max' hA)
  · have hcnt : (1 : ℝ) ≤ A.card := by exact_mod_cast card_pos.mpr hA
    nlinarith [mul_nonneg hε.le (Nat.cast_nonneg A.card)]
  · exact hN A hN' (fun a ha ↦ mem_Ioc.mpr ⟨by have := hp a ha; omega, by simpa using le_max' A a ha⟩)

end ErdosSuranyi708
