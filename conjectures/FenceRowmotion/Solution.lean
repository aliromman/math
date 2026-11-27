module

public import conjectures.FenceRowmotion.Witness

public section
namespace FenceRowmotion
open Finset

private def encode (I : Finset ℕ) : ℕ := ∑ j ∈ I, 2 ^ j

set_option maxHeartbeats 0

private theorem distinct_masks : ∀ i j : Fin 237, mask i = mask j → i = j := by
  decide +kernel

private theorem encoded : ∀ i : Fin 237, encode (ideals i) = mask i := by
  decide +kernel

private theorem are_ideals : ∀ i : Fin 237, Ideal 3 11 (ideals i) := by
  unfold Ideal
  decide +kernel

private theorem transitions : ∀ i : Fin 237, row 3 11 (ideals i) = ideals (next i) := by
  decide +kernel

theorem witness_orbit : Orbit 3 11 ideals := by
  refine ⟨by decide, ?_, are_ideals, transitions⟩
  intro i j equal
  exact distinct_masks i j (by rw [← encoded, equal, encoded])

theorem total_card : (∑ i, (ideals i).card) = 3774 := by decide +kernel

theorem resolution : ¬ HalfMesic := by
  intro conjecture
  have h := conjecture 3 11 (by decide) (by decide) 237 ideals witness_orbit
  rw [total_card] at h
  exact (by decide : 2 * 3774 ≠ 237 * (3 * 11 - 1)) h

/-- info: 'FenceRowmotion.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end FenceRowmotion
