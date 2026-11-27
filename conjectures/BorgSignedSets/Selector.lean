import conjectures.BorgSignedSets.OrbitSelector
import conjectures.BorgSignedSets.CylinderBound

namespace BorgSignedSets

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

/-- An intersecting system has a selector with the required mean, energy
and bounds on each support. -/
theorem exists_selector (F : Finset (Finset ι)) (A : Family ι k) (hk : 2 ≤ k)
    (hF : F.Nonempty) (hn : ∀ B ∈ F, B.Nonempty) (hA : Intersecting F A) :
    ∃ h : Cube ι (ZMod k) → ℚ, SelectorFacts F A h := by
  obtain ⟨B, hB⟩ := hF
  obtain ⟨i, _⟩ := hn B hB
  obtain ⟨L, hshift, hforce⟩ := exists_orbit_label i F A hA
  refine ⟨fun x => orbitScore k (L x), orbit_mean L hshift, orbit_energy L hshift, ?_, ?_, ?_⟩
  · intro x
    by_cases h : L x = 0
    · exact Or.inl (by rw [h, orbitScore_zero])
    · exact Or.inr (orbitScore_nonzero h)
  · intro C hC b hb x hx
    rw [hforce C hC b hb x hx, orbitScore_zero]
  · intro C hC
    exact section_bound_of_label F A hk L hshift hforce C hC (hn C hC)

end BorgSignedSets
