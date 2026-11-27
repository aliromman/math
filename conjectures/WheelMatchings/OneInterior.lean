module

public import conjectures.WheelMatchings.Geometry

@[expose] public section

namespace WheelMatchings

/-- The point at horizontal coordinate one is raised from height two to height five. -/
def height (i : Fin 12) : ℤ := if i.val = 1 then 5 else 2 * (i.val : ℤ)^2

def oneInterior (i : Fin 12) : Point := ((i.val : ℝ), (height i : ℝ))

def interiorSigns : Turn 12 := fun i j k ↦ decide (i.val ≠ 0 ∨ j.val ≠ 1 ∨ k.val ≠ 2)

private theorem interior_signs (i j k : Fin 12) (hij : i < j) (hjk : j < k) :
    if interiorSigns i j k then 0 < orient (oneInterior i) (oneInterior j) (oneInterior k)
    else orient (oneInterior i) (oneInterior j) (oneInterior k) < 0 := by
  let det (i j k : Fin 12) : ℤ :=
    ((j.val : ℤ) - i.val) * (height k - height i) - (height j - height i) * ((k.val : ℤ) - i.val)
  have hall : ∀ i j k : Fin 12, i < j → j < k →
      if interiorSigns i j k then 0 < det i j k else det i j k < 0 := by decide +kernel
  have h := hall i j k hij hjk
  split at h
  · rename_i hs
    simp only [hs, ↓reduceIte]
    dsimp [oneInterior, orient, det] at *
    exact_mod_cast h
  · rename_i hs
    simp only [hs]
    dsimp [oneInterior, orient, det] at *
    exact_mod_cast h

theorem oneInterior_general : General oneInterior := by
  refine ⟨fun i j h ↦ Fin.ext ?_, fun i j k hij hjk ↦ ?_⟩
  · have he : (i.val : ℝ) = j.val := congrArg Prod.fst h
    exact_mod_cast he
  · have h := interior_signs i j k hij hjk
    split at h
    · exact h.ne'
    · exact h.ne

/-- A supporting line with slope 4i touches each point other than point one alone. -/
theorem exposed (i : Fin 12) (hi : i ≠ 1) (j : Fin 12) (hj : j ≠ i) :
    (oneInterior i).2 - 4 * i.val * (oneInterior i).1 <
    (oneInterior j).2 - 4 * i.val * (oneInterior j).1 := by
  have hall : ∀ i j : Fin 12, i ≠ 1 → j ≠ i →
      height i - 4 * (i.val : ℤ) * i.val < height j - 4 * (i.val : ℤ) * j.val := by decide +kernel
  dsimp [oneInterior]
  exact_mod_cast hall i j hi hj

/-- Point one is a strict convex combination of three of the exposed vertices. -/
theorem interior_coordinates : oneInterior 1 =
    (23/44 : ℝ) • oneInterior 0 + (17/36 : ℝ) • oneInterior 2 + (1/198 : ℝ) • oneInterior 11 := by
  ext <;> norm_num [oneInterior, height, Prod.smul_def, Prod.add_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oneInterior_count : count (m := 6) oneInterior 10 = 248 := by
  apply (count_by_signs _ interiorSigns interior_signs 10).trans
  decide +kernel

end WheelMatchings
