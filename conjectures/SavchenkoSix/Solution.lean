module

public import conjectures.SavchenkoSix.Averaging
public import conjectures.SavchenkoSix.Carousel
public import conjectures.SavchenkoSix.FourMinors
public import conjectures.SavchenkoSix.SevenCheck
public import conjectures.SavchenkoSix.SignedCount
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace SavchenkoSix
open Finset Matrix

/-- The first term measures four-vertex obstructions to local transitivity. -/
theorem deficit {r : ℕ} (T : Tournament (Fin (2*r+1))) (hT : Regular r T) (hn : 7≤2*r+1) :
    64*((orderedSix T:ℤ)-orderedSix (carousel r))=
      6*((((2*r+1).choose 2:ℤ)-14)*excessOn T.sign univ 4-excessOn T.sign univ 6) := by
  let C := carousel r
  have ncard : 7≤Fintype.card (Fin (2*r+1)) := by simpa using hn
  have h := cycle_identity T C hT (carousel_regular r)
  rw [trace_six T ncard,trace_six C ncard,trace_four T ncard,trace_four C ncard,
    minorSum_two T,minorSum_two C,Fintype.card_fin] at h
  have minor (U : Tournament (Fin (2*r+1))) (k : ℕ) :
      minorSum U k=excessOn U.sign univ k+((2*r+1).choose k:ℤ) := by
    rw [excess_eq,Fintype.card_fin]; ring
  rw [minor T 4,minor C 4,minor T 6,minor C 6,show excessOn C.sign univ 4=0 from carousel_excess_four r,
    show excessOn C.sign univ 6=0 from carousel_excess_six r] at h
  linear_combination h

/-- The quantitative gap is uniform over all regular tournaments of the given order. -/
theorem gap {r : ℕ} (T : Tournament (Fin (2*r+1))) (hT : Regular r T) (hn : 7≤2*r+1) :
    6*(4*((2*r+1:ℕ):ℤ)-24)*excessOn T.sign univ 4≤64*((orderedSix T:ℤ)-orderedSix (carousel r)) := by
  rw [deficit T hT hn,←choose_margin (2*r+1) hn]
  linarith only [averaged_bound T hn seven_checked]

private theorem below_six {n : ℕ} (T : Tournament (Fin n)) (hn : n<6) : orderedSix T=0 := by
  have : IsEmpty (Fin 6 ↪ Fin n) := ⟨fun f ↦ by
    have h := Fintype.card_le_of_injective f f.injective
    simp only [Fintype.card_fin] at h
    omega⟩
  simp [orderedSix]

theorem resolution : Conjecture := by
  intro r T hT
  by_cases h : 7≤2*r+1
  · have a := gap T hT h
    have p : 0≤6*(4*((2*r+1:ℕ):ℤ)-24)*excessOn T.sign univ 4 :=
      mul_nonneg (by omega) (four_nonneg T)
    omega
  · have hn : 2*r+1<6 := by omega
    rw [below_six T hn,below_six (carousel r) hn]

/-- info: 'SavchenkoSix.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'SavchenkoSix.gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap

end SavchenkoSix
end
