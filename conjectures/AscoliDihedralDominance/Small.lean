module

public import conjectures.AscoliDihedralDominance.FiniteEvaluation
public import conjectures.AscoliDihedralDominance.SmallExact
meta import conjectures.AscoliDihedralDominance.GroupModels
import Mathlib.Tactic.Eval

@[expose] public section
namespace AscoliDihedral
open Finset

def prefixBounds (ds : List ℕ) : ℕ×ℤ :=
  if ds=[2,3] then (4,144) else if ds=[2,4] then (6,2928) else
    if ds=[2,2,3] then (5,7320) else (0,0)

private theorem prefix_correct (ds : List ℕ) :
    let k := (prefixBounds ds).1
    k ≤ Fintype.card (Dih (AbelianModel ds)) + 1 ∧
      (prefixBounds ds).2 ≤ ∑ m∈range k, gainAt (Dih (AbelianModel ds)) m := by
  unfold prefixBounds
  split_ifs with h₁ h₂ h₃
  · subst ds; exact ⟨by decide,low_gain_six.ge⟩
  · subst ds; exact ⟨by decide,low_gain_eight.ge⟩
  · subst ds; exact ⟨by decide,low_gain_twelve.ge⟩
  · simp

def smallCheck (ds : List ℕ) : Bool :=
  let N := Fintype.card (Dih (AbelianModel ds))
  let p := prefixBounds ds
  decide (0 < p.2 + Dih.lowerTotal N p.1
    (Dih.data (packBase N) (modelElements ds) (decide (N≤32))))

private theorem check_sound (ds : List ℕ) (h : smallCheck ds = true) :
    ProductDominant (Dih (AbelianModel ds)) :=
  Dih.finite_case (modelElements ds) (modelElements_nodup ds) (modelElements_toFinset_univ ds) _
    _ (prefix_correct ds).1 _ (prefix_correct ds).2 (of_decide_eq_true h)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
theorem small_models_dominant : ∀ ds ∈ smallModels, ProductDominant (Dih (AbelianModel ds)) := by
  suffices checked : smallModels.all smallCheck = true from
    fun ds hds ↦ check_sound ds (List.all_eq_true.mp checked ds hds)
  -- Verify the list produced by the elementary-divisor enumeration before checking each model.
  have enumerated : smallModels = eval% smallModels := by decide +kernel
  rw [enumerated]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

end AscoliDihedral
