module

public import conjectures.AscoliDihedralDominance.FiniteEvaluation
public import conjectures.AscoliDihedralDominance.SmallExact

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

set_option maxRecDepth 200000
private theorem case_3 : smallCheck [3] = true := by decide +kernel

private theorem case_4 : smallCheck [4] = true := by decide +kernel

private theorem case_5 : smallCheck [5] = true := by decide +kernel

private theorem case_2_3 : smallCheck [2,3] = true := by decide +kernel

private theorem case_7 : smallCheck [7] = true := by decide +kernel

private theorem case_2_4 : smallCheck [2,4] = true := by decide +kernel

private theorem case_8 : smallCheck [8] = true := by decide +kernel

private theorem case_3_3 : smallCheck [3,3] = true := by decide +kernel

private theorem case_9 : smallCheck [9] = true := by decide +kernel

private theorem case_2_5 : smallCheck [2,5] = true := by decide +kernel

private theorem case_11 : smallCheck [11] = true := by decide +kernel

private theorem case_2_2_3 : smallCheck [2,2,3] = true := by decide +kernel

private theorem case_3_4 : smallCheck [3,4] = true := by decide +kernel

private theorem case_13 : smallCheck [13] = true := by decide +kernel

private theorem case_2_7 : smallCheck [2,7] = true := by decide +kernel

private theorem case_3_5 : smallCheck [3,5] = true := by decide +kernel

private theorem case_2_2_4 : smallCheck [2,2,4] = true := by decide +kernel

private theorem case_2_8 : smallCheck [2,8] = true := by decide +kernel

private theorem case_4_4 : smallCheck [4,4] = true := by decide +kernel

private theorem case_16 : smallCheck [16] = true := by decide +kernel

private theorem case_17 : smallCheck [17] = true := by decide +kernel

private theorem case_2_3_3 : smallCheck [2,3,3] = true := by decide +kernel

private theorem case_2_9 : smallCheck [2,9] = true := by decide +kernel

private theorem case_19 : smallCheck [19] = true := by decide +kernel

private theorem case_2_2_5 : smallCheck [2,2,5] = true := by decide +kernel

private theorem case_4_5 : smallCheck [4,5] = true := by decide +kernel

private theorem case_3_7 : smallCheck [3,7] = true := by decide +kernel

private theorem case_2_11 : smallCheck [2,11] = true := by decide +kernel

private theorem case_23 : smallCheck [23] = true := by decide +kernel

private theorem case_2_2_2_3 : smallCheck [2,2,2,3] = true := by decide +kernel

private theorem case_2_3_4 : smallCheck [2,3,4] = true := by decide +kernel

private theorem case_3_8 : smallCheck [3,8] = true := by decide +kernel

private theorem case_5_5 : smallCheck [5,5] = true := by decide +kernel

private theorem case_25 : smallCheck [25] = true := by decide +kernel

private theorem case_2_13 : smallCheck [2,13] = true := by decide +kernel

private theorem case_3_3_3 : smallCheck [3,3,3] = true := by decide +kernel

private theorem case_3_9 : smallCheck [3,9] = true := by decide +kernel

private theorem case_27 : smallCheck [27] = true := by decide +kernel

private theorem case_2_2_7 : smallCheck [2,2,7] = true := by decide +kernel

private theorem case_4_7 : smallCheck [4,7] = true := by decide +kernel

private theorem case_29 : smallCheck [29] = true := by decide +kernel

private theorem case_2_3_5 : smallCheck [2,3,5] = true := by decide +kernel

private theorem case_31 : smallCheck [31] = true := by decide +kernel

private def checkedModels := [[3], [4], [5], [2,3], [7], [2,4], [8], [3,3], [9], [2,5], [11], [2,2,3], [3,4], [13], [2,7], [3,5], [2,2,4], [2,8], [4,4], [16], [17], [2,3,3], [2,9], [19], [2,2,5], [4,5], [3,7], [2,11], [23], [2,2,2,3], [2,3,4], [3,8], [5,5], [25], [2,13], [3,3,3], [3,9], [27], [2,2,7], [4,7], [29], [2,3,5], [31]]

theorem small_models_dominant : ∀ ds ∈ smallModels, ProductDominant (Dih (AbelianModel ds)) := by
  have he : smallModels.toFinset = checkedModels.toFinset := by decide +kernel
  have good : checkedModels.all smallCheck = true := by
    simp only [checkedModels,List.all_cons,List.all_nil,case_3,case_4,case_5,case_2_3,case_7,case_2_4,case_8,case_3_3,case_9,case_2_5,case_11,case_2_2_3,case_3_4,case_13,case_2_7,case_3_5,case_2_2_4,case_2_8,case_4_4,case_16,case_17,case_2_3_3,case_2_9,case_19,case_2_2_5,case_4_5,case_3_7,case_2_11,case_23,case_2_2_2_3,case_2_3_4,case_3_8,case_5_5,case_25,case_2_13,case_3_3_3,case_3_9,case_27,case_2_2_7,case_4_7,case_29,case_2_3_5,case_31,Bool.and_self]
  intro ds hds
  apply check_sound
  apply List.all_eq_true.mp good
  apply List.mem_toFinset.mp
  rw [←he]
  exact List.mem_toFinset.mpr hds

end AscoliDihedral
