module

public import conjectures.SidonSetSystems.Probes
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

public section
namespace SidonSetSystems
open Finset Module
open scoped Classical
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem Figure.free_dimension (A : Figure V) (free : A.Free) :
    finrank ℚ A.directions + 1 = A.sites.card := by
  classical
  have independent : AffineIndependent ℚ (fun x : A.sites => (x:V)) := by
    apply (affineIndependent_iff_of_fintype ..).mpr
    intro w hw hz j
    rw [Finset.weightedVSub_eq_linear_combination _ hw] at hz
    obtain ⟨f,hf⟩ := free (fun x => if x=j then 1 else 0)
    have eq := congrArg f.1 hz
    simp only [map_sum,map_smul,map_zero,smul_eq_mul] at eq
    have val (x : A.sites) : f.1 x=(if x=j then 1 else 0)-f.2 := by
      have e := hf x
      unfold Probe.read at e
      linarith
    simp_rw [val,mul_sub] at eq
    rw [sum_sub_distrib,←sum_mul,hw,zero_mul,sub_zero] at eq
    simpa using eq
  have dim := independent.finrank_vectorSpan_add_one
  have vr : Set.range (fun x : A.sites => (x:V))=(A.sites:Set V) := Subtype.range_val
  rw [vr] at dim
  change finrank ℚ (vectorSpan ℚ (A.sites:Set V))+1=A.sites.card
  simpa using dim

/-- Swapping two pairs of independent subspaces preserves their respective dimensions. -/
theorem crossed_spaces [FiniteDimensional ℚ V] (X Y Z W : Submodule ℚ V)
    (xy : Disjoint X Y) (zw : Disjoint Z W) (eq : X⊔W=Y⊔Z) :
    Disjoint X W ∧ Disjoint Y Z ∧ finrank ℚ X=finrank ℚ Z ∧ finrank ℚ Y=finrank ℚ W := by
  have le₁ : X⊔Y ≤ X⊔W := sup_le le_sup_left (by rw [eq]; exact le_sup_left)
  have le₂ : Z⊔W ≤ X⊔W := sup_le (by rw [eq]; exact le_sup_right) le_sup_right
  have a := Submodule.finrank_mono le₁
  have b := Submodule.finrank_mono le₂
  have e₁ := X.finrank_sup_add_finrank_inf_eq Y
  have e₂ := Z.finrank_sup_add_finrank_inf_eq W
  rw [xy.eq_bot,finrank_bot,add_zero] at e₁
  rw [zw.eq_bot,finrank_bot,add_zero] at e₂
  have e₃ := X.finrank_sup_add_finrank_inf_eq W
  have e₄ := Y.finrank_sup_add_finrank_inf_eq Z
  rw [←eq] at e₄
  have d₁ : finrank ℚ (X⊓W : Submodule ℚ V)=0 := by omega
  have d₂ : finrank ℚ (Y⊓Z : Submodule ℚ V)=0 := by omega
  exact ⟨disjoint_iff.mpr (Submodule.finrank_eq_zero.mp d₁),
    disjoint_iff.mpr (Submodule.finrank_eq_zero.mp d₂),by omega,by omega⟩

end SidonSetSystems
