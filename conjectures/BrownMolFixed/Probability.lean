module

public import conjectures.BrownMolFixed.Layers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace BrownMolFixed
open Finset
variable {n : ℕ}

/-- Factor independent choices by their Boolean observations. -/
private theorem observe {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι→Type*} [∀ i,Fintype (A i)]
    (hit : ∀ i,A i→Bool) (mass : ∀ i,A i→ℝ) (F : (ι→Bool)→ℝ) :
    (∑ x : (∀ i,A i),F (fun i ↦ hit i (x i))*∏ i,mass i (x i)) =
      ∑ b : ι→Bool,F b*∏ i,∑ x : A i,if hit i x=b i then mass i x else 0 := by
  classical
  simp_rw [Fintype.prod_sum,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  let h (i : ι) := hit i (x i)
  rw [sum_eq_single_of_mem h (mem_univ _) (by
    intro b _ ne
    obtain ⟨i,no⟩ : ∃ i,b i≠h i := by
      by_contra! same;exact ne (funext same)
    rw [prod_eq_zero (mem_univ i) (by simp [h] at no; simp [Ne.symm no]),mul_zero])]
  simp [h]

private def someLive {m : ℕ} (g : Fin m→Bool) := decide (∃ i,g i=true)
private def mass {m : ℕ} (p : ℝ) (g : Fin m→Bool) := ∏ i,bern p (g i)

private theorem mass_total (m : ℕ) (p : ℝ) : ∑ g : Fin m→Bool,mass p g=1 := by
  unfold mass
  rw [←Fintype.prod_sum (fun (_ : Fin m) (b : Bool) ↦ bern p b)]
  simp [bern]

private theorem mass_none (m : ℕ) (p : ℝ) :
    (∑ g : Fin m→Bool,if someLive g=false then mass p g else 0)=(1-p)^m := by
  classical
  rw [sum_eq_single_of_mem (fun _ ↦ false) (mem_univ _) (by
    intro g _ ne
    have h : ∃ i,g i=true := by
      by_contra! h
      exact ne (funext fun i ↦ by simpa using h i)
    simp [someLive,h])]
  simp [someLive,mass,bern]

private theorem mass_observation (m : ℕ) (p : ℝ) (b : Bool) :
    (∑ g : Fin m→Bool,if someLive g=b then mass p g else 0) =
      if b then 1-(1-p)^m else (1-p)^m := by
  cases b
  · exact mass_none m p
  · have both (g : Fin m→Bool) :
        (if someLive g=true then mass p g else 0)+(if someLive g=false then mass p g else 0)=mass p g := by
      cases someLive g <;> simp
    have h := congrArg (fun f : (Fin m→Bool)→ℝ ↦ ∑ g,f g) (funext both)
    change (∑ g : Fin m→Bool,((if someLive g=true then mass p g else 0)+(if someLive g=false then mass p g else 0)))=(∑ g : Fin m→Bool,mass p g) at h
    rw [sum_add_distrib,mass_none,mass_total] at h
    change _=1-(1-p)^m
    linarith

/-- Occupied layers are independent, and their set must be a nonempty interval. -/
def layerValue {R : Type*} [CommRing R] (w : Fin n→ℕ) (p : R) : R :=
  ∑ b : Fin n→Bool,(if IntervalSupport b then 1 else 0)*
    ∏ i,if b i then 1-(1-p)^(w i) else (1-p)^(w i)

theorem reliability_chain (w : Fin n→ℕ) (p : ℝ) : reliability (chain w) p=layerValue w p := by
  classical
  let E := Equiv.piCurry (fun (i : Fin n) (_ : Fin (w i)) ↦ Bool)
  let F (b : Fin n→Bool) : ℝ := if IntervalSupport b then 1 else 0
  have split := observe (fun i (g : Fin (w i)→Bool) ↦ someLive g)
    (fun _ g ↦ mass p g) F
  simp_rw [mass_observation] at split
  unfold reliability
  calc
    _ = ∑ f : Vertex w→Bool,F (fun i ↦ someLive (E f i))*∏ i,mass p (E f i) := by
      refine sum_congr (by ext f;simp) ?_
      intro f _
      rw [connected_iff,Fintype.prod_sigma]
      have occ : occupied f=fun i ↦ someLive (E f i) := by funext i;rfl
      rw [occ]
      by_cases h : IntervalSupport (fun i ↦ someLive (E f i))
      · simp only [F,h,↓reduceIte,one_mul]
        apply Finset.prod_congr (by ext i;simp)
        intro i _
        apply Finset.prod_congr (by ext j;simp)
        intro j _
        rfl
      · simp only [F,h,↓reduceIte,zero_mul]
    _ = _ := (E.sum_comp (fun g ↦ F (fun i ↦ someLive (g i))*∏ i,mass p (g i))).trans split
theorem continuous_value (w : Fin n→ℕ) : Continuous (fun p : ℝ ↦ layerValue w p) := by
  unfold layerValue
  apply continuous_finsetSum
  intro b _
  apply Continuous.const_mul
  apply continuous_finsetProd
  intro i _
  split_ifs <;> fun_prop

theorem root_between {a b : ℝ} {f : ℝ→ℝ} (ab : a<b) (hf : Continuous f)
    (sign : f a<0 ∧ 0<f b ∨ 0<f a ∧ f b<0) : ∃ x∈Set.Ioo a b,f x=0 := by
  rcases sign with ⟨l,r⟩|⟨l,r⟩
  · exact intermediate_value_Ioo ab.le hf.continuousOn (show 0∈Set.Ioo (f a) (f b) from ⟨l,r⟩)
  · exact intermediate_value_Ioo' ab.le hf.continuousOn (show 0∈Set.Ioo (f b) (f a) from ⟨r,l⟩)

end BrownMolFixed
end
