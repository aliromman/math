module

public import conjectures.PoissonApproximation.Statement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace PoissonApproximation
open Real Set Finset ProbabilityTheory MeasureTheory
open scoped unitInterval

/-- The single-trial case, including its degenerate endpoints. -/
theorem single_trial (r : I) :
    distance (binomial 1 (parameter 1 (by decide) r)) (poissonMeasure ⟨r,r.2.1⟩) =
      exp (-(r:ℝ)) - (1-(r:ℝ)) := by
  let x : ℝ := r
  let μ := binomial 1 (parameter 1 (by decide) r)
  let ν := poissonMeasure ⟨x,r.2.1⟩
  have : IsProbabilityMeasure ν := ProbabilityTheory.instIsProbabilityMeasureNatPoissonMeasure _
  have x₀ : 0≤x := r.2.1
  have x₁ : x≤1 := r.2.2
  have mass (j : ℕ) : ν.real {j}=exp (-x)*x^j/j.factorial := poissonMeasure_real_singleton _ _
  have bzero : μ.real {0}=1-x := by simp [μ,parameter,x]
  have pzero : ν.real {0}=exp (-x) := by
    simpa using mass 0
  have pone : ν.real {1}=exp (-x)*x := by
    simpa using mass 1
  have deficit : 1-x≤exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have tails : 2-x ≤ (2+x)*exp (-x) := by
    have E := Real.exp_bound' x₀ x₁ (n:=3) (by decide)
    norm_num [sum_range_succ,Nat.factorial] at E
    have cubic : exp x ≤ 1+x+x^2/2+x^3/4 := by nlinarith [pow_nonneg x₀ 3]
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [mul_le_mul_of_nonneg_left cubic (show 0≤2-x by linarith),sq_nonneg (x^2)]
  let f (t : ℝ) := |μ.real {j : ℕ | (j:ℝ)≤t} - ν.real {j : ℕ | (j:ℝ)≤t}|
  have small {t : ℝ} (hl : 0≤t) (hu : t<1) : f t=exp (-x)-(1-x) := by
    have e : {j : ℕ | (j:ℝ)≤t} = {0} := by
      ext j
      change (j:ℝ)≤t ↔ j=0
      constructor
      · intro a
        have h : j<1 := by exact_mod_cast (a.trans_lt hu : (j:ℝ)<1)
        omega
      · rintro rfl; simpa using hl
    unfold f
    rw [e,bzero,pzero,abs_of_nonpos (sub_nonpos.mpr deficit)]
    ring
  have bound (t : ℝ) : f t≤exp (-x)-(1-x) := by
    by_cases ht : 0≤t
    · by_cases hu : t<1
      · exact (small ht hu).le
      · have one : (1:ℝ)≤t := le_of_not_gt hu
        have e : {j : ℕ | (j:ℝ)≤t} =ᵐ[μ] Set.univ := by
          have H : ∀ᵐ j ∂μ, j≤1 := ae_le_of_hasLaw_binomial (X:=id) HasLaw.id
          filter_upwards [H] with j hj
          simp [(show (j:ℝ)≤1 by exact_mod_cast hj).trans one]
        have sub : (↑(Finset.range 2) : Set ℕ) ⊆ {j : ℕ | (j:ℝ)≤t} := by
          intro j hj
          have h : j<2 := mem_range.mp hj
          exact (show (j:ℝ)≤1 by exact_mod_cast (show j≤1 by omega)).trans one
        have lower := measureReal_mono (μ:=ν) sub
        rw [←sum_measureReal_singleton] at lower
        simp only [sum_range_succ,sum_range_zero,zero_add,pzero,pone] at lower
        unfold f
        rw [measureReal_congr e,probReal_univ,abs_of_nonneg (sub_nonneg.mpr measureReal_le_one)]
        linarith
    · have e : {j : ℕ | (j:ℝ)≤t} = ∅ := by
        ext j
        simp [show ¬(j:ℝ)≤t by linarith [Nat.cast_nonneg (α:=ℝ) j]]
      simpa [f,e] using sub_nonneg.mpr deficit
  apply le_antisymm (ciSup_le bound)
  change exp (-x)-(1-x)≤⨆ t : ℝ, f t
  rw [←small (t:=0) (by norm_num) (by norm_num)]
  exact le_ciSup (show BddAbove (Set.range f) from ⟨_,by rintro _ ⟨t,rfl⟩; exact bound t⟩) 0

end PoissonApproximation
