module

public import conjectures.PoissonApproximation.Masses
public import conjectures.PoissonApproximation.Endpoints
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace PoissonApproximation
open Real Finset Set ProbabilityTheory MeasureTheory
open scoped unitInterval

private theorem cdf_control (n : ℕ) (hn : 2≤n) (r : I) :
    let x : ℝ := r
    let D k := ∑ i ∈ range (k+1), (bmass n x i - pmass x i)
    ∀ k, |D k| ≤ exp (-x) - (1-x/n)^n := by
  let x : ℝ := r
  let q := 1-x/n
  let D (k : ℕ) := ∑ i ∈ range (k+1), (bmass n x i-pmass x i)
  have h0 : 0≤x := r.2.1
  have h1 : x≤1 := r.2.2
  have N : (2:ℝ)≤n := by exact_mod_cast hn
  have np : (0:ℝ)<n := by linarith
  have qdef : q^n ≤ exp (-x) := zero_deficit n hn h1
  have power : q^n = q^2*q^(n-2) := by
    rw [←pow_add,show 2+(n-2)=n by omega]
  have one_less : q^(n-1) = q*q^(n-2) := by
    rw [←pow_succ',show n-2+1=n-1 by omega]
  have two_choose : (2:ℝ)*(n.choose 2)=n*((n:ℝ)-1) := by
    have t := Nat.descFactorial_eq_factorial_mul_choose n 2
    simp [Nat.descFactorial, Nat.factorial] at t
    have h := congrArg (Nat.cast (R:=ℝ)) t
    push_cast [Nat.cast_sub (by omega : 1≤n)] at h
    linarith
  have b₁ : bmass n x 1 = x*q^(n-1) := by
    simp only [bmass,Nat.choose_one_right,pow_one,q]
    field_simp
  have b₂ : bmass n x 2 = (1-1/n)*x^2*q^(n-2)/2 := by
    unfold bmass
    change _ * _ * q ^ _ = _
    field_simp
    nlinarith [congrArg (fun u : ℝ => u * (x^2*q^(n-2))) two_choose]
  have d₀ : D 0 = q^n-exp (-x) := by simp [D,bmass,pmass,q]
  have d₁ : D 1 = D 0+bmass n x 1-pmass x 1 := by simp [D,sum_range_succ]; ring
  have d₂ : D 2 = D 1+bmass n x 2-pmass x 2 := by simp [D,sum_range_succ]; ring
  have p₁ : pmass x 1 = exp (-x)*x := by simp [pmass]
  have p₂ : pmass x 2 = exp (-x)*x^2/2 := by norm_num [pmass]
  obtain ⟨P₁,P₂⟩ := endpoint_bounds n hn h0 h1
  change (2*q^2+x*q)*q^(n-2) ≤ _ at P₁
  change (4*q^2+2*x*q+(1-1/n)*x^2)*q^(n-2) ≤ _ at P₂
  have upper₁ : D 1 ≤ exp (-x)-q^n := by
    rw [d₁,d₀,b₁,p₁,power,one_less]
    nlinarith only [P₁]
  have upper₂ : D 2 ≤ exp (-x)-q^n := by
    rw [d₂,d₁,d₀,b₁,b₂,p₁,p₂,power,one_less]
    nlinarith only [P₂]
  have decreasing {k l : ℕ} (hk : 2≤k) (hl : k≤l) : D l ≤ D k := by
    induction l,hl using Nat.le_induction with
    | base => rfl
    | succ l hl ih =>
      have m := tail_mass n hn h0 h1 (l+1) (by omega)
      exact (show D (l+1)≤D l by
        change (∑ i∈Finset.range ((l+1)+1), _) ≤ _
        rw [sum_range_succ]
        exact add_le_of_nonpos_right (sub_nonpos.mpr m)).trans ih
  let μ := binomial n (parameter n (by omega) r)
  let ν := poissonMeasure ⟨x,h0⟩
  have : IsProbabilityMeasure ν := ProbabilityTheory.instIsProbabilityMeasureNatPoissonMeasure _
  have v_mass (j : ℕ) : ν.real {j} = pmass x j := poissonMeasure_real_singleton _ _
  have measure_D (k : ℕ) : D k = μ.real (↑(range (k+1)) : Set ℕ) - ν.real (↑(Finset.range (k+1)) : Set ℕ) := by
    rw [←sum_measureReal_singleton,←sum_measureReal_singleton,←sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [v_mass]
    rw [show μ.real {j}=bmass n x j from binomial_real_singleton n j _]
  have large {k : ℕ} (hk : n≤k) : 0 ≤ D k := by
    have ae : ∀ᵐ j ∂μ, j≤n := ae_le_of_hasLaw_binomial (X:=id) HasLaw.id
    have e : (↑(range (k+1)) : Set ℕ) =ᵐ[μ] Set.univ := by
      filter_upwards [ae] with j hj
      simp [show j<k+1 by omega]
    rw [measure_D,measureReal_congr e,probReal_univ]
    exact sub_nonneg.mpr measureReal_le_one
  change ∀ k, |D k|≤exp (-x)-q^n
  intro k
  rcases k with _ | _ | k
  · rw [d₀,abs_of_nonpos (sub_nonpos.mpr qdef)]
    linarith
  · apply abs_le.mpr ⟨?_,upper₁⟩
    have m := first_excess n hn h0 h1
    rw [d₁,d₀]
    linarith
  · have hk : 2≤k+2 := by omega
    have Dpos := (large (show n≤max n (k+2) from le_max_left ..)).trans
      (decreasing hk (le_max_right ..))
    rw [abs_of_nonneg Dpos]
    exact (decreasing (k:=2) (by omega) hk).trans upper₂

/-- The zero threshold realizes the Kolmogorov distance at every mean from zero to one. -/
theorem many_trials (n : ℕ) (hn : 2≤n) (r : I) :
    distance (binomial n (parameter n (by omega) r)) (poissonMeasure ⟨r,r.2.1⟩) =
      exp (-(r:ℝ)) - (1-(r:ℝ)/n)^n := by
  let μ := binomial n (parameter n (by omega) r)
  let ν := poissonMeasure ⟨(r:ℝ),r.2.1⟩
  have : IsProbabilityMeasure ν := ProbabilityTheory.instIsProbabilityMeasureNatPoissonMeasure _
  have v_mass (j : ℕ) : ν.real {j} = pmass (r:ℝ) j := poissonMeasure_real_singleton _ _
  have u_mass (j : ℕ) : μ.real {j} = bmass n (r:ℝ) j := binomial_real_singleton n j _
  let f (t : ℝ) := |μ.real {j : ℕ | (j:ℝ)≤t} - ν.real {j : ℕ | (j:ℝ)≤t}|
  let A := exp (-(r:ℝ)) - (1-(r:ℝ)/n)^n
  change (⨆ t : ℝ, f t) = A
  have bound (t : ℝ) : f t ≤ A := by
    by_cases ht : 0≤t
    · have eq : {j : ℕ | (j:ℝ)≤t} = (↑(range (⌊t⌋₊+1)) : Set ℕ) := by
        ext k
        simp [Nat.le_floor_iff ht]
      unfold f
      rw [eq,←sum_measureReal_singleton,←sum_measureReal_singleton,←sum_sub_distrib]
      simp only [v_mass,u_mass]
      exact cdf_control n hn r ⌊t⌋₊
    · have eq : {j : ℕ | (j:ℝ)≤t} = ∅ := by
        ext k
        simp [show ¬(k:ℝ)≤t by linarith [Nat.cast_nonneg (α:=ℝ) k]]
      simpa [f,eq,A] using sub_nonneg.mpr (zero_deficit n hn r.2.2)
  have hit : f 0=A := by
    have eq : {j : ℕ | (j:ℝ)≤0} = {0} := by ext j; simp
    unfold f
    rw [eq,u_mass,v_mass]
    simp only [bmass,pmass,Nat.choose_zero_right,Nat.cast_one,pow_zero,mul_one,one_mul,
      Nat.sub_zero,Nat.factorial_zero,div_one,A]
    rw [abs_of_nonpos (sub_nonpos.mpr (zero_deficit n hn r.2.2))]
    ring
  apply le_antisymm (ciSup_le bound)
  exact hit ▸ le_ciSup (show BddAbove (Set.range f) from ⟨A,by rintro _ ⟨t,rfl⟩; exact bound t⟩) 0

end PoissonApproximation
