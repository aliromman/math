module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Poisson.Basic

@[expose] public section
namespace PoissonApproximation
open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Kolmogorov distance for two laws supported on the natural numbers. -/
noncomputable def distance (μ ν : Measure ℕ) : ℝ :=
  ⨆ t : ℝ, |μ.real {j : ℕ | (j : ℝ) ≤ t} - ν.real {j : ℕ | (j : ℝ) ≤ t}|

/-- The success probability that gives mean r in n trials. -/
noncomputable def parameter (n : ℕ) (hn : 0 < n) (r : I) : I :=
  ⟨(r : ℝ) / n, div_nonneg r.2.1 (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast hn : (0:ℝ) < n)).mpr
      (r.2.2.trans (by exact_mod_cast hn : (1:ℝ) ≤ n))⟩

/-- Nagaev and Chebotarev, equation (84). -/
def Conjecture : Prop := ∀ (n : ℕ) (hn : 0 < n),
  distance (binomial n (parameter n hn 1)) (poissonMeasure 1) =
    Real.exp (-1) - (1 - 1 / (n : ℝ)) ^ n

end PoissonApproximation
