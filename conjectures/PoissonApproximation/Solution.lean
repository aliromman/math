module

public import conjectures.PoissonApproximation.Bernoulli
public import conjectures.PoissonApproximation.Limit

public section
namespace PoissonApproximation
open Real ProbabilityTheory
open scoped unitInterval

/-- At every common mean from zero to one, the error at zero is the full distance. -/
theorem low_mean (n : ℕ) (hn : 0<n) (r : I) :
    distance (binomial n (parameter n hn r)) (poissonMeasure ⟨r,r.2.1⟩) =
      exp (-(r:ℝ)) - (1-(r:ℝ)/n)^n := by
  rcases eq_or_lt_of_le (show 1≤n by omega) with e|h
  · subst n
    simpa using single_trial r
  · exact many_trials n h r

theorem resolution : Conjecture := by
  intro n hn
  convert low_mean n hn 1 using 3
  congr 1

/-- info: 'PoissonApproximation.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'PoissonApproximation.scaled_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scaled_limit

end PoissonApproximation
