module

public import conjectures.ChauveHistoryGrowth.Slope

public section
noncomputable section
namespace ChauveHistoryGrowth
open PowerSeries

private theorem cat_two (n : ℕ) : count (cat n) 2+(n+2)^2≤count (cat (n+1)) 2 := by
  rw [cat,fork_count .tip (cat n) 1]
  simp [splits,leaf_one,Tree.leaves,cat_leaves,pow_two]
  nlinarith

private theorem cat_cube (n : ℕ) : ((n:ℝ)+1)^3≤4*(count (cat n) 2 : ℝ) := by
  induction n with
  | zero =>
    have pos := count_pos (cat 0) (n:=2) (by decide)
    norm_num
    exact_mod_cast (show 1≤4*count (cat 0) 2 by omega)
  | succ n ih =>
    have h : (count (cat n) 2 : ℝ)+(n+2:ℝ)^2≤count (cat (n+1)) 2 := by
      exact_mod_cast cat_two n
    push_cast
    nlinarith [sq_nonneg (n:ℝ),show 0≤(n:ℝ) by positivity]

private theorem cat_growth (C : ℝ) : ∃ K : ℕ, ∀ t : Tree, t.Caterpillar →
    K≤t.leaves → C*t.leaves≤growth t := by
  obtain ⟨K,bound⟩ := exists_nat_ge (4*C^2)
  refine ⟨K,fun t ht large => ?_⟩
  have size : 4*C^2≤(t.leaves : ℝ) := bound.trans (by exact_mod_cast large)
  have cube := cat_cube (index t)
  have eq := congrArg (coeff 2) (same_cat ht)
  rw [hc,hc] at eq
  rw [← Nat.cast_add_one,index_size,← eq] at cube
  have lower := mul_le_mul_of_nonneg_right size (sq_nonneg (t.leaves : ℝ))
  have sqr : (nthRoot t 2)^2=(count t 2 : ℝ) := by
    unfold nthRoot
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (by positivity) (by decide)
  have pos : 0≤nthRoot t 2 := Real.rpow_nonneg (by positivity) _
  apply le_trans _ (root_le_growth t (n:=2) (by decide))
  apply le_of_sq_le_sq _ pos
  rw [sqr]; nlinarith

/-- The extremal shapes are unique from size two onward. Their exponential
factors are limits of the roots of the actual finite history counts. -/
theorem resolution : Conjecture := by
  refine ⟨fun k _ => ⟨2,fun n hn t eq => ?_⟩,growth_limit,cat_growth,slope,slope_positive,?_⟩
  · rw [← eq]
    exact structural hn t
  · intro ε hε
    obtain ⟨K,hK⟩:=Metric.tendsto_atTop.mp balanced_slope.2 ε hε
    refine ⟨K,fun t h large => ?_⟩
    rw [factor_of_balanced h]
    exact (Real.dist_eq ..) ▸ hK t.leaves large

/-- info: 'ChauveHistoryGrowth.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end ChauveHistoryGrowth
end
