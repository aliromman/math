module

public import conjectures.CFPLogDensity.Constant
public import conjectures.CFPLogDensity.Schedule
public import conjectures.CFPLogDensity.LowerTransfer
public import conjectures.CFPLogDensity.Upper
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

public section
namespace CFPLogDensity
open Filter

theorem sampled_eq_real (S : Set ℕ) :
    sampledDensity S = upperLogDensity S := by
  rw [sampledDensity, upperLogDensity, limsup_eq, limsup_eq]
  congr 1
  ext c
  change (∀ᶠ n : ℕ in atTop, logMass S n / Real.log n ≤ c) ↔
    (∀ᶠ x : ℝ in atTop, logMass S ⌊x⌋₊ / Real.log x ≤ c)
  constructor
  · intro h
    have floorT := tendsto_nat_floor_atTop (α := ℝ)
    filter_upwards [floorT.eventually h, floorT.eventually (eventually_ge_atTop (2 : ℕ)), eventually_ge_atTop (2 : ℝ)] with x hb hn hx
    have logpos : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
    have logs : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)) (Nat.floor_le (by linarith))
    have mass : 0 ≤ logMass S ⌊x⌋₊ := by unfold logMass; exact Finset.sum_nonneg fun _ _ => by positivity
    exact (div_le_div_of_nonneg_left mass logpos logs).trans hb
  · intro h
    simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h

/-- The lower bound applies to all color classes with the stated intervals of subset sums. -/
theorem maximal_color {r : ℕ} (hr : 3 ≤ r) {b : ℝ} (hb : Root r b) (S : Fin r → Set ℕ)
    (initial : ∃ D : ℕ, 0<D ∧ ∀ᶠ j : ℕ in atTop,
      ∃ i, ∀ x : ℕ, D*2^j*(j+1)≤x → x≤(2^j)^2/D → x∈S i) :
    value r b ≤ ⨆ i, sampledDensity (S i) := by
  classical
  let M := ⨆ i, sampledDensity (S i)
  change value r b ≤ M
  by_contra! deficit
  have below : max M 0 < value r b := max_lt_iff.mpr ⟨deficit,(value_bounds hr hb).1⟩
  obtain ⟨c,hc,cv⟩ := exists_between below
  obtain ⟨C,cC,Cv⟩ := exists_between cv
  have positive : 0 ≤ C := (le_max_right M 0).trans (hc.trans cC).le
  have below_c (i : Fin r) : sampledDensity (S i) < c :=
    (le_ciSup (Set.finite_range (fun i => sampledDensity (S i))).bddAbove i).trans_lt
      ((le_max_left M 0).trans_lt hc)
  obtain ⟨K,hK,g,hg,curve⟩ := schedule_constants hr hb positive Cv
  obtain ⟨D,hD,intervals⟩ := initial
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventual_shell_counts S below_c cC)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (dense_to_full_shells S D K hD (by omega) intervals)
  apply schedule_impossible (N := max N L) (p := K+1) (q := 2*K-1) (fun i => fullShells (S i))
    (by omega) (by omega) (Cv.trans (value_bounds hr hb).2) hg curve
  · intro t ht i
    exact hN t ((le_max_left N L).trans ht) i
  · intro t ht
    exact hL t ((le_max_right N L).trans ht)

theorem optimum_of_intervals {r : ℕ} (hr : 3≤r)
    (intervals : ∀ color : ℕ→Fin r, ∃ D : ℕ, 0<D ∧ ∀ᶠ j : ℕ in atTop,
      ∃ i, ∀ x : ℕ, D*2^j*(j+1)≤x → x≤(2^j)^2/D → x ∈ subsetSums color i)
    {b : ℝ} (hb : Root r b) : densityConstant r = value r b ∧
      ∃ color : ℕ→Fin r, UsesAll color ∧ (⨆ i, upperLogDensity (subsetSums color i)) = value r b := by
  simp only [densityConstant,← sampled_eq_real]
  let _ : NeZero r := ⟨by omega⟩
  have lower (color : ℕ→Fin r) := maximal_color hr hb (subsetSums color) (intervals color)
  have gap : 2*b ≤ b^r := by
    have rr : (3:ℝ) ≤ r := by exact_mod_cast hr
    have prod := mul_nonneg (show 0≤(r:ℝ)-1 by linarith) (show 0≤2*b-1 by linarith [hb.1])
    nlinarith [hb.2]
  obtain ⟨color,used,bound⟩ := upper_coloring (by omega) hb.1 gap
  let witness : {f : ℕ→Fin r // UsesAll f} := ⟨color,used⟩
  let _ : Nonempty {f : ℕ→Fin r // UsesAll f} := ⟨witness⟩
  refine ⟨?_,color,used,le_antisymm (ciSup_le bound) (lower color)⟩
  apply le_antisymm
  · exact (ciInf_le ⟨value r b,by rintro _ ⟨c,rfl⟩; exact lower c.val⟩ witness).trans (ciSup_le bound)
  · exact le_ciInf (fun c => lower c.val)
end CFPLogDensity
