module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Finset Real Set
namespace AlabamaParadox

private theorem log_factor {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    x*(log 2-1) ≤ log (1-x) + x*log ((2-x)/(1-x)) := by
  let F (t : ℝ) := (1-t)*log (1-t) + t*log (1-t/2) + t
  let D (t : ℝ) := log ((1-t/2)/(1-t)) - t/(2-t)
  have derivF {t : ℝ} (ht : t < 1) : HasDerivAt F (D t) t := by
    have ha : 0 < 1-t := by linarith
    have hb : 0 < 1-t/2 := by linarith
    have hA := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
    have hB := (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).div_const 2)
    convert (((hA.mul (hA.log ha.ne')).add ((hasDerivAt_id t).mul (hB.log hb.ne'))).add
      (hasDerivAt_id t)) using 1
    · rfl
    · dsimp [D]
      rw [Real.log_div hb.ne' ha.ne']
      field_simp [ha.ne', hb.ne', show 2-t ≠ 0 by linarith]
      ring
  have mono : MonotoneOn F (Iio 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f':=D) (convex_Iio 1)
    · exact fun t ht => (derivF ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (derivF (interior_subset ht)).hasDerivWithinAt
    · intro t ht'
      have ht : t < 1 := interior_subset ht'
      have ha : 0 < 1-t := by linarith
      have hb : 0 < 1-t/2 := by linarith
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
      have e : 1-((1-t/2)/(1-t))⁻¹ = t/(2-t) := by
        rw [inv_div]
        field_simp [hb.ne', show 2-t ≠ 0 by linarith]
        ring
      simpa only [D, sub_nonneg, e] using e ▸ h
  have good := mono (show (0:ℝ) ∈ Set.Iio 1 by norm_num) h1 h0
  have ha : 0 < 1-x := by linarith
  have hb : 0 < 1-x/2 := by linarith
  have e : (2-x) = 2*(1-x/2) := by ring
  rw [Real.log_div (by linarith) ha.ne', e, Real.log_mul (by norm_num) hb.ne']
  simp [F] at good
  nlinarith

/-- The probability of at most one success in independent trials with total mean one
is at least `2/e`. The product and sum on the right give this probability. -/
public theorem at_most_one {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hsmall : ∀ i, p i < 1) (hs : ∑ i, p i = 1) :
    2 / exp 1 ≤ (∏ i, (1-p i)) * (1 + ∑ i, p i/(1-p i)) := by
  let b i := (2-p i)/(1-p i)
  have hb i : 0 < b i := div_pos (by linarith [hsmall i]) (by linarith [hsmall i])
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t:=univ) (p:=b) (w:=p) (fun i _ => (hp i).le) hs (fun i _ => hb i)
  simp only [smul_eq_mul] at hj
  have key := sum_le_sum (s:=univ) (fun i _ => log_factor (hp i).le (hsmall i))
  change ∑ i, p i*(log 2-1) ≤ ∑ i, (log (1-p i)+p i*log (b i)) at key
  rw [← sum_mul, hs, one_mul, sum_add_distrib] at key
  have he : ∑ i, p i*b i = 1 + ∑ i, p i/(1-p i) := by
    calc
      _ = ∑ i, (p i + p i/(1-p i)) := by
        apply sum_congr rfl
        intro i _
        dsimp [b]
        field_simp [show 1-p i ≠ 0 by linarith [hsmall i]]
        ring
      _ = _ := by rw [sum_add_distrib, hs]
  have hprod : 0 < ∏ i, (1-p i) := prod_pos (fun i _ => by linarith [hsmall i])
  have hsum : 0 < 1 + ∑ i, p i/(1-p i) := by
    have : 0 ≤ ∑ i, p i/(1-p i) :=
      sum_nonneg (fun i _ => div_nonneg (hp i).le (by linarith [hsmall i]))
    linarith
  rw [he] at hj
  have hlog : log (2/exp 1) ≤ log ((∏ i, (1-p i))*(1+∑ i, p i/(1-p i))) := by
    rw [log_div (by norm_num) (exp_pos 1).ne', log_exp, log_mul hprod.ne' hsum.ne',
      log_prod (fun i _ => by linarith [hsmall i])]
    linarith
  exact (log_le_log_iff (by positivity) (mul_pos hprod hsum)).mp hlog

end AlabamaParadox
