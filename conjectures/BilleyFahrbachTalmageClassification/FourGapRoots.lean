module

public import conjectures.BilleyFahrbachTalmageClassification.RealRoots
import Mathlib.Tactic.NormNum

/-! # The five known real roots near the test point -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial

private def knownRoots (c : ℝ) : Multiset ℝ := ↑[c,c+2,c+4,c+6,c+8]

private noncomputable def knownFactors (c : ℝ) : ℝ[X] :=
  ((knownRoots c).map fun t => X-C t).prod

private noncomputable abbrev test : ℂ := 1+(5/2:ℂ)*Complex.I

private theorem real_eval (c : ℝ) : |(knownFactors c).eval (c+1)| = 105 := by
  simp [knownFactors,knownRoots]
  norm_num

private theorem complex_eval (c : ℝ) : 11*105 ≤ ‖aeval ((c:ℂ)+test) (knownFactors c)‖ := by
  have h : aeval ((c:ℂ)+test) (knownFactors c) =
      test * ((test-2) * ((test-4) * ((test-6)*(test-8)))) := by
    simp [knownFactors,knownRoots]
  rw [h]
  apply (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp
  simp only [norm_mul,mul_pow,Complex.sq_norm,Complex.normSq_apply]
  norm_num [test,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im]

/-- If a split polynomial has the five prescribed roots, its modulus grows
by a factor of at least eleven on the test vertical line. -/
theorem fourGap_root_ratio (p : ℝ[X]) (hp : p.Splits) (c : ℝ)
    (hroot : ∀ j ∈ ([0,2,4,6,8]:List ℕ), p.eval (c+j) = 0) :
    11*|p.eval (c+1)| ≤ ‖aeval ((c:ℂ)+(1+(5/2:ℂ)*Complex.I)) p‖ := by
  change 11*|p.eval (c+1)| ≤ ‖aeval ((c:ℂ)+test) p‖
  classical
  by_cases hn : p=0
  · simp [hn]
  have hd : (knownRoots c).Nodup := by simp [knownRoots]
  have hr : knownFactors c ∣ p := (Multiset.prod_X_sub_C_dvd_iff_le_roots hn _).mpr
    ((Multiset.le_iff_subset hd).mpr (by
      intro x hx
      apply (mem_roots hn).mpr
      rcases (show x=c ∨ x=c+2 ∨ x=c+4 ∨ x=c+6 ∨ x=c+8 by simpa [knownRoots] using hx) with
        rfl | rfl | rfl | rfl | rfl
      · simpa using hroot 0 (by simp)
      · simpa using hroot 2 (by simp)
      · simpa using hroot 4 (by simp)
      · simpa using hroot 6 (by simp)
      · simpa using hroot 8 (by simp)))
  obtain ⟨q,hq⟩ := hr
  have hq' : q.Splits := hp.of_dvd hn (hq ▸ dvd_mul_left ..)
  have hval := norm_eval_le_aeval q hq' ((c:ℂ)+test)
  have hRe : ((c:ℂ)+test).re = c+1 := by norm_num [test,Complex.add_re,Complex.mul_re]
  rw [hRe] at hval
  rw [hq,eval_mul,abs_mul,real_eval,map_mul,norm_mul,←mul_assoc]
  exact mul_le_mul (complex_eval c) hval (abs_nonneg _) (norm_nonneg _)

end BilleyFahrbachTalmageClassification
