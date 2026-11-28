module

public import conjectures.BilleyFahrbachTalmageClassification.Statement
public import conjectures.BilleyFahrbachTalmageClassification.PositiveValues
public import conjectures.BilleyFahrbachTalmageClassification.RealRoots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Integral linear factors and translation of the argument -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials

theorem integralRoots_mul {p q : ℝ[X]} (hp : IntegralRoots p) (hq : IntegralRoots q) :
    IntegralRoots (p*q) := by
  intro z hz
  rw [map_mul, mul_eq_zero] at hz
  exact hz.elim (hp z) (hq z)

theorem integralRoots_const {a : ℝ} (ha : a≠0) : IntegralRoots (C a) := by
  intro z hz
  simp [ha] at hz

theorem integralRoots_linear (i : ℤ) : IntegralRoots (X-C (i:ℝ)) := by
  intro z hz
  refine ⟨i,?_⟩
  simpa using sub_eq_zero.mp (show z-(i:ℂ)=0 by simpa using hz)

theorem integralRoots_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (hf : ∀ i∈s, IntegralRoots (f i)) :
    IntegralRoots (∏ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (integralRoots_const (one_ne_zero : (1:ℝ)≠0))
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact integralRoots_mul (hf a (by simp)) (ih fun i hi => hf i (by simp [hi]))

theorem integralRoots_translate {p : ℝ[X]} (hp : IntegralRoots p) (a : ℤ) :
    IntegralRoots (p.comp (X+C (a:ℝ))) := by
  intro z hz
  rw [aeval_comp, map_add, aeval_X, aeval_C] at hz
  obtain ⟨i,hi⟩ := hp _ hz
  use i-a
  push_cast at hi ⊢
  linear_combination hi

theorem integralRoots_of_translate {p : ℝ[X]} (a : ℤ) (hp : IntegralRoots (p.comp (X+C (a:ℝ)))) :
    IntegralRoots p := by
  have h := integralRoots_translate hp (-a)
  simpa [Polynomial.comp_assoc] using h

theorem splits_translate_iff (p : ℝ[X]) (c : ℝ) : (p.comp (X+C c)).Splits ↔ p.Splits :=
  (splits_iff_comp_splits_of_natDegree_eq_one (natDegree_X_add_C c)).symm

noncomputable def prefixPoly (c : ℕ) : ℝ[X] := ∏ j ∈ range c, (X+C ((j:ℝ)+1))

theorem prefixPoly_aeval (c : ℕ) (z : ℂ) : aeval z (prefixPoly c) = risingProduct (z+1) c := by
  simp only [prefixPoly, map_prod, map_add, aeval_X, aeval_C, risingProduct]
  apply prod_congr rfl
  intro j hj
  push_cast
  ring

theorem prefixPoly_splits (c : ℕ) : (prefixPoly c).Splits := Splits.prod (fun _ _ => Splits.X_add_C _)

theorem prefixPoly_integral (c : ℕ) : IntegralRoots (prefixPoly c) := by
  apply integralRoots_prod
  intro j hj
  have h := integralRoots_linear (-((j:ℤ)+1))
  convert h using 1
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, map_neg, sub_neg_eq_add]

theorem prefixPoly_ne_zero (c : ℕ) : prefixPoly c ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  exact fun j _ => X_add_C_ne_zero _

theorem peakPolynomial_ne_zero (A : Finset ℕ) (ha : Admissible A) : peakPolynomial A ≠ 0 := by
  have ht := peak_after_pos A ha (n:=maxPeak A+1) (by omega)
  rintro hz
  simp [hz] at ht

/-- A polynomial identity on the positive real axis gives the translated polynomial identity. -/
theorem positive_axis_identity (S : Finset ℕ) (c : ℕ) (P : ℝ[X])
    (he : ∀ x : ℝ, 0 < x → peakValue S ((c:ℂ)+x) = aeval (x:ℂ) P) :
    (peakPolynomial S).comp (X+C (c:ℝ)) = P := by
  apply eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0:ℝ)).mono
  intro x hx
  have h := he x hx
  have hreal : aeval (x:ℂ) P = ((P.eval x:ℝ):ℂ) := aeval_algebraMap_apply_eq_algebraMap_eval x P
  rw [show (c:ℂ)+(x:ℂ)=(((c:ℝ)+x:ℝ):ℂ) by simp, peakValue_real, hreal] at h
  simpa [eval_comp, add_comm x] using Complex.ofReal_inj.mp h

end BilleyFahrbachTalmageClassification
