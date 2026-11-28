module

public import conjectures.BilleyFahrbachTalmageClassification.SquarePolynomials
public import conjectures.BilleyFahrbachTalmageClassification.DifferenceBounds
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Rational coefficients for a gap followed by gaps of size two -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification.Square
open Finset

/-- The pair at index k represents the power differences of orders k and k+1,
after division by y and substitution of y² for the argument. -/
def powerRows : ℕ → Row × Row
  | 0 => ([], [1])
  | k+1 => let (a,b) := powerRows k
           (b, add b (linear (-1/4) (1/4) a))

def differenceRow (k : ℕ) : Row := (powerRows k).1

private theorem power_rows_correct (k : ℕ) (y : ℝ) :
    y*eval (powerRows k).1 (y^2) = ((1+y)/2)^k-((1-y)/2)^k ∧
    y*eval (powerRows k).2 (y^2) = ((1+y)/2)^(k+1)-((1-y)/2)^(k+1) := by
  induction k with
  | zero => simp [powerRows]; ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    simp only [powerRows, eval_add, eval_linear]
    push_cast
    linear_combination ((y^2-1)/4)*ih.1 + ih.2

theorem difference_at_nat (k : ℕ) (y : ℝ) :
    difference (k:ℂ) y = ((y*eval (differenceRow k) (y^2) : ℝ) : ℂ) := by
  rw [differenceRow, (power_rows_correct k y).1]
  simp [difference]

abbrev NewtonTerms := List (ℕ × Row)

def timesTerms (a : ℚ) (cs : NewtonTerms) : NewtonTerms :=
  cs.map (fun p => (p.1, scale a p.2))

noncomputable def termsValue (cs : NewtonTerms) (s z : ℝ) : ℝ :=
  (cs.map (fun p => Ring.choose s p.1 * eval p.2 z)).sum

private theorem terms_times (a : ℚ) (cs : NewtonTerms) (s z : ℝ) :
    termsValue (timesTerms a cs) s z = a*termsValue cs s z := by
  induction cs with
  | nil => simp [termsValue, timesTerms]
  | cons p cs ih =>
    change Ring.choose s p.1 * eval (scale a p.2) z + termsValue (timesTerms a cs) s z = _
    rw [ih, eval_scale]
    change _ = a * (Ring.choose s p.1 * eval p.2 z + termsValue cs s z)
    ring

/-- Separate the remaining real power from the finite Newton expansion. -/
structure GapModel where
  power : ℚ
  terms : NewtonTerms

def startModel (h : ℕ) : GapModel :=
  ⟨if Even h then -2 else 0, (List.range h).map (fun k =>
    (k, scale ((-1 : ℚ)^(h-1-k)) (differenceRow k)))⟩

def integerTerms (k : ℕ) : NewtonTerms → Row
  | [] => []
  | (i,p) :: ps => add (scale (k.choose i) p) (integerTerms k ps)

def atInteger (M : GapModel) (k : ℕ) : Row :=
  add (scale M.power (differenceRow k)) (integerTerms k M.terms)

private theorem eval_integerTerms (k : ℕ) (cs : NewtonTerms) (z : ℝ) :
    eval (integerTerms k cs) z = termsValue cs k z := by
  induction cs with
  | nil => rfl
  | cons p cs ih =>
    rcases p with ⟨i,p⟩
    simp only [integerTerms, eval_add, eval_scale, ih, termsValue, List.map_cons, List.sum_cons,
      Ring.choose_natCast, Rat.cast_natCast]

private theorem eval_atInteger (M : GapModel) (k : ℕ) (z : ℝ) :
    eval (atInteger M k) z =
      M.power * eval (differenceRow k) z + termsValue M.terms k z := by
  simp [atInteger, eval_integerTerms]

def nextModel (M : GapModel) (k : ℕ) : GapModel :=
  ⟨-2 * M.power, timesTerms (-2) M.terms ++ [(k, atInteger M k)]⟩

def model (h : ℕ) : ℕ → GapModel
  | 0 => startModel h
  | r+1 => nextModel (model h r) (h+2*r+1)

private theorem terms_next (M : GapModel) (k : ℕ) (s z : ℝ) :
    termsValue (nextModel M k).terms s z =
      -2 * termsValue M.terms s z + Ring.choose s k * eval (atInteger M k) z := by
  simp only [nextModel, termsValue, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  change termsValue (timesTerms (-2) M.terms) s z + _ = _
  rw [terms_times]
  push_cast
  rfl

private theorem difference_real_cast {s y : ℝ} (hy : y ∈ Set.Icc 0 1) :
    difference (s : ℂ) y = ((difference (s:ℂ) y).re : ℂ) := by
  rw [difference_real_part hy, difference, Complex.ofReal_sub,
    Complex.ofReal_cpow (by linarith [hy.1] : 0 ≤ (1+y)/2),
    Complex.ofReal_cpow (by linarith [hy.2] : 0 ≤ (1-y)/2)]

private theorem sum_list_range {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

private theorem start_correct (h : ℕ) (hh : 1 ≤ h) (s y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    gapKernel [h] (s:ℂ) y = (((startModel h).power * (difference s y).re +
      y*termsValue (startModel h).terms s (y^2) : ℝ) : ℂ) := by
  let f (k : ℕ) := (-1:ℂ)^(h-1-k) * Ring.choose (s:ℂ) k * difference (k:ℂ) y
  have hzero : f 0 = 0 := by simp [f, difference]
  have hn : (∑ k ∈ Ico 1 h, f k) = ∑ k ∈ range h, f k := by
    rw [sum_Ico_eq_sub _ hh, sum_range_one, hzero, sub_zero]
  have hsum : (∑ k ∈ range h, f k) = (y:ℂ) * (termsValue (startModel h).terms s (y^2) : ℂ) := by
    simp only [startModel, termsValue, List.map_map, Function.comp_def, eval_scale,
      Rat.cast_pow, Rat.cast_neg, Rat.cast_one, sum_list_range, Complex.ofReal_sum, mul_sum]
    apply sum_congr rfl
    intro k _
    dsimp only [f]
    rw [difference_at_nat, ← Complex.ofReal_choose]
    push_cast
    ring
  have hpre : (if Even h then -2 * difference (s:ℂ) y else 0) =
      ((((startModel h).power : ℝ) : ℂ) * ((difference (s:ℂ) y).re : ℂ)) := by
    rw [← difference_real_cast hy]
    by_cases he : Even h <;> simp [startModel, he]
  simp only [gapKernel, applyGaps, gapStep, Nat.zero_add]
  change (if Even h then -2 * difference (s:ℂ) y else 0) + (∑ k ∈ Ico 1 h, f k) = _
  rw [hn, hsum, hpre]
  push_cast
  rfl

/-- This expansion evaluates the same kernel at the real argument and at every integer node. -/
theorem kernel_model (h r : ℕ) (hh : 1 ≤ h) (s y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    gapKernel (h :: List.replicate r 2) (s:ℂ) y =
      ((((model h r).power : ℝ) * (difference (s:ℂ) y).re +
        y*termsValue (model h r).terms s (y^2) : ℝ) : ℂ) := by
  induction r generalizing s with
  | zero => exact start_correct h hh s y hy
  | succ r ih =>
    let k := h+2*r+1
    have hk : 0+(h::List.replicate r 2).sum+1=k := by simp [k, List.sum_replicate]; omega
    have hstep : gapKernel (h :: List.replicate (r+1) 2) (s:ℂ) y =
        Ring.choose (s:ℂ) k * gapKernel (h::List.replicate r 2) (k:ℂ) y -
          2 * gapKernel (h::List.replicate r 2) s y := by
      rw [List.replicate_succ']
      change applyGaps ((h :: List.replicate r 2) ++ [2]) 0 (fun z => difference z y) s = _
      rw [applyGaps_append]
      simp only [applyGaps, gapStep_two]
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, hk]
      rfl
    have hi := ih (k:ℝ)
    rw [show ((k:ℝ):ℂ) = (k:ℂ) by simp, difference_at_nat] at hi
    simp only [Complex.ofReal_re] at hi
    rw [hstep, ih, hi]
    change _ = (((((nextModel (model h r) k).power:ℚ):ℝ) * _ +
      y*termsValue (nextModel (model h r) k).terms s (y^2) : ℝ):ℂ)
    rw [terms_next, eval_atInteger]
    simp only [nextModel, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat]
    rw [← Complex.ofReal_choose]
    push_cast
    ring

end BilleyFahrbachTalmageClassification.Square
