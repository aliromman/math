module

public import conjectures.BilleyFahrbachTalmageClassification.SmallGapModel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Signs on the two unit intervals for each of the six small gaps -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification.Square

def sign (r : ℕ) : ℚ := (-1)^(r+1)

def termsMatrix (j : ℕ) (a : ℚ) : NewtonTerms → Rows
  | [] => []
  | (k,p) :: ps => addRows (tensor (scale a (chooseRow j k)) p) (termsMatrix j a ps)

private theorem termsMatrix_correct (j : ℕ) (a : ℚ) (cs : NewtonTerms) (x z : ℝ) :
    evalRows (termsMatrix j a cs) x z = a * termsValue cs ((j:ℝ)+x) z := by
  induction cs with
  | nil => simp [termsMatrix, termsValue]
  | cons p cs ih =>
    rcases p with ⟨k,p⟩
    rw [termsMatrix, evalRows_add, eval_tensor, eval_scale, eval_chooseRow, ih]
    change _ = a * (Ring.choose ((j:ℝ)+x) k * eval p z + termsValue cs ((j:ℝ)+x) z)
    ring

/-- Replace the power difference on this unit interval by its value at the right endpoint. -/
def certificate (h r j : ℕ) : Rows :=
  let M := model h r
  addRows [scale (sign r * M.power) (differenceRow (j+1))] (termsMatrix j (sign r) M.terms)

private theorem certificate_eval (h r j : ℕ) (x z : ℝ) :
    evalRows (certificate h r j) x z =
      (-1:ℝ)^(r+1) * ((model h r).power * eval (differenceRow (j+1)) z +
        termsValue (model h r).terms ((j:ℝ)+x) z) := by
  simp only [certificate, evalRows_add, evalRows_cons, eval_scale, Rat.cast_mul, evalRows_nil,
    mul_zero, add_zero, termsMatrix_correct, sign, Rat.cast_pow, Rat.cast_neg, Rat.cast_one]
  ring

private theorem power_sign (h r : ℕ) :
    0 ≤ (-1:ℝ)^(r+1) * ((model h r).power : ℝ) := by
  induction r with
  | zero =>
    by_cases hh : Even h <;> norm_num [model, startModel, hh]
  | succ r ih =>
    simp only [model, nextModel, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, pow_succ _ (r+1)]
    linarith

private theorem sign_of_certificate {h r j : ℕ} (hh : 1 ≤ h) (hj : 1 ≤ j)
    (cert : positiveRectangles [] (certificate h r j) = true) {s y : ℝ}
    (hs₀ : j ≤ s) (hs₁ : s ≤ j+1) (hy : y ∈ Set.Ioc 0 1) :
    0 < (-1:ℝ)^(r+1) * (gapKernel (h :: List.replicate r 2) (s:ℂ) y).re := by
  have hy₀ : y ∈ Set.Icc 0 1 := ⟨hy.1.le, hy.2⟩
  have hcert := rectangles_sound _ cert (s-j) (y^2) (by linarith) (by linarith)
    (sq_nonneg y) (by nlinarith only [mul_nonneg (sub_nonneg.mpr hy.2) (add_nonneg hy.1.le zero_le_one)])
  rw [certificate_eval, show (j:ℝ)+(s-j)=s by ring] at hcert
  have hd := difference_ge_next hj hs₀ hs₁ hy₀
  rw [difference_at_nat, Complex.ofReal_re] at hd
  have hlow := mul_le_mul_of_nonneg_left hd (power_sign h r)
  have hstrict := mul_pos hy.1 hcert
  rw [kernel_model h r hh s y hy₀, Complex.ofReal_re]
  nlinarith only [hstrict, hlow]

def rowChecks (h : ℕ) : Bool := (List.range 4).all fun r =>
  positiveRectangles [] (certificate h r (h-3)) && positiveRectangles [] (certificate h r (h-2))

private theorem all_rows {h : ℕ} (hh : 4 ≤ h) (hh' : h ≤ 9) : rowChecks h = true := by
  interval_cases h <;> decide +kernel

theorem sign_on_intervals {h r : ℕ} (hh : 4 ≤ h) (hh' : h ≤ 9) (hr : r ≤ 3)
    {s y : ℝ} (hs₀ : (h:ℝ)-3 ≤ s) (hs₁ : s ≤ (h:ℝ)-1) (hy : y ∈ Set.Ioc 0 1) :
    0 < (-1:ℝ)^(r+1) * (gapKernel (h :: List.replicate r 2) (s:ℂ) y).re := by
  have hc := all_rows hh hh'
  simp only [rowChecks, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
  obtain ⟨left, right⟩ := hc r (by omega)
  have hd₃ : ((h-3:ℕ):ℝ) = (h:ℝ)-3 := by rw [Nat.cast_sub (by omega : 3≤h)]; norm_num
  have hd₂ : ((h-2:ℕ):ℝ) = (h:ℝ)-2 := by rw [Nat.cast_sub (by omega : 2≤h)]; norm_num
  by_cases split : s ≤ (h:ℝ)-2
  · exact sign_of_certificate (by omega) (by omega) left (by rwa [hd₃]) (by rw [hd₃]; linarith) hy
  · exact sign_of_certificate (by omega) (by omega) right (by rw [hd₂]; linarith) (by rw [hd₂]; linarith) hy

end BilleyFahrbachTalmageClassification.Square

namespace BilleyFahrbachTalmageClassification

/-- Each gap from four through nine, followed by up to three gaps of size two,
has a fixed nonzero kernel sign throughout the two unit intervals. -/
theorem small_gap_sign {h r : ℕ} (hh : 4 ≤ h) (hh' : h ≤ 9) (hr : r ≤ 3)
    {s y : ℝ} (hs₀ : (h:ℝ)-3 ≤ s) (hs₁ : s ≤ (h:ℝ)-1) (hy : y ∈ Set.Ioc 0 1) :
    0 < (-1:ℝ)^(r+1) * (gapKernel (h :: List.replicate r 2) (s:ℂ) y).re :=
  Square.sign_on_intervals hh hh' hr hs₀ hs₁ hy

end BilleyFahrbachTalmageClassification
