module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The corrections from successive gaps of length two

At the next positive integer the recurrence bounds the new coefficient
by a binomial multiple of its predecessor. This cancels the factorial
denominator in the binomial basis at a real argument. -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Finset

private def factorialRatio (h k : ℕ) : ℝ := ∏ i ∈ range k, ((h:ℝ)+i+1)

private theorem factorialRatio_step (h k : ℕ) :
    factorialRatio h (k+1) = factorialRatio h k * ((h:ℝ)+k+1) := prod_range_succ _ _

private theorem coefficient_growth (h : ℕ) (D : ℝ) (C : ℕ → ℝ)
    (hc : C 0 ≤ ((h:ℝ)+1)*D)
    (hstep : ∀ j, 2*C (j+1) ≤ ((h:ℝ)+2*j+3)*((h:ℝ)+2*j+2)*C j) (j : ℕ) :
    2^j*C j ≤ factorialRatio h (2*j+1)*D := by
  induction j with
  | zero => simpa [factorialRatio] using hc
  | succ j ih =>
    have hi := hstep j
    have hn : 0 ≤ ((h:ℝ)+2*j+3)*((h:ℝ)+2*j+2) := by positivity
    have hh := mul_le_mul_of_nonneg_left ih hn
    have hk := mul_le_mul_of_nonneg_left hi (show 0 ≤ (2:ℝ)^j by positivity)
    rw [show 2*(j+1)+1=2*j+1+1+1 by omega, factorialRatio_step, factorialRatio_step, pow_succ]
    push_cast
    nlinarith only [hh,hk]

private theorem choose_ratio (h k : ℕ) (s : ℝ) (hs : s ≤ h) :
    |Ring.choose s (h+k)| * factorialRatio h k =
      |Ring.choose s h| * ∏ i ∈ range k, ((h:ℝ)-s+i) := by
  induction k with
  | zero => simp [factorialRatio]
  | succ k ih =>
    have hc : ((h:ℝ)+k+1) * Ring.choose s (h+k+1) =
        Ring.choose s (h+k)*(s-((h:ℝ)+k)) := by
      simpa [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_add] using
        Ring.choose_smul_choose s (Nat.le_succ (h+k))
    have ha := congrArg abs hc
    simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (h:ℝ)+k+1),
      abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) k] : s-((h:ℝ)+k) ≤ 0)] at ha
    rw [Nat.add_succ, factorialRatio_step, prod_range_succ]
    calc
      _ = (((h:ℝ)+k+1)*|Ring.choose s (h+k+1)|)*factorialRatio h k := by ring
      _ = _ := by rw [ha, ← mul_assoc, ← ih]; ring

private theorem choose_origin (h : ℕ) (hh : 2 ≤ h) (s : ℝ) (hs : 1 ≤ s) :
    (h:ℝ)*((h:ℝ)-1)*|Ring.choose s h| =
      s*(s-1)*|Ring.choose (s-2) (h-2)| := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hh
  have first (x : ℝ) (k : ℕ) :
      (k+1:ℝ)*Ring.choose x (k+1) = x*Ring.choose (x-1) k := by
    simpa [Nat.choose_one_right,nsmul_eq_mul] using
      Ring.choose_smul_choose x (n:=k+1) (k:=1) (by omega)
  have h₁ := congrArg abs (first s (m+1))
  have h₂ := congrArg abs (first (s-1) m)
  simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((m+1:ℕ):ℝ)+1),
    abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)+1), abs_of_nonneg (by linarith : 0 ≤ s),
    abs_of_nonneg (by linarith : 0 ≤ s-1), show s-1-1=s-2 by ring] at h₁ h₂
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at *
  linear_combination ((m:ℝ)+1)*h₁ + s*h₂

private theorem choose_prefix_bound (h : ℕ) (hh : 2 ≤ h) (s D Dh : ℝ)
    (hs : 1 ≤ s) (hs' : s ≤ h) (hD : 0 ≤ D) (hDh : s*Dh ≤ (h:ℝ)*D) :
    |Ring.choose s h| *Dh ≤ |Ring.choose (s-2) (h-2)| *D := by
  have hv := choose_origin h hh s hs
  have hm : 0 < (h:ℝ) := by exact_mod_cast (by omega : 0 < h)
  have hm' : 0 < (h:ℝ)-1 := sub_pos.mpr (by exact_mod_cast (show 1 < h by omega))
  have hb := mul_le_mul_of_nonneg_left hDh (abs_nonneg (Ring.choose s h))
  apply le_of_mul_le_mul_left (a := s*((h:ℝ)-1)) _ (by positivity)
  calc
    _ ≤ ((h:ℝ)*((h:ℝ)-1)*|Ring.choose s h|)*D := by
      nlinarith only [mul_le_mul_of_nonneg_left hb hm'.le]
    _ = s*(s-1)*|Ring.choose (s-2) (h-2)| *D := by rw [hv]
    _ ≤ _ := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hs')
        (mul_nonneg (mul_nonneg (by linarith : 0≤s) (abs_nonneg (Ring.choose (s-2) (h-2)))) hD)]

/-- An absolute error for the first long gap and bounds at three later integer
nodes give the sign at the same real argument after up to three short gaps. -/
theorem correction_sign (h r : ℕ) (s D Dh : ℝ) (C H : ℕ → ℝ)
    (hh : 2 ≤ h) (hs : 1 ≤ s) (hs' : s ≤ h) (hD : 0 < D) (hDh : s*Dh ≤ (h:ℝ)*D)
    (hcpos : ∀ i, 0 ≤ C i) (hc : C 0 ≤ ((h:ℝ)+1)*Dh)
    (hstep : ∀ j, 2*C (j+1) ≤ ((h:ℝ)+2*j+3)*((h:ℝ)+2*j+2)*C j)
    (hzero : |H 0+D| ≤ |Ring.choose (s-2) (h-2)| *D)
    (hnext : ∀ i, H (i+1) = Ring.choose s (h+2*i+1)*C i - 2*H i)
    (henv : |Ring.choose (s-2) (h-2)| * (1+∑ i ∈ range r,
      (∏ k ∈ range (2*i+1), ((h:ℝ)-s+k))/(2*4^i)) < 1) :
    0 < (-1:ℝ)^(r+1)*H r := by
  let B := |Ring.choose (s-2) (h-2)|
  let t (i : ℕ) := (∏ k ∈ range (2*i+1), ((h:ℝ)-s+k))/(2*4^i)
  have ht (i : ℕ) : 0 ≤ ∏ k ∈ range (2*i+1), ((h:ℝ)-s+k) :=
    prod_nonneg fun _ _ => by positivity [sub_nonneg.mpr hs']
  have hcor (i : ℕ) : |Ring.choose s (h+2*i+1)*C i| /2^(i+1) ≤ B*D*t i := by
    have hg := coefficient_growth h Dh C hc hstep i
    have hu := mul_le_mul_of_nonneg_left hg (abs_nonneg (Ring.choose s (h+2*i+1)))
    have hb := mul_le_mul_of_nonneg_right (choose_prefix_bound h hh s D Dh hs hs' hD.le hDh) (ht i)
    have hi := choose_ratio h (2*i+1) s hs'
    rw [← Nat.add_assoc] at hi
    have hprod : (2:ℝ)^i*(|Ring.choose s (h+2*i+1)| * C i) ≤
        B*D*(∏ k ∈ range (2*i+1), ((h:ℝ)-s+k)) := by
      calc
        _ = |Ring.choose s (h+2*i+1)| * (2^i*C i) := by ring
        _ ≤ _ := hu
        _ = |Ring.choose s h| * Dh * (∏ k ∈ range (2*i+1), ((h:ℝ)-s+k)) := by
          rw [← mul_assoc, hi]; ring
        _ ≤ _ := hb
    rw [abs_mul, abs_of_nonneg (hcpos i)]
    dsimp only [t]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have he : (2:ℝ)*4^i = 2^i*2^(i+1) := by
      rw [show (4:ℝ)=2*2 by norm_num, mul_pow, pow_succ]; ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_right hprod (show 0 ≤ (2:ℝ)^(i+1) by positivity)]
  have hsum (j : ℕ) : |(-1:ℝ)^j*H j/2^j+D| ≤ B*D*(1+∑ i ∈ range j,t i) := by
    induction j with
    | zero => simpa [B] using hzero
    | succ j ih =>
      have he :
          (-1:ℝ)^(j+1)*H (j+1)/2^(j+1)+D =
          ((-1:ℝ)^j*H j/2^j+D) +
            (-1:ℝ)^(j+1)*(Ring.choose s (h+2*j+1)*C j)/2^(j+1) := by
        rw [hnext, pow_succ, pow_succ]; ring
      have ha := abs_add_le ((-1:ℝ)^j*H j/2^j+D)
        ((-1:ℝ)^(j+1)*(Ring.choose s (h+2*j+1)*C j)/2^(j+1))
      rw [he, sum_range_succ]
      rw [abs_div, abs_mul ((-1:ℝ)^(j+1)), abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (by positivity : 0 < (2:ℝ)^(j+1))] at ha
      linarith [hcor j]
  have hu : B*(1+∑ i ∈ range r,t i) < 1 := henv
  have hv := (le_abs_self _).trans (hsum r)
  have hn : (-1:ℝ)^r*H r/2^r < 0 := by nlinarith only [hv, mul_lt_mul_of_pos_right hu hD]
  have hneg := (div_lt_iff₀ (by positivity : 0 < (2:ℝ)^r)).mp hn
  rw [pow_succ]
  linarith

end BilleyFahrbachTalmageClassification
