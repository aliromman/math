module

public import conjectures.BilleyFahrbachTalmageClassification.FourTwoExact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
namespace BilleyFahrbachTalmageClassification

private theorem testPoint_eq : (1+(5/2:ℂ)*Complex.I) = peakTestPoint := by
  apply Complex.ext <;> norm_num [peakTestPoint,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]

private theorem testPower_norm {t : ℝ} (ht : 0 ≤ t) : ‖(t:ℂ)^peakTestPoint‖ = t := by
  rw [Complex.norm_cpow_eq_rpow_re_of_nonneg ht (by norm_num [peakTestPoint])]
  exact Real.rpow_one t

private theorem half_decomposition {y : ℝ} (hy : y ∈ Set.Icc 0 (1/2)) :
    difference peakTestPoint y = ((1/2:ℝ):ℂ)^peakTestPoint *
      ((1+(y:ℂ))^peakTestPoint - (1-(y:ℂ))^peakTestPoint) := by
  obtain ⟨h0,h1⟩ := hy
  have hp (r : ℝ) (hr : 0 ≤ r) : ((r/2:ℝ):ℂ)^peakTestPoint =
      (((1/2:ℝ):ℂ)^peakTestPoint) * (r:ℂ)^peakTestPoint := by
    rw [←Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hr,
      ←Complex.ofReal_mul, show (1/2:ℝ)*r = r/2 by ring]
  rw [difference, hp (1+y) (by linarith), hp (1-y) (by linarith), mul_sub]
  push_cast
  rfl

private theorem error_low {y : ℝ} (hy : y ∈ Set.Icc 0 (1/2)) :
    ‖gapKernel [2,2,2,2] peakTestPoint y - (y:ℂ)*lowApprox (y^2)‖ ≤ y := by
  obtain ⟨h0,h1⟩ := hy
  let Y := (y:ℂ)
  let A := ((1/2:ℝ):ℂ)^peakTestPoint
  let B := truncTest 12 (-1/2)
  let U := (1+Y)^peakTestPoint
  let V := (1-Y)^peakTestPoint
  let T := truncTest 12 Y
  let W := truncTest 12 (-Y)
  have yn : ‖Y‖ = y := by simp [Y,abs_of_nonneg h0]
  have hn : ‖(-1/2:ℂ)‖ ≤ (1/2:ℝ) := by norm_num [norm_div]
  have hnt : ‖A-B‖ ≤ 1/512 := by
    convert truncTest_error 12 hn using 1 <;> norm_num [A,B,norm_div]
  have hB : ‖B‖ ≤ 1 := by
    have ha : ‖A‖ = 1/2 := testPower_norm (by norm_num)
    have hbb := norm_sub_le A (A-B)
    rw [sub_sub_cancel] at hbb
    linarith
  have h₁ : ‖U-T‖ ≤ 8*y^12 := by
    simpa only [U,T,yn] using truncTest_error 12 (x := Y) (by rw [yn]; exact h1)
  have h₂ : ‖V-W‖ ≤ 8*y^12 := by
    simpa only [V,W,sub_eq_add_neg,norm_neg,yn] using
      truncTest_error 12 (x := -Y) (by rw [norm_neg,yn]; exact h1)
  have hu1 : ‖U-1‖ ≤ 8*y := by
    simpa [truncTest,U,yn] using truncTest_error 1 (x := Y) (by rw [yn]; exact h1)
  have hv1 : ‖V-1‖ ≤ 8*y := by
    simpa [truncTest,V,sub_eq_add_neg,yn] using
      truncTest_error 1 (x := -Y) (by rw [norm_neg,yn]; exact h1)
  have huv : ‖U-V‖ ≤ 16*y := by
    have := norm_sub_le (U-1) (V-1)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  have htail : ‖(U-T)-(V-W)‖ ≤ 16*y^12 := by
    linarith [norm_sub_le (U-T) (V-W)]
  have hpow : y^12 ≤ y/2048 := by
    have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 11) h0
    norm_num at this
    rw [show (12:ℕ) = 11+1 by decide,pow_succ]
    linarith
  rw [fourTwo_formula,lowApprox_eq,half_decomposition ⟨h0,h1⟩]
  change ‖16*(A*(U-V)) + Y*fourCorrections (y^2) -
        (16*B*(T-W) + Y*fourCorrections (y^2))‖ ≤ y
  rw [show 16*(A*(U-V))+Y*fourCorrections (y^2)-(16*B*(T-W)+Y*fourCorrections (y^2)) =
     16*((A-B)*(U-V)+B*((U-T)-(V-W))) by ring, norm_mul]
  have hsum := norm_add_le ((A-B)*(U-V)) (B*((U-T)-(V-W)))
  rw [norm_mul,norm_mul] at hsum
  have hfirst := mul_le_mul hnt huv (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1/512)
  have hsecond := mul_le_mul hB htail (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  norm_num only [Complex.norm_ofNat]
  linarith

theorem fourTwo_bound_low {y : ℝ} (hy : y ∈ Set.Icc 0 (1/2)) :
    ‖gapKernel [2,2,2,2] (1+(5/2:ℂ)*Complex.I) y‖ ≤ 24*y := by
  rw [testPoint_eq]
  obtain ⟨h0,h1⟩ := hy
  have hi := lowApprox_bound (y^2) (sq_nonneg _) (by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)])
  have he := error_low ⟨h0,h1⟩
  have hn := norm_sub_le (gapKernel [2,2,2,2] peakTestPoint y - (y:ℂ)*lowApprox (y^2))
     (-((y:ℂ)*lowApprox (y^2)))
  rw [sub_neg_eq_add,sub_add_cancel,norm_neg,norm_mul,Complex.norm_real,Real.norm_of_nonneg h0] at hn
  linarith [mul_le_mul_of_nonneg_left hi h0]

theorem fourTwo_bound_high {y : ℝ} (hy : y ∈ Set.Icc (1/2) 1) :
    ‖gapKernel [2,2,2,2] (1+(5/2:ℂ)*Complex.I) y‖ ≤ 14*y := by
  rw [testPoint_eq]
  obtain ⟨h0,h1⟩ := hy
  let v := (1-y)/2
  have v0 : 0 ≤ v := by dsimp [v]; linarith
  have v1 : v ≤ 1/4 := by dsimp [v]; linarith
  have yv : 1-2*v = y := by dsimp [v]; ring
  have uv : (1+y)/2 = 1-v := by dsimp [v]; ring
  have hu := truncTest_error 6 (x := -(v:ℂ)) (by simp [abs_of_nonneg v0]; linarith)
  have ht : ‖(1-(v:ℂ))^peakTestPoint - truncTest 6 (-v)‖ ≤ 8*v^6 := by
    simpa [sub_eq_add_neg,abs_of_nonneg v0] using hu
  have hE : gapKernel [2,2,2,2] peakTestPoint y =
      16*((1-(v:ℂ))^peakTestPoint-truncTest 6 (-v) - (v:ℂ)^peakTestPoint) + highApprox v := by
    rw [fourTwo_formula, highApprox_eq,yv,difference,uv]
    push_cast
    rw [show ((1:ℂ)-(y:ℂ))/2 = (v:ℂ) by dsimp [v]; push_cast; rfl]
    ring
  have hp := pow_le_pow_left₀ v0 v1 6
  norm_num at hp
  have hi := highApprox_bound v v0 v1
  rw [hE]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hs := norm_sub_le ((1-(v:ℂ))^peakTestPoint-truncTest 6 (-v)) ((v:ℂ)^peakTestPoint)
  rw [testPower_norm v0] at hs
  norm_num only [Complex.norm_ofNat]
  linarith

end BilleyFahrbachTalmageClassification
