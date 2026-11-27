module

public import conjectures.KolblSimplexRoots.Statement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

public noncomputable section
namespace KolblSimplexRoots
open Real

private def cis (a : ℝ) : ℂ := Complex.exp (a * Complex.I)
private def shift (r j : ℕ) : ℝ := r + 1/2 - j
private def factor (x y : ℝ) : ℂ := (y : ℂ) - x * Complex.I
private def block (D j : ℕ) (y : ℝ) : ℂ := ∏ i ∈ Finset.range D, factor (shift i j) y
private def phase (D j : ℕ) (t : ℝ) := ∑ i ∈ Finset.range D, arctan (shift i j * t)
private def radius (x y : ℝ) := y * √(1+(x/y)^2)
private def size (D j : ℕ) (y : ℝ) := ∏ i ∈ Finset.range D, radius (shift i j) y

private theorem polar (x y : ℝ) (hy : 0 < y) :
    factor x y = (radius x y : ℂ) * cis (-arctan (x/y)) := by
  have hr : 0 < √(1+(x/y)^2) := by positivity
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, cis, Complex.exp_ofReal_mul_I_re, Real.cos_neg, Real.cos_arctan]
    simp only [factor, Complex.sub_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, sub_zero,
      Complex.ofReal_re, radius]
    field_simp
  · rw [Complex.im_ofReal_mul, cis, Complex.exp_ofReal_mul_I_im, Real.sin_neg, Real.sin_arctan]
    simp only [factor, Complex.sub_im, Complex.mul_I_im, Complex.ofReal_im, Complex.ofReal_re,
      zero_sub, radius]
    field_simp

private theorem block_polar (D j : ℕ) (y : ℝ) (hy : 0 < y) :
    block D j y = (size D j y : ℂ) * cis (-phase D j (1/y)) := by
  unfold block size cis phase
  rw [← Finset.sum_neg_distrib]
  push_cast
  rw [Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simpa [cis, div_eq_mul_inv] using polar (shift i j) y hy

private theorem size_pos (D j : ℕ) {y : ℝ} (hy : 0 < y) : 0 < size D j y := by
  unfold size radius
  exact Finset.prod_pos fun _ _ => by positivity

private theorem basis_block (D j : ℕ) (y : ℝ) :
    basis D j ⟨-1/2,y⟩ = Complex.I^D * block D j y := by
  unfold basis block
  rw [show Complex.I^D = ∏ _i ∈ Finset.range D, Complex.I by simp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr (by simp)
  intro i _
  apply Complex.ext <;> simp [factor, shift, Complex.mul_re, Complex.mul_im]; ring

private theorem phase_mono (D : ℕ) {j k : ℕ} (h : j ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    phase D k t ≤ phase D j t := by
  unfold phase shift
  apply Finset.sum_le_sum
  intro i _
  gcongr

private theorem phase_reflect {D j : ℕ} (hj : j ≤ D) (t : ℝ) :
    phase D (D-j) t = -phase D j t := by
  unfold phase
  rw [← Finset.sum_range_reflect (fun i => arctan (shift i (D-j)*t)) D, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [show shift (D-1-i) (D-j) = -shift i j by unfold shift; push_cast [Nat.cast_sub (by omega : i ≤ D-1), Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_sub hj]; ring,
    neg_mul, arctan_neg]

private theorem phase_pos (D : ℕ) (hD : 0 < D) {t : ℝ} (ht : 0 < t) : 0 < phase D 0 t := by
  unfold phase shift
  simp only [Nat.cast_zero, sub_zero]
  apply Finset.sum_pos
  · intro i _
    apply Real.arctan_pos.mpr; positivity
  · exact ⟨0, Finset.mem_range.mpr hD⟩

private theorem phase_strict (D : ℕ) (hD : 0 < D) : StrictMono (phase D 0) := by
  intro a b hab
  unfold phase shift
  simp only [Nat.cast_zero, sub_zero]
  apply Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hD⟩
  intro i _
  gcongr

private def projection (D j : ℕ) (y : ℝ) : ℝ := (Complex.I * block D j y).re

private theorem projection_formula (D j : ℕ) {y : ℝ} (hy : 0 < y) :
    projection D j y = size D j y * sin (phase D j (1/y)) := by
  rw [projection, block_polar _ _ _ hy, mul_left_comm, Complex.re_ofReal_mul,
    Complex.I_mul_re, cis, Complex.exp_ofReal_mul_I_im, Real.sin_neg, neg_neg]

private theorem projection_sign {D j : ℕ} (hj : j ≤ D) {y : ℝ} (hy : 0 < y)
    (hπ : phase D 0 (1/y) < π) :
    (2*j ≤ D → 0 ≤ projection D j y) ∧ (D ≤ 2*j → projection D j y ≤ 0) := by
  have hr := phase_reflect hj (1/y)
  have ht : 0 ≤ 1/y := by positivity
  have upper := phase_mono D (Nat.zero_le j) ht
  have lower := phase_mono D hj ht
  have hr0 := phase_reflect (j:=0) (Nat.zero_le D) (1/y)
  simp only [Nat.sub_zero] at hr0
  rw [projection_formula _ _ hy]
  constructor
  · intro h
    have hm := phase_mono D (show j ≤ D-j by omega) ht
    exact mul_nonneg (size_pos _ _ hy).le (Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)
  · intro h
    have hm := phase_mono D (show D-j ≤ j by omega) ht
    exact mul_nonpos_of_nonneg_of_nonpos (size_pos _ _ hy).le (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith))

private theorem projection_zero_pos {D : ℕ} (hD : 0 < D) {y : ℝ} (hy : 0 < y)
    (ht : phase D 0 (1/y) < π) : 0 < projection D 0 y := by
  rw [projection_formula _ _ hy]
  exact mul_pos (size_pos _ _ hy) (Real.sin_pos_of_pos_of_lt_pi (phase_pos _ hD (by positivity)) ht)

/-- Pascal's difference identity after rotation of all factors by `-I`. -/
private theorem block_diff (d j : ℕ) (y : ℝ) :
    Complex.I * block (d+1) j y - Complex.I * block (d+1) (j+1) y =
      (d+1:ℂ) * block d j y := by
  have left : block (d+1) j y = block d j y * factor (shift d j) y := by
    simp [block, Finset.prod_range_succ]
  have right : block (d+1) (j+1) y = block d j y * factor (shift 0 (j+1)) y := by
    unfold block
    rw [Finset.prod_range_succ']
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    congr 1; unfold shift; push_cast; ring
  rw [left,right]
  have e : Complex.I * (factor (shift d j) y - factor (shift 0 (j+1)) y) = (d+1:ℂ) := by
    apply Complex.ext <;> simp [factor, shift, Complex.mul_re, Complex.mul_im]; ring
  linear_combination (norm := ring) block d j y * e

private theorem abel_sum {R : Type*} [CommRing R] (n : ℕ) (a b : ℕ → R) :
    ∑ j ∈ Finset.range (n+1), a j * (b j - b (j+1)) =
      a 0*b 0 + ∑ j ∈ Finset.range n, (a (j+1)-a j)*b (j+1) - a n*b (n+1) := by
  induction n with
  | zero => simp; ring
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (n:=n)]; ring

private def weighted (d : ℕ) (h : ℕ → ℕ) (y : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (d+1), (h j : ℂ)*block d j y

private theorem at_center (d : ℕ) (h : ℕ → ℕ) (y : ℝ) :
    ehrhart d h ⟨-1/2,y⟩ = Complex.I^d * weighted d h y / d.factorial := by
  unfold ehrhart weighted
  simp_rw [basis_block]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem weighted_proj (d : ℕ) (h : ℕ → ℕ) (y : ℝ) :
    (d+1:ℝ)*(weighted d h y).re = (h 0:ℝ)*projection (d+1) 0 y +
      ∑ j ∈ Finset.range d, ((h (j+1):ℝ)-h j)*projection (d+1) (j+1) y -
      (h d:ℝ)*projection (d+1) (d+1) y := by
  rw [← abel_sum d (fun j => (h j:ℝ)) (fun j => projection (d+1) j y)]
  unfold weighted
  rw [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have e := congrArg Complex.re (block_diff d j y)
  rw [Complex.sub_re, show (d+1:ℂ) = ((d+1:ℝ):ℂ) by push_cast; rfl, Complex.re_ofReal_mul] at e
  rw [show (h j:ℂ) = ((h j:ℝ):ℂ) by simp, Complex.re_ofReal_mul]
  unfold projection
  rw [e]; ring

private theorem root_phase {d : ℕ} {h : ℕ → ℕ} (hh : 0 < h 0) (hu : Unimodal d h)
    {y : ℝ} (hy : 0 < y) (hr : ehrhart d h ⟨-1/2,y⟩ = 0) : π ≤ phase (d+1) 0 (1/y) := by
  by_contra! hπ
  have pos := projection_zero_pos (D:=d+1) (by omega) hy hπ
  have endneg := (projection_sign (D:=d+1) le_rfl hy hπ).2 (by omega)
  have middle : 0 ≤ ∑ j ∈ Finset.range d, ((h (j+1):ℝ)-h j)*projection (d+1) (j+1) y := by
    apply Finset.sum_nonneg
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have sign := projection_sign (show j+1≤d+1 by omega) hy hπ
    by_cases hm : j < d/2
    · exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hu.1 j hm)) (sign.1 (by omega))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hu.2 j (by omega) hj')) (sign.2 (by omega))
  have first := mul_pos (show 0 < (h 0:ℝ) by exact_mod_cast hh) pos
  have last := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α:=ℝ) (h d)) endneg
  rw [at_center, div_eq_zero_iff] at hr
  have bz : weighted d h y = 0 := (mul_eq_zero.mp (hr.resolve_right (by exact_mod_cast Nat.factorial_ne_zero d))).resolve_left (pow_ne_zero _ Complex.I_ne_zero)
  have eq := weighted_proj d h y
  rw [bz, Complex.zero_re, mul_zero] at eq
  linarith

private theorem threshold (d : ℕ) (hd : 2 ≤ d) : ∃ v, 0 < v ∧ phase (d+1) 0 v = π := by
  have h0 : phase (d+1) 0 0 = 0 := by simp [phase]
  have h4 : π ≤ phase (d+1) 0 4 := by
    have step (n : ℕ) : phase n 0 4 ≤ phase (n+1) 0 4 := by
      simp only [phase, Finset.sum_range_succ, le_add_iff_nonneg_right, shift, Nat.cast_zero, sub_zero]
      positivity
    have ha : π/3 ≤ arctan 2 := by
      rw [← Real.arctan_sqrt_three]
      apply Real.arctan_mono
      exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    have base : π ≤ phase 3 0 4 := by
      have h6 := Real.arctan_mono (by norm_num : (2:ℝ)≤6)
      have h10 := Real.arctan_mono (by norm_num : (2:ℝ)≤10)
      norm_num [phase, shift, Finset.sum_range_succ]; linarith
    exact base.trans (monotone_nat_of_le_succ step (by omega))
  have hc : Continuous (phase (d+1) 0) := by unfold phase; fun_prop
  obtain ⟨v,hv,h⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 4 by norm_num) hc.continuousOn
    (show π ∈ Set.Icc (phase (d+1) 0 0) (phase (d+1) 0 4) from ⟨by rw [h0]; exact pi_pos.le,h4⟩)
  exact ⟨v,lt_of_le_of_ne hv.1 (by rintro rfl; linarith [pi_pos]),h⟩

private theorem block_reflect (D : ℕ) (y : ℝ) : block D D y = star (block D 0 y) := by
  unfold block
  rw [← Finset.prod_range_reflect (fun i => factor (shift i D) y) D]
  simp only [star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have hlt := Finset.mem_range.mp hi
  have hshift : shift (D-1-i) D = -shift i 0 := by
    unfold shift
    push_cast [Nat.cast_sub (by omega : i≤D-1), Nat.cast_sub (by omega : 1≤D)]
    ring
  rw [hshift]
  simp [factor]

private theorem simplex_root (d : ℕ) {v : ℝ} (hv : 0 < v) (hπ : phase (d+1) 0 v = π) :
    ehrhart d (fun _ => 1) ⟨-1/2,1/v⟩ = 0 := by
  let y := 1/v
  have hy : 0 < y := by dsimp [y]; positivity
  have e : block (d+1) (d+1) y = block (d+1) 0 y := by
    rw [block_reflect, block_polar _ _ _ hy]
    have hp : phase (d+1) 0 (1/y) = π := by simpa [y] using hπ
    rw [hp]
    have hc : cis (-π) = -1 := by simp [cis, Complex.exp_neg, Complex.exp_pi_mul_I]
    rw [hc]; simp
  have eq := abel_sum (R:=ℂ) d (fun _ => 1) (fun j => Complex.I * block (d+1) j y)
  simp only [one_mul, sub_self, zero_mul, Finset.sum_const_zero, add_zero, block_diff, e] at eq
  rw [← Finset.mul_sum] at eq
  have num : weighted d (fun _ => 1) y = 0 := by
    simpa [weighted] using (mul_eq_zero.mp eq).resolve_left (by exact_mod_cast (show d+1≠0 by omega))
  rw [at_center]; change Complex.I^d * weighted d (fun _ => 1) y / _ = 0
  rw [num, mul_zero, zero_div]

private theorem ehrhart_conj (d : ℕ) (h : ℕ → ℕ) (z : ℂ) :
    ehrhart d h (star z) = star (ehrhart d h z) := by simp [ehrhart,basis]

private theorem segment_at_height {z : ℂ} {y : ℝ} (hy : 0 < y) (hre : z.re = -1/2)
    (h : |z.im| ≤ y) : z ∈ segment ℝ (⟨-1/2,-y⟩ : ℂ) ⟨-1/2,y⟩ := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  refine ⟨(y-z.im)/(2*y),(y+z.im)/(2*y),by positivity,by apply div_nonneg <;> linarith,by field_simp; ring,?_⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul, hre]
    field_simp; ring
  · simp only [Complex.add_im, Complex.real_smul, Complex.im_ofReal_mul]
    field_simp; ring

/-- The bound holds for every nonnegative centered-unimodal coefficient sequence
with positive constant coefficient, including sequences that are not palindromic. -/
theorem coefficient_bound (d : ℕ) (h : ℕ → ℕ) (h0 : 0 < h 0) (hu : Unimodal d h) :
    clSpan (ehrhart d h) ⊆ clSpan (ehrhart d (fun _ => 1)) := by
  apply convexHull_min _ (convex_convexHull _ _)
  rintro z ⟨hre,hz⟩
  by_cases hd : 2 ≤ d
  · obtain ⟨v,hv,hπ⟩ := threshold d hd
    let y := 1/v
    have hy : 0 < y := by dsimp [y]; positivity
    have root := simplex_root d hv hπ
    have negroot := ehrhart_conj d (fun _ => 1) ⟨-1/2,y⟩
    have hnegroot : ehrhart d (fun _ => 1) ⟨-1/2,-y⟩ = 0 := by
      rw [root,star_zero] at negroot
      exact negroot
    have rootset : (⟨-1/2,y⟩ : ℂ) ∈ {w : ℂ | w.re = -1/2 ∧ ehrhart d (fun _ => 1) w = 0} := ⟨rfl,root⟩
    apply segment_subset_convexHull (s:={w : ℂ | w.re = -1/2 ∧ ehrhart d (fun _ => 1) w = 0})
      (show ⟨-1/2,-y⟩ ∈ _ from ⟨rfl,hnegroot⟩) rootset
    apply segment_at_height hy hre
    have bound (t : ℝ) (ht : 0<t) (hroot : ehrhart d h ⟨-1/2,t⟩=0) : t ≤ y := by
      have e := root_phase h0 hu ht hroot
      rw [← hπ] at e
      have a := (phase_strict (d+1) (by omega)).le_iff_le.mp e
      exact (le_div_iff₀ hv).mpr (by simpa [mul_comm] using (le_div_iff₀ ht).mp a)
    obtain ⟨x,t⟩ := z
    change x = -1/2 at hre; subst x
    change |t| ≤ y
    rcases lt_trichotomy 0 t with hp | he | hn
    · rw [abs_of_pos hp]; exact bound t hp hz
    · rw [← he, abs_zero]; exact hy.le
    · have conjroot := ehrhart_conj d h ⟨-1/2,t⟩
      rw [hz,star_zero] at conjroot
      rw [abs_of_neg hn]
      exact bound (-t) (by linarith) conjroot
  · interval_cases d
    · simp [ehrhart,basis,h0.ne'] at hz
    · have im := congrArg Complex.im hz
      simp [ehrhart,basis,Finset.sum_range_succ,Complex.add_im] at im
      have hh : (0:ℝ) < h 0 + h 1 := by exact_mod_cast (show 0<h 0+h 1 by omega)
      have e : ((h 0:ℝ)+h 1)*z.im=0 := by linarith
      have him := (mul_eq_zero.mp e).resolve_left hh.ne'
      have he : z = ⟨-1/2,0⟩ := Complex.ext hre him
      apply subset_convexHull
      refine ⟨hre,?_⟩
      rw [he]
      norm_num [ehrhart,basis,Finset.sum_range_succ,Complex.ext_iff]

/-- Kölbl's inclusion for the lattice-point enumerators of reflexive polytopes. -/
theorem result : Conjecture := by
  intro d P _ h hh hu
  have e := hh 0
  have single : (∑ j ∈ Finset.range (d+1), h j * (0+d-j).choose d) = h 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hne
      have lt := Finset.mem_range.mp hj
      rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
    · simp
  rw [single] at e
  simp only [latticeCount, ite_true] at e
  exact coefficient_bound d h (by omega) hu

/-- info: 'KolblSimplexRoots.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

end KolblSimplexRoots
