module

public import conjectures.BilleyFahrbachTalmageClassification.DensityFormula
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The peak recurrence after division by the prefix factorial -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial Finset PermutationPeaks PeakPolynomials

noncomputable def normalizedValue (c : ℕ) (S : Finset ℕ) (z : ℂ) : ℂ :=
  peakValue S ((c:ℂ)+z) / risingProduct (z+1) c

theorem normalized_prefix (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) {z : ℂ}
    (hz : 0 < z.re) :
    normalizedValue (maxPeak S) S z = ∫ y : ℝ in 0..1, (prefixDensity S y : ℂ) * difference z y := by
  rw [normalizedValue, density_formula S hS hne hz, mul_div_cancel_left₀]
  apply risingProduct_ne_zero
  simp
  linarith

theorem normalized_empty (z : ℂ) : normalizedValue 0 ∅ z = 1 := by
  simp [normalizedValue, peakValue, peakPolynomial_empty, risingProduct]

theorem peakValue_real (S : Finset ℕ) (x : ℝ) :
    peakValue S (x : ℂ) = ((peakPolynomial S).eval x : ℝ) := by
  exact aeval_algebraMap_apply_eq_algebraMap_eval x _

private theorem risingProduct_choose (z : ℂ) (c : ℕ) :
    risingProduct (z+1) c = c.factorial * Ring.choose (z+c) c := by
  rw [risingProduct_eq, Ring.multichoose_eq]
  congr 2
  ring

theorem absorb_choose (z : ℂ) (c j : ℕ) :
    risingProduct ((j:ℂ)+1) c * Ring.choose ((c:ℂ)+z) (c+j) =
      risingProduct (z+1) c * Ring.choose z j := by
  have h := Ring.choose_add_smul_choose z j c
  simp only [nsmul_eq_mul] at h
  rw [risingProduct_choose, risingProduct_choose, ← Nat.cast_add, Ring.choose_natCast,
    add_comm (c:ℂ) z, Nat.add_comm c j]
  linear_combination (c.factorial : ℂ)*h

theorem normalized_next (c a g : ℕ) (S : Finset ℕ) (hS : Admissible S)
    (ha : maxPeak S=c+a) (hg : 1 ≤ g) {z : ℂ} (hz : 0 < z.re) :
    normalizedValue c (insert (c+(a+g)+1) S) z =
      Ring.choose z (a+g)*normalizedValue c S (a+g) - 2*normalizedValue c S z -
      normalizedValue c (insert (c+(a+g)) S) z := by
  let j := a+g
  have h := extension_recurrence S hS ((c:ℂ)+z) (c+j) (by dsimp [j]; omega) (by dsimp [j]; omega)
  have hreal : (((peakPolynomial S).eval ((c+j:ℕ):ℝ):ℝ):ℂ) = peakValue S ((c:ℂ)+j) := by
    rw [← peakValue_real]
    push_cast
    rfl
  rw [hreal] at h
  rw [← Nat.cast_add (R:=ℂ) a g]
  change normalizedValue c (insert (c+j+1) S) z = Ring.choose z j * normalizedValue c S j -
    2*normalizedValue c S z - normalizedValue c (insert (c+j) S) z
  simp only [normalizedValue, h]
  have hf := absorb_choose z c j
  have hn : risingProduct (z+1) c ≠ 0 := risingProduct_ne_zero (by simp; linarith) _
  have hj : risingProduct ((j:ℂ)+1) c ≠ 0 := risingProduct_ne_zero (by simp; positivity) _
  field_simp [hn, hj]
  linear_combination (peakValue S ((c:ℂ)+j))*hf

theorem gapStep_succ (a g : ℕ) (hg : 1 ≤ g) (F : ℂ → ℂ) (s : ℂ) :
    gapStep a (g+1) F s = Ring.choose s (a+g) * F (a+g) - 2*F s - gapStep a g F s := by
  have hsum : ∑ j ∈ Ico (a+1) (a+g), (-1:ℂ)^(a+g-j) * Ring.choose s j * F j =
      -(∑ j ∈ Ico (a+1) (a+g), (-1:ℂ)^(a+g-1-j) * Ring.choose s j * F j) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    have hj' := (mem_Ico.mp hj).2
    rw [show a+g-j = (a+g-1-j)+1 by omega, pow_succ]
    ring
  simp only [gapStep, ← Nat.add_assoc a g 1, Nat.add_sub_cancel, Nat.even_add_one]
  rw [sum_Ico_succ_top (by omega : a+1 ≤ a+g), hsum]
  simp only [Nat.sub_self, pow_zero, one_mul, Nat.cast_add]
  by_cases he : Even g <;> simp [he] <;> ring

theorem normalized_gap (c a : ℕ) (S : Finset ℕ) (hS : Admissible S)
    (ha : maxPeak S=c+a) (g : ℕ) (hg : 1 ≤ g) {z : ℂ} (hz : 0 < z.re) :
    normalizedValue c (insert (c+(a+g)) S) z = gapStep a g (normalizedValue c S) z := by
  induction g, hg using Nat.le_induction with
  | base =>
    have he : c+(a+1) = maxPeak S+1 := by omega
    have hz0 : peakValue (insert (maxPeak S+1) S) ((c:ℂ)+z) = 0 := by
      by_cases hne : S.Nonempty
      · exact adjacent_extension_zero S hne _
      · have hs := not_nonempty_iff_eq_empty.mp hne
        subst S
        have hbad : ¬ Admissible ({1} : Finset ℕ) := fun h => by
          have hh := h.1 1 (by simp)
          omega
        simp [maxPeak, peakValue, peakPolynomial_inadmissible _ hbad]
    simp [normalizedValue, he, hz0, gapStep]
  | succ g hg ih =>
    rw [gapStep_succ a g hg, ← ih, show c+(a+(g+1))=c+(a+g)+1 by omega]
    exact normalized_next c a g S hS ha hg hz

/-- Append the gaps in increasing order along the permutation. -/
def extend (S : Finset ℕ) : List ℕ → Finset ℕ
  | [] => S
  | g::gs => extend (insert (maxPeak S+g) S) gs

theorem extend_admissible (S : Finset ℕ) (hS : Admissible S) (gs : List ℕ)
    (hg : ∀ g ∈ gs, 2 ≤ g) : Admissible (extend S gs) := by
  induction gs generalizing S with
  | nil => exact hS
  | cons g gs ih =>
    have h := hg g (by simp)
    apply ih _ (admissible_insert_above S hS _ (by omega)
      (fun i hi => by have := le_maxPeak hi; omega))
    intro j hj
    exact hg j (by simp [hj])

theorem extend_max (S : Finset ℕ) (gs : List ℕ) : maxPeak (extend S gs) = maxPeak S+gs.sum := by
  induction gs generalizing S with
  | nil => simp [extend]
  | cons g gs ih =>
    rw [extend, ih, max_insert (by omega : maxPeak S ≤ maxPeak S+g)]
    simp [Nat.add_assoc]

theorem applyGaps_congr (gs : List ℕ) (a : ℕ) {F G : ℂ → ℂ}
    (h : ∀ z : ℂ, 0 < z.re → F z = G z) {z : ℂ} (hz : 0 < z.re) :
    applyGaps gs a F z = applyGaps gs a G z := by
  induction gs generalizing a F G z with
  | nil => exact h _ hz
  | cons g gs ih =>
    apply ih (a+g) _ hz
    intro w hw
    simp only [gapStep, h w hw]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [h j (by simpa using (show 0 < (j:ℝ) by exact_mod_cast (show 0 < j by have := (mem_Ico.mp hj).1; omega)))]

theorem normalized_extend (c a : ℕ) (S : Finset ℕ) (hS : Admissible S) (ha : maxPeak S=c+a)
    (gs : List ℕ) (hg : ∀ g ∈ gs, 2 ≤ g) {z : ℂ} (hz : 0 < z.re) :
    normalizedValue c (extend S gs) z = applyGaps gs a (normalizedValue c S) z := by
  induction gs generalizing S a z with
  | nil => rfl
  | cons g gs ih =>
    have h2 := hg g (by simp)
    let T := insert (maxPeak S+g) S
    have hT : Admissible T := admissible_insert_above S hS _ (by omega)
      (fun i hi => by have := le_maxPeak hi; omega)
    have ht : maxPeak T = c+(a+g) := by dsimp [T]; rw [max_insert (by omega : maxPeak S ≤ _), ha]; omega
    change normalizedValue c (extend T gs) z = applyGaps gs (a+g) (gapStep a g (normalizedValue c S)) z
    rw [ih _ T hT ht (fun j hj => hg j (by simp [hj])) hz]
    apply applyGaps_congr _ _ _ hz
    intro w hw
    have he : maxPeak S+g=c+(a+g) := by omega
    simpa [T, he] using normalized_gap c a S hS ha g (by omega) hw

end BilleyFahrbachTalmageClassification
