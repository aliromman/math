module

public import conjectures.McCuneSeatJumps.Cells
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

open Finset MeasureTheory
namespace McCuneSeatJumps

private theorem gap {h k : ℕ} (hh : 0 < h) {p : Shares} {a b : Seats}
    (ha : Inside p h a) (hb : Inside p (h+k) b) (loss : ∃ i, b i < a i) :
    ∃ j, (k : ℤ) < (h:ℤ)*b j - ((h+k:ℕ):ℤ)*a j ∧
         (h:ℤ)*b j - ((h+k:ℕ):ℤ)*a j < h := by
  obtain ⟨i,hi⟩ := loss
  let D (j : Fin 3) : ℤ := (h:ℤ)*b j - ((h+k:ℕ):ℤ)*a j
  have sumD : ∑ j, D j = 0 := by
    simp [D,sum_sub_distrib,← mul_sum,← Nat.cast_sum, ha.1,hb.1,mul_comm]
  have newlt : (b i:ℤ)+1 ≤ a i := by exact_mod_cast hi
  have apos : 1 ≤ (a i:ℤ) := by omega
  have Di : D i ≤ -(h:ℤ)-k := by
    change (h:ℤ)*b i - ((h+k:ℕ):ℤ)*a i ≤ _
    push_cast
    nlinarith [mul_nonneg (by positivity : (0:ℤ) ≤ h) (sub_nonneg.mpr newlt),
      mul_nonneg (by positivity : (0:ℤ) ≤ k) (sub_nonneg.mpr apos)]
  have delta (r : Fin 3) : (D r:ℝ) =
      ((h+k:ℕ):ℝ)*err p h a r - h*err p (h+k) b r := by
    dsimp [D,err]; push_cast; ring
  have upper (j : Fin 3) : D j < (h:ℤ) := by
    have a' := mul_lt_mul_of_pos_left (ha.2 j i) (show (0:ℝ) < (h+k:ℕ) by positivity)
    have b' := mul_lt_mul_of_pos_left (hb.2 i j) (show (0:ℝ) < h by positivity)
    have eq : (D j:ℝ)-(D i:ℝ) < h+(h+k:ℕ) := by rw [delta,delta]; linarith only [a',b']
    have eq' : D j-D i < (h:ℤ)+(h+k:ℕ) := by exact_mod_cast eq
    omega
  have ex : ∃ j, (k:ℤ) < D j := by
    rw [Fin.sum_univ_three] at sumD
    fin_cases i
    · change D 0 ≤ -(h:ℤ)-k at Di
      exact ⟨1,by linarith only [sumD,Di,upper 2]⟩
    · change D 1 ≤ -(h:ℤ)-k at Di
      exact ⟨2,by linarith only [sumD,Di,upper 0]⟩
    · change D 2 ≤ -(h:ℤ)-k at Di
      exact ⟨0,by linarith only [sumD,Di,upper 1]⟩
  obtain ⟨j,hj⟩ := ex
  exact ⟨j,hj,upper j⟩

private theorem arithmetic_obstruction {h k : ℕ} {a b : Seats} {j : Fin 3}
    (lo : (k : ℤ) < (h:ℤ)*b j - ((h+k:ℕ):ℤ)*a j)
    (up : (h:ℤ)*b j - ((h+k:ℕ):ℤ)*a j < h) : k < h ∧ ¬ h-k ∣ h := by
  have kh : k < h := by omega
  refine ⟨kh,?_⟩
  intro dv
  let r : ℤ := h-k
  have dvh : r ∣ (h:ℤ) := by
    have t : ((h-k:ℕ):ℤ) ∣ (h:ℤ) := by exact_mod_cast dv
    simpa [r,Nat.cast_sub kh.le] using t
  have dvk : r ∣ (k:ℤ) := by
    convert dvd_sub dvh (dvd_refl r) using 1
    dsimp [r]; ring
  have dvM : r ∣ ((h+k:ℕ):ℤ) := by simpa using dvd_add dvh dvk
  let d : ℤ := (h:ℤ)*b j - ((h+k:ℕ):ℤ)*a j
  change (k:ℤ) < d at lo
  change d < (h:ℤ) at up
  have dvdD : r ∣ d := dvd_sub (dvd_mul_of_dvd_left dvh _) (dvd_mul_of_dvd_left dvM _)
  have zero := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ (h:ℤ)-d by omega)
    (show (h:ℤ)-d < r by change _ < (h:ℤ)-k; omega) (dvd_sub dvh dvdD)
  omega

public theorem necessary {h k : ℕ} (hh : 0 < h) (hp : 0 < probability h k) :
    k < h ∧ ¬ h-k ∣ h := by
  by_contra hn
  have z : volume (loss h k) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_inside hh, ae_inside (show 0 < h+k by omega)] with x old new
    rintro ⟨_,a,b,ha,hb,hi⟩
    obtain ⟨j,lo,up⟩ := gap hh (old a ha) (new b hb) hi
    exact hn (arithmetic_obstruction lo up)
  simp [probability,z] at hp

end McCuneSeatJumps
