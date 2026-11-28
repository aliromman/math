module

public import conjectures.BilleyFahrbachTalmageClassification.IntegerKernels
public import conjectures.BilleyFahrbachTalmageClassification.PeakRoots
public import conjectures.BilleyFahrbachTalmageClassification.PrefixRatio
public import conjectures.BilleyFahrbachTalmageClassification.RealRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Removing the prescribed roots before applying the midpoint inequality -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification
open Polynomial PermutationPeaks PeakPolynomials

private theorem quotient_midpoint (P Q : ℝ[X]) (hP : P.Splits) (hQ : Q ∣ P) (x : ℝ)
    (hn : ∀ t ∈ Set.Icc (x-1) (x+1), P.eval t ≠ 0) :
    Q.eval x ^ 2 * (|P.eval (x-1)| * |P.eval (x+1)|) ≤
      |Q.eval (x-1)| * |Q.eval (x+1)| * (P.eval x)^2 := by
  obtain ⟨V,hV⟩ := hQ
  have hp : P ≠ 0 := by
    intro hzero
    exact hn x ⟨by linarith,by linarith⟩ (by rw [hzero]; simp)
  have hv := hP.of_dvd hp (hV ▸ dvd_mul_left ..)
  have hm := eval_midpoint V hv x (fun t ht h => hn t ht (by rw [hV,eval_mul,h,mul_zero]))
  rw [hV]
  simp only [eval_mul, abs_mul, mul_pow]
  nlinarith only [mul_le_mul_of_nonneg_left hm
    (mul_nonneg (sq_nonneg (Q.eval x)) (mul_nonneg (abs_nonneg (Q.eval (x-1))) (abs_nonneg (Q.eval (x+1)))))]

private theorem subset_extended (A : Finset ℕ) (gs : List ℕ) : A ⊆ extend A gs := by
  induction gs generalizing A with
  | nil => rfl
  | cons g gs ih => exact (Finset.subset_insert ..).trans (ih _)

/-- A zero-free interval below the last long gap contradicts splitting over the reals. -/
theorem gap_midpoint_obstruction (A : Finset ℕ) (hA : Admissible A) (h r : ℕ) (hh : 4 ≤ h)
    (hsign : ∀ t : ℝ, (h:ℝ)-3 ≤ t → t ≤ (h:ℝ)-1 →
      0 < (-1:ℝ)^(r+1)*(normalizedValue (maxPeak A) (extend A (h::List.replicate r 2)) t).re) :
    ¬(peakPolynomial (extend A (h::List.replicate r 2))).Splits := by
  intro hsplit
  let c := maxPeak A
  let n := h-2
  let x : ℝ := (c:ℝ)+n
  let S := extend A (h::List.replicate r 2)
  let P := peakPolynomial S
  let V := peakPolynomial A
  let M := X-C (x+2)
  let L := X-C (c:ℝ)
  have hn : 2 ≤ n := by dsimp [n]; omega
  have he : h = n+2 := by dsimp [n]; omega
  have hs : Admissible S := by
    apply extend_admissible A hA
    intro j hj
    simp only [List.mem_cons, List.mem_replicate] at hj
    rcases hj with rfl|⟨_,rfl⟩ <;> omega
  have hnm : c+h ∈ S := subset_extended (insert (c+h) A) _ (Finset.mem_insert_self ..)
  have hroot : M ∣ P := by
    apply dvd_iff_isRoot.mpr
    change P.eval (x+2) = 0
    simpa only [P,x, he, Nat.cast_add, Nat.cast_ofNat, add_assoc, c] using
      peak_root S hs hnm
  have hnz (t : ℝ) (ht : t ∈ Set.Icc (x-1) (x+1)) : P.eval t ≠ 0 := by
    intro hz
    have hc : (h:ℝ) = (n:ℝ)+2 := by exact_mod_cast he
    have hl := ht.1
    have hu := ht.2
    change (c:ℝ)+n-1 ≤ t at hl
    change t ≤ (c:ℝ)+n+1 at hu
    have hbad := hsign (t-c) (by linarith) (by linarith)
    change 0 < (-1:ℝ)^(r+1)*(normalizedValue c S (t-c:ℝ)).re at hbad
    rw [normalizedValue_real, Complex.ofReal_re, show (c:ℝ)+(t-c)=t by ring] at hbad
    change (peakPolynomial S).eval t = 0 at hz
    simp [hz] at hbad
  have hval (k : ℕ) (hk : 0<k) (hk' : k<h) :
      P.eval ((c:ℝ)+k) = -(-2:ℝ)^r*V.eval ((c:ℝ)+k) := integer_before_gap A hA h r k (by omega) hk hk'
  have hpos (k : ℕ) (hk : 0<k) : 0 < V.eval ((c:ℝ)+k) := by
    have hx := peak_after_pos A hA (n:=c+k) (by dsimp [c]; omega)
    simpa using hx
  have hl : (c:ℝ)+((n-1:ℕ):ℝ)=x-1 := by dsimp [x]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hu : (c:ℝ)+((n+1:ℕ):ℝ)=x+1 := by dsimp [x]; push_cast; ring
  have hpL := hl ▸ hpos (n-1) (by omega)
  have hpR := hu ▸ hpos (n+1) (by omega)
  have hpolL := hl ▸ hval (n-1) (by omega) (by omega)
  have hpolR := hu ▸ hval (n+1) (by omega) (by omega)
  have hpolC := hval n (by omega) (by omega)
  change P.eval x = -(-2:ℝ)^r*V.eval x at hpolC
  have ratio (Q : ℝ[X]) (hQ : Q ∣ P) :
      Q.eval x ^ 2 * (V.eval (x-1)*V.eval (x+1)) ≤
      |Q.eval (x-1)| * |Q.eval (x+1)| * (V.eval x)^2 := by
    have hrat := quotient_midpoint P Q hsplit hQ x hnz
    rw [hpolL,hpolR,hpolC,abs_mul,abs_mul,abs_of_pos hpL,abs_of_pos hpR,mul_pow] at hrat
    have hnK : 0 < (-(-2:ℝ)^r)^2 := sq_pos_of_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
    apply le_of_mul_le_mul_left (a := (-(-2:ℝ)^r)^2) _ hnK
    calc
      _ = Q.eval x^2*(|-(-2:ℝ)^r| * V.eval (x-1) * (|-(-2:ℝ)^r| * V.eval (x+1))) := by
        calc
          _ = |(-(-2:ℝ)^r)|^2 * _ := by rw [sq_abs]
          _ = _ := by ring
      _ ≤ _ := hrat
      _ = _ := by ring
  by_cases hne : A.Nonempty
  · have hca : c ∈ S := subset_extended A _ (maxPeak_mem hne)
    have hpc := peak_root S hs hca
    change P.eval (c:ℝ)=0 at hpc
    obtain ⟨Z,hZ⟩ := hroot
    have hz : L ∣ Z := by
      apply dvd_iff_isRoot.mpr
      rw [hZ, eval_mul] at hpc
      exact (mul_eq_zero.mp hpc).resolve_left (by
        simp only [M, eval_sub, eval_X, eval_C, x]
        have : 0 ≤ (n:ℝ) := by positivity
        linarith)
    obtain ⟨W,hW⟩ := hz
    have hrat := ratio (M*L) ⟨W, by rw [hZ,hW,mul_assoc]⟩
    have hx : (x:ℝ)-(c:ℝ) = n := by dsimp [x]; ring
    have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hm1 : x-1-(c:ℝ) = (n:ℝ)-1 := by linarith
    have hp1 : x+1-(c:ℝ) = (n:ℝ)+1 := by linarith
    simp only [M,L,eval_mul,eval_sub,eval_X,eval_C, hx,hm1,hp1,
      show x-(x+2)= -2 by ring, show x-1-(x+2)= -3 by ring, show x+1-(x+2)= -1 by ring,
      abs_mul, abs_of_nonneg (by linarith : 0 ≤ (n:ℝ)-1), abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)+1)] at hrat
    norm_num at hrat
    have hpre := prefix_ratio A hA hne n hn
    change V.eval x ^ 2 / (V.eval ((c:ℝ)+(n-1:ℝ))*V.eval ((c:ℝ)+(n+1:ℝ))) <
      (4/3)*(n:ℝ)^2/((n:ℝ)^2-1) at hpre
    rw [show (c:ℝ)+(n-1:ℝ)=x-1 by dsimp [x]; ring, show (c:ℝ)+(n+1:ℝ)=x+1 by dsimp [x]; ring] at hpre
    have hlt := (div_lt_div_iff₀ (mul_pos hpL hpR) (by nlinarith : 0 < (n:ℝ)^2-1)).mp hpre
    nlinarith only [hlt,hrat]
  · have hrat := ratio M hroot
    have hv : V=1 := by simp [V, Finset.not_nonempty_iff_eq_empty.mp hne, peakPolynomial_empty]
    simp only [hv,eval_one,M,eval_sub,eval_X,eval_C,show x-(x+2)= -2 by ring,
      show x-1-(x+2)= -3 by ring,show x+1-(x+2)= -1 by ring] at hrat
    norm_num at hrat

end BilleyFahrbachTalmageClassification
