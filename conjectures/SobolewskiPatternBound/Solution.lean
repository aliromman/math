module

public import conjectures.SobolewskiPatternBound.Statement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace SobolewskiPatternBound

/-- If `M` divides `z+n` with `n>0`, its residue plus `n` is at least `M`. -/
private theorem residue_bound {M z n : ℕ} (hn : 0 < n) (h : M ∣ z+n) :
    M ≤ z % M + n := by
  apply Nat.le_of_dvd (by omega)
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.mod_add_mod]
  exact Nat.mod_eq_zero_of_dvd h

/-- In the first `2^j` multiples of a Mersenne number, the pattern consisting of
a one followed by `j` zeros cannot occur. -/
private theorem no_window {j k n : ℕ} (hj : j < k) (hn : n < 2^j) (p : ℕ) :
    n * (2^k-1) / 2^p % 2^(j+1) ≠ 2^j := by
  let z := n*(2^k-1)
  change z / 2^p % 2^(j+1) ≠ 2^j
  have hq : 0 < 2^k := by positivity
  have ht : 0 < 2^p := by positivity
  intro h
  by_cases zero : n = 0
  · simp [z, zero] at h
    exact (Nat.ne_of_gt (by positivity : 0 < 2^j)) h.symm
  have hd : 2^k ∣ z+n := by
    have hz : z+n = n*2^k := by
      dsimp [z]
      simpa only [Nat.mul_add, Nat.mul_one] using
        congrArg (n * ·) (Nat.sub_add_cancel hq)
    rw [hz]
    exact dvd_mul_left ..
  by_cases high : k ≤ p
  · have ht' := Nat.pow_le_pow_right (by decide : 0 < 2) high
    have h1 : z ≤ n*2^p := Nat.mul_le_mul_left n (by omega)
    have h2 := Nat.mul_lt_mul_of_pos_right hn ht
    have h3 := (Nat.div_lt_iff_lt_mul ht).mpr (h1.trans_lt h2)
    have h4 := Nat.mod_le (z/2^p) (2^(j+1))
    omega
  have low : z / 2^p % 2^j = 0 := by
    rw [← Nat.mod_mod_of_dvd (z / 2^p) (Nat.pow_dvd_pow 2 (show j ≤ j+1 by omega)), h, Nat.mod_self]
  have small : z % 2^(p+j) < 2^p := by
    rw [pow_add, Nat.mod_mul, low, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_lt _ ht
  by_cases below : p+j ≤ k
  · have hr := residue_bound (Nat.pos_of_ne_zero zero) ((Nat.pow_dvd_pow 2 below).trans hd)
    rw [pow_add] at hr small
    have h1 := Nat.mul_le_mul_left (2^p) hn
    have h2 := Nat.le_mul_of_pos_left n ht
    rw [Nat.mul_succ] at h1
    omega
  · have hr := residue_bound (Nat.pos_of_ne_zero zero) hd
    have hdvd := Nat.pow_dvd_pow 2 (show k ≤ p+j by omega)
    have hred := Nat.mod_le (z % 2^(p+j)) (2^k)
    rw [Nat.mod_mod_of_dvd z hdvd] at hred
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show p ≤ k-1 by omega)
    have hb := Nat.pow_le_pow_right (by decide : 0 < 2) (show j ≤ k-1 by omega)
    have hh : 2^k = 2^(k-1) + 2^(k-1) := by
      calc 2^k = 2^((k-1)+1) := by congr 1; omega
           _ = _ := by rw [pow_succ, Nat.mul_two]
    omega

/-- The progression from zero has at least `2^j` terms when its difference is `2^k-1`
and the pattern is one followed by `j` zeros, for any `k>j`. -/
public theorem mersenne_prefix {j k : ℕ} (hj : j < k) :
    Prefix (j+1) (2^j) (2^k-1) (2^j) := by
  have vanishes {n : ℕ} (hn : n < 2^j) : occurrences (j+1) (2^j) (n*(2^k-1)) = 0 := by
    unfold occurrences count
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _
    exact no_window hj hn p
  intro t
  have h0 := vanishes (n:=0) (by positivity)
  rw [Nat.zero_mul] at h0
  rw [vanishes t.isLt, h0]

/-- A short positive word can contain the pattern only at its least significant position. -/
private theorem short_count {j w a : ℕ} (hj : j+1 ≤ w) (ha : a < 2^(j+1)) :
    count (j+1) (2^j) w a = if a = 2^j then 1 else 0 := by
  let s := (Finset.range (w + 1 - (j+1))).filter fun p => a / 2^p % 2^(j+1) = 2^j
  have off {p : ℕ} (hp : p ≠ 0) : a / 2^p % 2^(j+1) ≠ 2^j := by
    have pp : 2 ≤ 2^p := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ p by omega)
    have hh := Nat.mul_le_mul_left (2^j) pp
    rw [pow_succ] at ha
    have hq := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^p)).mpr (ha.trans_le hh)
    exact (lt_of_le_of_lt (Nat.mod_le _ _) hq).ne
  by_cases hv : a = 2^j
  · have h : s = {0} := by
      ext p
      by_cases hp : p = 0
      · subst p
        simp [s, hv, Nat.mod_eq_of_lt (hv ▸ ha), show j < w by omega]
      · simp [s, off hp, hp]
    change s.card = _
    simp [h, hv]
  · have h : s = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro p _
      rcases eq_or_ne p 0 with rfl | hp
      · simpa [Nat.mod_eq_of_lt ha] using hv
      · exact off hp
    change s.card = _
    simp [h, hv]

/-- The extremal pair of binary blocks in the definition of the two constants is (1,1). -/
private theorem first_zeros {j : ℕ} (hj : 1 ≤ j) : FirstPair (j+1) (2^j) j 1 1 := by
  let B := 2^j
  have hB : 2 ≤ B := Nat.pow_le_pow_right (by decide : 0 < 2) hj
  have hsize : (2^j : ℕ).size = j+1 := Nat.size_pow
  have h0 (x : ℕ) : count (j+1) (2^j) j x = 0 := by simp [count]
  have hsmall : B+1 < 2^(j+1) := by rw [pow_succ]; change B+1 < B*2; omega
  have hw : j+1 ≤ j+j := by omega
  have c0 := short_count (j:=j) hw (a:=0) (by positivity)
  have c1 := short_count (j:=j) hw (a:=1) (by omega)
  have cB := short_count (j:=j) hw (a:=B) (by omega)
  have cB1 := short_count (j:=j) hw (a:=B+1) hsmall
  unfold FirstPair
  simp only [Nat.add_sub_cancel]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp only [parity, hsize, Nat.sub_self, Nat.zero_add, Nat.add_sub_cancel,
      h0, Nat.one_mul, B] at *
    simp_all
  · intro x y hxy
    rcases hxy with h | ⟨h, hy⟩
    · have hx : x.val = 0 := by omega
      simp [parity, hsize, hx, h0]
      omega
    · have hy0 : y.val = 0 := by omega
      have z0 : (0:ℕ) ≠ 2^j := by change 0 ≠ B; omega
      have z1 : (1:ℕ) ≠ 2^j := by change 1 ≠ B; omega
      simp [parity, hsize, h, hy0, h0, c0, c1, z0, z1]

private theorem envelope_lt {j : ℕ} :
    envelope (j+1) j 1 1 (2^(2*j+4)-1) < 17 := by
  let d := 2^(2*j+4)-1
  have he : 2^(2*j+4) = 16*(2^j)^2 := by rw [pow_add, Nat.mul_comm 2 j, pow_mul]; ring
  have hdNat : d < 16*(2^j)^2 := by
    dsimp [d]
    rw [he]
    exact Nat.sub_lt (by positivity) (by decide)
  have hd : (d : ℝ) < 16 * ((2:ℝ)^j)^2 := by exact_mod_cast hdNat
  have hp : 0 < ((2:ℝ)^j)^2 := by positivity
  have he2 : (2:ℝ)^(j+(j+1)-1) = ((2:ℝ)^j)^2 := by
    rw [show j+(j+1)-1=j*2 by omega, pow_mul]
  change envelope (j+1) j 1 1 d < 17
  simp only [envelope, intercept, slope, Nat.cast_one, he2, div_mul_eq_mul_div, one_mul]
  have h := (div_lt_iff₀ hp).mpr hd
  have hb : 0 ≤ (2:ℝ)^j * (1 / ((2:ℝ)^j)^2) := by positivity
  linarith

/-- The predicted bound stays below 17 while these progressions have at least `2^j` terms. -/
public theorem family {j : ℕ} (hj : 1 ≤ j) :
    let d := 2^(2*j+4)-1
    FirstPair (j+1) (2^j) j 1 1 ∧ 2^(2*(j+1)+1) ≤ d ∧
    envelope (j+1) j 1 1 d < 17 ∧ (2^j : ℕ) ≤ lengthAtZero (j+1) (2^j) d := by
  dsimp only
  refine ⟨first_zeros hj, ?_, envelope_lt, ?_⟩
  · have := Nat.pow_lt_pow_right (by decide : 1 < 2) (show 2*(j+1)+1 < 2*j+4 by omega)
    omega
  · exact le_iSup_of_le (2^j) (le_iSup_of_le (mersenne_prefix (show j < 2*j+4 by omega)) le_rfl)

public theorem resolution : ¬ Conjecture := by
  intro h
  obtain ⟨hpair, hd, topBound, longRun⟩ := family (j := 5) (by decide)
  have hj : Nat.factorization 32 2 = 5 := Nat.factorization_pow_self (n := 5) Nat.prime_two
  have pred := h 6 32 (by decide) (by decide) (by decide) (by decide)
  dsimp only at pred
  rw [hj] at pred
  have ub := ((pred 1 1 hpair).2 16383 hd).1
  have hc : ((32 : ℝ) : EReal) ≤ (envelope 6 5 1 1 16383 : EReal) := longRun.trans ub
  exact (not_le_of_gt (topBound.trans (by norm_num : (17 : ℝ) < 32))) (EReal.coe_le_coe_iff.mp hc)

/-- info: 'SobolewskiPatternBound.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end SobolewskiPatternBound
