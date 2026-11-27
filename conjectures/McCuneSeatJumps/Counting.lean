module

public import conjectures.McCuneSeatJumps.Statement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
open Finset
namespace McCuneSeatJumps

/-- The two rectangle widths sum to this integer when the losing state starts with l seats. -/
def room (h k l : ℕ) := h+2*k-3*k*l

/-- The residue for a second state that starts with a seats. -/
def residue (h k l a : ℕ) := (k*(a+(h+1-l))) % h

/-- The product of the two widths. A residue outside the feasible interval gives zero. -/
def cellWeight (h k l a : ℕ) := residue h k l a * (room h k l-residue h k l a)

private theorem omitted {h k l a : ℕ} (hk : 0 < k) (hl : 0 < l) (lh : l ≤ h)
    (ha : h-l+1 ≤ a) (ah : a < h) : cellWeight h k l a = 0 := by
  by_cases hz : room h k l = 0
  · simp [cellWeight,hz]
  let d := h-a+(l-1)
  have dp : 0 < d := by dsimp [d]; omega
  have dl' : d ≤ 3*l-2 := by dsimp [d]; omega
  have hshift : (a+(h+1-l))+d = 2*h := by dsimp [d]; omega
  have e : k*(3*l-2)+2*k=3*k*l := by
    rw [show 2*k=k*2 by omega, ← Nat.mul_add, Nat.sub_add_cancel (by omega : 2 ≤ 3*l)]
    ring
  have kd : k*d < h := by
    have hh : 3*k*l < h+2*k := Nat.lt_of_sub_ne_zero hz
    have := Nat.mul_le_mul_left k dl'
    omega
  have eq : residue h k l a = h-k*d := by
    have hh : k*(a+(h+1-l)) + k*d ≡ h-k*d+k*d [MOD h] := by
      rw [← Nat.mul_add, hshift, Nat.sub_add_cancel kd.le]
      simp [Nat.ModEq, ← Nat.mul_assoc]
    have q := Nat.ModEq.add_right_cancel' (k*d) hh
    simpa [Nat.ModEq, residue, Nat.mod_eq_of_lt (show h-k*d < h by
      have kp := Nat.mul_pos hk dp; omega)] using q
  have le : room h k l ≤ h-k*d := by
    unfold room
    have := Nat.mul_le_mul_left k dl'
    omega
  simp [cellWeight,eq,Nat.sub_eq_zero_of_le le]

private theorem sum_full {h k l : ℕ} (hk : 0 < k) (hl : 0 < l) (lh : l ≤ h) :
    ∑ a ∈ range (h-l+1), cellWeight h k l a = ∑ a ∈ range h, cellWeight h k l a := by
  apply sum_subset_zero_on_sdiff (range_mono (by omega))
  · intro a ha
    simp only [mem_sdiff, mem_range] at ha
    exact omitted hk hl lh (by omega) ha.1
  · intros; rfl

private theorem permuted (m n c : ℕ) (hm : 0 < m) (co : m.Coprime n) (f : ℕ → ℕ) :
    ∑ a ∈ range m, f ((n*(a+c))%m) = ∑ a ∈ range m, f a := by
  let p (a : Fin m) : Fin m := ⟨(n*(a+c))%m, Nat.mod_lt _ hm⟩
  have inj : Function.Injective p := by
    intro a b e
    have e' : n*(a.val+c) ≡ n*(b.val+c) [MOD m] := congrArg Fin.val e
    apply Fin.ext
    exact ((Nat.ModEq.cancel_left_of_coprime co.gcd_eq_one e').add_right_cancel' c).eq_of_lt_of_lt a.isLt b.isLt
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_bijective p (Finite.injective_iff_bijective.mp inj) _ _ fun _ => rfl

private theorem periods (g m n c : ℕ) (hm : 0 < m) (co : m.Coprime n) (f : ℕ → ℕ) :
    ∑ a ∈ range (g*m), f ((n*(a+c))%m) = g*∑ a ∈ range m, f a := by
  induction g with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, sum_range_add, ih, Nat.succ_mul]
    congr 1
    convert permuted m n c hm co f using 2 with i
    congr 1
    rw [show n*(t*m+i+c)=(n*t)*m+n*(i+c) by ring, Nat.mul_add_mod_self_right]

private theorem tetrahedral (t : ℕ) :
    6 * ∑ i ∈ range t, i*(t-i) = t*(t-1)*(t+1) := by
  have step (n : ℕ) :
      ∑ i ∈ range (n+1), i*(n+1-i) = (∑ i ∈ range n, i*(n-i)) + ∑ i ∈ range (n+1), i := by
    rw [sum_range_succ, sum_range_succ (f := fun i => i)]
    have h : ∑ i ∈ range n, i*(n+1-i) = ∑ i ∈ range n, (i*(n-i)+i) := by
      apply sum_congr rfl
      intro i hi
      rw [show n+1-i=(n-i)+1 by simp only [mem_range] at hi; omega, Nat.mul_add_one]
    rw [h,sum_add_distrib]
    simp only [show n+1-n=1 by omega, mul_one]
    omega
  induction t with
  | zero => simp
  | succ t ih =>
    have H := sum_range_id_mul_two (t+1)
    rw [step,Nat.mul_add,ih]
    simp only [Nat.add_one_sub_one] at H ⊢
    cases t with
    | zero => simp
    | succ t =>
      simp only [Nat.add_one_sub_one]
      nlinarith only [H]

/-- Six times the total width product for one losing seat count. -/
theorem sum_cellWeight {h k l : ℕ} (hh : 0 < h) (hk : 0 < k) (hl : 0 < l) (lh : l ≤ h) :
    6 * ∑ a ∈ range (h-l+1), cellWeight h k l a =
      (h.gcd k)^3 * (room h k l / h.gcd k) * (room h k l / h.gcd k - 1) *
        (room h k l / h.gcd k + 1) := by
  let g := h.gcd k
  let m := h/g
  let n := k/g
  let t := room h k l/g
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ hh
  have dh : g ∣ h := Nat.gcd_dvd_left ..
  have dk : g ∣ k := Nat.gcd_dvd_right ..
  have dw : g ∣ room h k l := Nat.dvd_sub (dvd_add dh (dvd_mul_of_dvd_right dk _))
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right dk _) _)
  have gm : g*m=h := Nat.mul_div_cancel' dh
  have gn : g*n=k := Nat.mul_div_cancel' dk
  have gt : g*t=room h k l := Nat.mul_div_cancel' dw
  have mp : 0<m := Nat.div_pos (Nat.le_of_dvd hh dh) gp
  have co : m.Coprime n := Nat.coprime_div_gcd_div_gcd gp
  have tm : t≤m := by
    apply Nat.div_le_div_right
    unfold room
    have pos := Nat.mul_le_mul_left (3*k) hl
    omega
  have row (a) : cellWeight h k l a =
      g^2 * (((n*(a+(h+1-l)))%m)*(t-((n*(a+(h+1-l)))%m))) := by
    have hr : residue h k l a = g*((n*(a+(h+1-l)))%m) := by
      unfold residue
      nth_rw 1 [← gn]
      nth_rw 2 [← gm]
      rw [Nat.mul_assoc, Nat.mul_mod_mul_left]
    rw [cellWeight,hr,← gt, ← Nat.mul_sub]
    ring
  rw [sum_full hk hl lh]
  simp_rw [row]
  rw [← mul_sum]
  have per := periods g m n (h+1-l) mp co (fun i => i*(t-i))
  rw [gm] at per
  rw [per]
  have trunc : ∑ i ∈ range t, i*(t-i) = ∑ i ∈ range m, i*(t-i) := by
    apply sum_subset_zero_on_sdiff (range_mono tm)
    · intro i hi
      simp only [mem_sdiff, mem_range] at hi
      simp [Nat.sub_eq_zero_of_le (by omega : t ≤ i)]
    · intros; rfl
  rw [← trunc]
  change 6*(g^2*(g*∑ i ∈ range t, i*(t-i))) = g^3*t*(t-1)*(t+1)
  rw [show 6*(g^2*(g*∑ i ∈ range t, i*(t-i))) = g^3*(6*∑ i ∈ range t, i*(t-i)) by ring,
    tetrahedral]
  ring

/-- The same sum in the real units used for the simplex areas. -/
theorem sum_cellWeight_real {h k l : ℕ} (hh : 0 < h) (hk : 0 < k) (hl : 0 < l) (lh : l ≤ h) :
    ((∑ a ∈ range (h-l+1), cellWeight h k l a : ℕ) : ℝ) =
      ((h.gcd k : ℕ) : ℝ)^3 *
        (((room h k l / h.gcd k : ℕ) : ℝ)^3 - ((room h k l / h.gcd k : ℕ) : ℝ)) / 6 := by
  have e := congrArg (Nat.cast (R := ℝ)) (sum_cellWeight hh hk hl lh)
  cases ht : room h k l / h.gcd k with
  | zero =>
    simp only [ht, Nat.zero_sub, Nat.zero_mul, Nat.cast_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_self, mul_zero, zero_div] at e ⊢
    push_cast at e ⊢
    linarith only [e]
  | succ t =>
    rw [ht, Nat.add_one_sub_one] at e
    push_cast at e ⊢
    linear_combination e / 6

end McCuneSeatJumps
