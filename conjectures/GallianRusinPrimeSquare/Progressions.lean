module

public import conjectures.GallianRusinPrimeSquare.Statement
public import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

@[expose] public section
namespace GallianRusinPrimeSquare
open Polynomial Finset

noncomputable def geom (r s : ℕ) : ℤ[X] := ∑ j ∈ range r, X^(s*j)

def NN (P : ℤ[X]) : Prop := ∀ k, 0≤P.coeff k

/-- Equality of all coefficients before degree M. -/
def Prefix (M : ℕ) (P Q : ℤ[X]) : Prop := ∀ k<M, P.coeff k=Q.coeff k

theorem Prefix.mul {M} {P Q U V : ℤ[X]} (h : Prefix M P Q) (g : Prefix M U V) :
    Prefix M (P*U) (Q*V) := by
  intro k hk
  simp only [coeff_mul]
  apply sum_congr rfl
  intro t ht
  have ht := Finset.mem_antidiagonal.mp ht
  rw [h _ (by omega),g _ (by omega)]

theorem Prefix.pow {M} {P Q : ℤ[X]} (h : Prefix M P Q) (e : ℕ) :
    Prefix M (P^e) (Q^e) := by
  induction e with
  | zero => simp [Prefix]
  | succ e ih => simpa only [pow_succ] using ih.mul h

theorem Prefix.congr_left {M} {P Q : ℤ[X]} (h : Prefix M P Q) (U : ℤ[X]) :
    Prefix M (U*P) (U*Q) := Prefix.mul (fun _ _ ↦ rfl) h

private theorem nn_one : NN 1 := by simp [NN,coeff_one]; omega

theorem NN.mul {P Q : ℤ[X]} (h : NN P) (g : NN Q) : NN (P*Q) :=
  fun k ↦ by rw [coeff_mul]; exact sum_nonneg fun t _ ↦ mul_nonneg (h t.1) (g t.2)

theorem NN.pow {P : ℤ[X]} (h : NN P) (n : ℕ) : NN (P^n) := by
  induction n with
  | zero => simpa using nn_one
  | succ n ih => simpa only [pow_succ] using ih.mul h

theorem geom_one (r : ℕ) : geom r 1=standard r := by simp [geom,standard]

theorem geom_eval (r s : ℕ) : (geom r s).eval 1=r := by simp [geom,eval_finsetSum]

theorem geom_coeff {r s : ℕ} (hs : 0<s) (k : ℕ) :
    (geom r s).coeff k=if s∣k ∧ k/s<r then 1 else 0 := by
  classical
  simp only [geom,finsetSum_coeff,coeff_X_pow]
  by_cases h : s∣k ∧ k/s<r
  · rw [ite_eq_left h,sum_eq_single (k/s)]
    · simp [Nat.mul_div_cancel' h.1]
    · intro b _ hb
      apply ite_eq_right
      intro he
      apply hb
      simp [he,Nat.mul_div_cancel_left _ hs]
    · simp [h.2]
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro j hj
    apply ite_eq_right
    rintro rfl
    exact h ⟨dvd_mul_right _ _,by simpa [Nat.mul_div_cancel_left _ hs] using mem_range.mp hj⟩

theorem geom_nn {r s : ℕ} (hs : 0<s) : NN (geom r s) := by
  intro k
  rw [geom_coeff hs]
  split <;> decide

theorem geom_low {r s : ℕ} (hr : 0<r) (hs : 0<s) : Prefix s (geom r s) 1 := by
  intro k hk
  rw [geom_coeff hs,coeff_one]
  by_cases e : k=0
  · simp [e,hr]
  · have d : ¬s∣k := fun h ↦ (Nat.le_of_dvd (by omega) h).not_gt hk
    simp [d,e]

theorem geom_shift (r s : ℕ) :
    (1-X^s) * geom r s = 1-X^(s*r) := by
  unfold geom
  simp_rw [pow_mul]
  have h := geom_sum_mul (X^s : ℤ[X]) r
  linear_combination -h

theorem geom_ne {r s} (hr : 0<r) (hs : 0<s) : geom r s≠0 := by
  intro h
  have c := geom_coeff (r:=r) hs 0
  simp [h,hr] at c

theorem standard_split {r s : ℕ} :
    standard (s*r)=geom s 1 * geom r s := by
  rw [←geom_one]
  apply mul_left_cancel₀ (show (1-X^1 : ℤ[X])≠0 by intro h; have hc := congrArg (fun U : ℤ[X] ↦ U.eval 0) h; simp at hc)
  rw [←mul_assoc,geom_shift,geom_shift]
  simp [geom_shift]

theorem expand_geom (r s t : ℕ) : expand ℤ t (geom r s) = geom r (t*s) := by
  simp [geom,←pow_mul,mul_assoc]

theorem coeff_shift (U : ℤ[X]) (s k : ℕ) :
    ((1-X^s)*U).coeff k = U.coeff k - if s≤k then U.coeff (k-s) else 0 := by
  rw [sub_mul,one_mul,coeff_sub,coeff_X_pow_mul']

def lag (s : ℕ) (f : ℕ → ℤ) (k : ℕ) : ℤ := if s≤k then f (k-s) else 0

def delta (s : ℕ) (f : ℕ → ℤ) (k : ℕ) : ℤ := f k-lag s f k

private theorem lag_lag (s t : ℕ) (f : ℕ → ℤ) (k : ℕ) :
    lag s (lag t f) k=lag (s+t) f k := by
  simp only [lag]
  split_ifs <;> first | rfl | congr 1; omega

private theorem lag_sub (s : ℕ) (f g : ℕ → ℤ) (k : ℕ) :
    lag s (fun j ↦ f j-g j) k = lag s f k - lag s g k := by
  simp only [lag]
  split <;> simp

private theorem delta_comm (s t : ℕ) (f : ℕ → ℤ) (k : ℕ) :
    delta s (delta t f) k=delta t (delta s f) k := by
  change f k - lag t f k - lag s (fun j ↦ f j-lag t f j) k =
    f k - lag s f k - lag t (fun j ↦ f j-lag s f j) k
  rw [lag_sub,lag_sub,lag_lag,lag_lag,Nat.add_comm s t]
  ring

private theorem delta_unique {s M : ℕ} (hs : 0<s) {f g : ℕ → ℤ}
    (hf : ∀ k<M, delta s f k=delta s g k) {k : ℕ} (hk : k<M) : f k=g k := by
  induction k using Nat.strong_induction_on with | ind k ih =>
    have e := hf k hk
    simp only [delta,lag] at e
    by_cases h : s≤k
    · simp only [h,ite_true] at e
      rw [ih (k-s) (by omega) (by omega)] at e
      omega
    · simpa [h] using e

private theorem delta_repeat {s : ℕ} {U : ℤ[X]} (hz : ∀ k, s≤k → U.coeff k=0) :
    delta s (fun k ↦ U.coeff (k%s)) = U.coeff := by
  funext k
  by_cases h : s≤k
  · rw [delta,lag,ite_eq_left h,←Nat.mod_eq_sub_mod h,hz k h,sub_self]
  · simp [delta,lag,h,Nat.mod_eq_of_lt (by omega : k<s)]

/-- Recover coefficients from a relation between two finite differences. -/
theorem periodic_coeff {s t M : ℕ} (hs : 0<s) {P U : ℤ[X]}
    (hz : ∀ k, s≤k → U.coeff k=0)
    (h : Prefix M ((1-X^s)*P) ((1-X^t)*U)) {k : ℕ} (hk : k<M) :
    P.coeff k=delta t (fun j ↦ U.coeff (j%s)) k := by
  apply delta_unique hs (M:=M) _ hk
  intro j hj
  rw [delta_comm,delta_repeat hz]
  simpa only [delta,lag,coeff_shift] using h j hj

theorem geom_mul_coeff (U : ℤ[X]) (r s k : ℕ) :
    (U*geom r s).coeff k = ∑ j ∈ range r, if s*j≤k then U.coeff (k-s*j) else 0 := by
  simp [geom,mul_sum,coeff_mul_X_pow']

/-- Every degree in the indicated interval has a positive coefficient. -/
theorem geom_power_support {r : ℕ} (hr : 0<r) (e k : ℕ) :
    (0<(geom r 1^e).coeff k ↔ k≤e*(r-1)) ∧
    (e*(r-1)<k → (geom r 1^e).coeff k=0) := by
  induction e generalizing k with
  | zero =>
    simp only [pow_zero,zero_mul,coeff_one]
    by_cases h : k=0 <;> simp [h]
  | succ e ih =>
    rw [pow_succ,geom_mul_coeff]
    simp only [one_mul,Nat.succ_mul]
    have nn (j) : 0≤(if j≤k then (geom r 1^e).coeff (k-j) else 0) := by
      split
      · exact (geom_nn (r:=r) (by decide : 0<1)).pow e _
      · rfl
    by_cases he : k ≤ e*(r-1)+(r-1)
    · let j := min k (r-1)
      have jmem : j∈range r := mem_range.mpr (by dsimp [j]; omega)
      have jk : j≤k := min_le_left _ _
      have jj : k-j≤e*(r-1) := by dsimp [j]; omega
      have hj := (ih (k-j)).1.mpr jj
      have val := single_le_sum (fun j (_ : j∈range r) ↦ nn j) jmem
      rw [ite_eq_left jk] at val
      exact ⟨iff_of_true (hj.trans_le val) he,fun bad ↦ (bad.not_ge he).elim⟩
    · have z : (∑ j ∈ range r, if j≤k then (geom r 1^e).coeff (k-j) else 0)=0 := by
        apply sum_eq_zero
        intro j hj
        have := mem_range.mp hj
        split
        · apply (ih _).2
          omega
        · rfl
      simp [z,he]

/-- Each representation of k as i+qj contributes one face. -/
theorem window (p q k : ℕ) (hp : 0<p) (hq : 0<q) :
    (geom p 1*geom p q).coeff k =
    ((range p).filter fun j ↦ j≤k/q ∧ (k<p ∨ (k-p)/q<j)).card := by
  rw [geom_mul_coeff,Finset.natCast_card_filter]
  apply sum_congr rfl
  intro j _
  rw [geom_coeff (by decide : 0<1)]
  simp only [one_dvd,true_and,Nat.div_one]
  have upper : q*j≤k ↔ j≤k/q := by rw [Nat.le_div_iff_mul_le hq,Nat.mul_comm]
  have low : k-q*j<p ↔ k<p ∨ (k-p)/q<j := by
    rw [Nat.div_lt_iff_lt_mul hq,Nat.mul_comm j q]
    omega
  split_ifs <;> first | rfl | tauto

theorem window_low {p q h : ℕ} (hq : 0<q) (hh : q*h<p) :
    (geom p 1*geom p q).coeff (q*h)=h+1 := by
  rw [window _ _ _ (by omega) hq]
  have hhp : h<p := by have := Nat.le_mul_of_pos_left h hq; omega
  have e : ((range p).filter fun j ↦ j≤q*h/q ∧ (q*h<p ∨ (q*h-p)/q<j))=range (h+1) := by
    ext j
    simp [hh,Nat.mul_div_cancel_left _ hq]
    omega
  rw [e,card_range]
  simp

theorem window_high {p q h r : ℕ} (hq : 0<q) (hr : r<q) (hp : p=q*h+r)
    (bound : 2*h<p) :
    (geom p 1*geom p q).coeff (p+q*h)=h := by
  rw [window _ _ _ (by omega) hq]
  have hi : (p+q*h)/q=2*h := by
    rw [show p+q*h=r+q*(2*h) by rw [hp]; ring,Nat.add_mul_div_left _ _ hq,
      Nat.div_eq_of_lt hr,zero_add]
  have lo : (p+q*h-p)/q=h := by simp [Nat.mul_div_cancel_left _ hq]
  have e : ((range p).filter fun j ↦ j≤(p+q*h)/q ∧
      (p+q*h<p ∨ (p+q*h-p)/q<j))=Ioc h (2*h) := by
    ext j
    simp only [mem_filter,mem_range,mem_Ioc,hi,lo]
    omega
  rw [e,Nat.card_Ioc]
  congr 1
  omega

theorem square_window {p : ℕ} (hp : 2≤p) :
    (geom p 1^2).coeff (2*p-2)=1 ∧ (geom p 1^2).coeff (2*p-1)=0 := by
  rw [pow_two,window _ _ _ (by omega) (by decide : 0<1),window _ _ _ (by omega) (by decide : 0<1)]
  simp only [Nat.div_one]
  have first : ((range p).filter fun j ↦ j≤2*p-2 ∧ (2*p-2<p ∨ 2*p-2-p<j))={p-1} := by
    ext j
    simp only [mem_filter,mem_range,mem_singleton]
    omega
  have last : ((range p).filter fun j ↦ j≤2*p-1 ∧ (2*p-1<p ∨ 2*p-1-p<j))=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    simp only [mem_filter,mem_range] at hj
    omega
  simp [first,last]

end GallianRusinPrimeSquare
