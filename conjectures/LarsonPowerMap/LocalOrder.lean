module

public import conjectures.LarsonPowerMap.PrimeCycle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

@[expose] public section
open Finset
namespace LarsonPowerMap

private theorem sq_zero_pow {R : Type*} [CommRing R] {w : R} (zero : w^2=0) (n : ℕ) :
    (1+w)^n = 1+n*w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih,Nat.cast_succ]
    linear_combination (n:R)*zero

/-- For a composite exceptional length, every possible exponent gives the same
orbit length. It is the least prime divisor of the exceptional length. -/
theorem composite_order {n a k : ℕ} (lo : 2≤a) (only : bad n a={k}) (comp : ¬k.Prime) :
    orderOf (a : ZMod k) = k.minFac := by
  obtain ⟨two,up,_⟩ := single_bounds only
  let p := k.minFac
  let r := k/p
  have hp : p.Prime := Nat.minFac_prime (by omega)
  let _ : Fact p.Prime := ⟨hp⟩
  have hp₂ := hp.two_le
  have pd : p∣k := Nat.minFac_dvd _
  have eq : r*p=k := Nat.div_mul_cancel pd
  have pr : p≤r := Nat.minFac_le_div (by omega) comp
  have rk : r<k := Nat.div_lt_self (by omega) hp.one_lt
  have good {j} (pos : 1≤j) (lt : j<k) : j∣a-1 := by
    have h : a ≡ 1 [MOD j] := by
      by_contra ne
      have bj : j∈bad n a := mem_filter.mpr ⟨mem_Icc.mpr ⟨pos,by omega⟩,ne⟩
      exact lt.ne (mem_singleton.mp (only ▸ bj))
    exact (Nat.modEq_iff_dvd' (by omega : 1≤a)).mp h.symm
  have pdiv : p∣a-1 := good (by omega) (by omega)
  have rdiv : r∣a-1 := good (by omega) rk
  let w : ZMod k := ((a-1 : ℕ) : ZMod k)
  have z : w^2=0 := by
    have d : k∣(a-1)^2 := by rw [←eq,pow_two]; exact Nat.mul_dvd_mul rdiv pdiv
    simpa [w] using (ZMod.natCast_eq_zero_iff _ k).mpr d
  have pw : (p : ZMod k)*w=0 := by
    have d : k∣p*(a-1) := by rw [←eq,mul_comm r p]; exact Nat.mul_dvd_mul_left _ rdiv
    simpa [w] using (ZMod.natCast_eq_zero_iff _ k).mpr d
  have aw : (a : ZMod k)=1+w := by
    dsimp [w]
    rw [Nat.cast_sub (by omega : 1≤a),Nat.cast_one]
    ring
  apply orderOf_eq_prime_iff.mpr
  refine ⟨by rw [aw,sq_zero_pow z,pw,add_zero],?_⟩
  intro isOne
  have bj : k∈bad n a := only ▸ mem_singleton_self k
  exact (mem_filter.mp bj).2 ((ZMod.natCast_eq_natCast_iff a 1 k).mp (by simpa using isOne))

theorem local_lower {n k a : ℕ} (h : bad n a={k}) : (1:ℚ)/(2*k) ≤ loss k a := by
  have mem : k∈bad n a := h ▸ mem_singleton_self k
  have ne : (a : ZMod k)≠1 := fun e =>
    (mem_filter.mp mem).2 ((ZMod.natCast_eq_natCast_iff a 1 k).mp (by simpa using e))
  have ko := (single_bounds h).1
  have kp : 0<(k:ℚ) := by exact_mod_cast (by omega : 0<k)
  let d := orderOf (a : ZMod k)
  have dn : d≠1 := fun e => ne (orderOf_eq_one_iff.mp e)
  change 1/(2*(k:ℚ)) ≤ (1-(d:ℚ)⁻¹)/k
  by_cases zero : d=0
  · rw [zero]; simp only [Nat.cast_zero,inv_zero,sub_zero]
    apply div_le_div_of_nonneg_left (by norm_num) kp
    linarith
  · have two : 2≤d := by omega
    have dp : (2:ℚ)≤d := by exact_mod_cast two
    have dpos : (0:ℚ)<d := by linarith
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr dp) kp.le]

end LarsonPowerMap
