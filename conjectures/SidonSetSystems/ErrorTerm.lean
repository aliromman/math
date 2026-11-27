module

public import conjectures.SidonSetSystems.Sparse
public import conjectures.SidonSetSystems.Lower
import Mathlib.Data.Nat.Choose.Bounds

public section
namespace SidonSetSystems
open Filter

private theorem choose_shift (N n d t : ℕ) (ht : N+t≤n) :
    (N+t).choose (d+1) ≤ N.choose (d+1)+t*n^d := by
  induction t with
  | zero => simp
  | succ t ih =>
    have prev := ih (by omega)
    have step := ((N+t).choose_le_pow d).trans (Nat.pow_le_pow_left (by omega : N+t≤n) d)
    rw [show N+(t+1)=(N+t)+1 by omega,Nat.choose_succ_succ,Nat.succ_mul]
    simp only [Nat.succ_eq_add_one]
    omega

/-- For each fixed k ≥ 3, the deficit from the published upper bound has order at most n^(k−2). -/
theorem sharp_error (k : ℕ) (hk : 3≤k) : ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
    upperBound k n ≤ extremal k n+C*n^(k-2) := by
  obtain ⟨D,lo⟩ := lower_estimate hk (sparse_shapes k hk)
  let s := 1+3^D
  let d := k-2
  have s2 : 2≤s := by
    have h : 0<3^D := by positivity
    dsimp [s]
    omega
  have deg : d+1=k-1 := by dsimp [d]; omega
  refine ⟨s+D+1,?_⟩
  filter_upwards [eventually_ge_atTop s] with n hn
  let N := n-s
  have total : N+s=n := Nat.sub_add_cancel hn
  have low := lo N
  change N.choose (k-1) ≤ extremal k (N+s)+D*(N+2)^d at low
  rw [total] at low
  have loss := choose_shift N n d s total.le
  rw [total,deg] at loss
  have upper := Nat.choose_le_choose (k-1) (Nat.sub_le n 1)
  have err := Nat.mul_le_mul_left D (Nat.pow_le_pow_left (by omega : N+2≤n) d)
  have tail : n≤n^d := by
    simpa using (Nat.pow_le_pow_right (by omega : 0<n) (by dsimp [d]; omega : 1≤d))
  change (n-1).choose (k-1)+(n-k) ≤ extremal k n+(s+D+1)*n^d
  rw [Nat.add_mul,Nat.add_mul,one_mul]
  omega

/-- info: 'SidonSetSystems.sharp_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sharp_error

end SidonSetSystems
