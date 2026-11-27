module

public import conjectures.MatrixWidth.Drift
public import conjectures.MatrixWidth.Cesaro
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section
namespace MatrixWidth
open Finset Filter
open scoped Topology

theorem transition_kernel (k d : ℕ) : Kernel (transition k d) :=
  ⟨transition_nonneg k d,row_hasSum k d⟩

theorem expect_finite (k d x : ℕ) (f : ℕ→ℝ) :
    HasSum (fun y => transition k d x y*f y) (∑ y∈range (x+k+1),transition k d x y*f y) := by
  apply hasSum_sum_of_ne_finset_zero
  intro y hy
  have h : transition k d x y=0 := le_antisymm (le_of_not_gt fun h =>
    hy (mem_range.mpr (by have := (transition_support h).1; omega))) (transition_nonneg ..)
  rw [h,zero_mul]

theorem uniform_drift {k d : ℕ} (hd : 2≤d) (hk : d<k) {β : ℝ}
    (hb : 1<β) (hc : β*((k:ℝ)-d)<(d:ℝ)*((k:ℝ)-1)) :
    ∃ D : ℝ, 0≤D ∧ ∀x,expect (transition k d) x (weight β)≤weight β x/2+D := by
  have lt := (drift_ratio hd hk hb hc).eventually_lt_const (by norm_num : 0<(1:ℝ)/2)
  obtain ⟨n,hn⟩ := eventually_atTop.mp lt
  let E := fun x => expect (transition k d) x (weight β)
  have Epos (x) : 0≤E x := tsum_nonneg fun y => mul_nonneg (transition_nonneg ..) (weight_pos β y).le
  let D := ∑ i∈range n,E i
  have Dpos : 0≤D := sum_nonneg fun i _ => Epos i
  refine ⟨D,Dpos,fun x => ?_⟩
  by_cases h : x<n
  · have small := single_le_sum (f:=E) (fun i _ => Epos i) (mem_range.mpr h)
    change E x ≤ weight β x/2+D
    linarith only [small,(weight_pos β x).le]
  · have ux := (div_lt_iff₀ (weight_pos β x)).mp (hn x (by omega))
    rw [show expect (transition k d) x (weight β)=_ from (expect_finite k d x (weight β)).tsum_eq]
    linarith

theorem stationary_positive {k d : ℕ} (hd : 2≤d) (hk : d<k) {π : ℕ→ℝ}
    (hπ : Stationary (transition k d) π) (x : ℕ) : 0<π x := by
  have some : ∃ i,0<π i := by
    by_contra! h
    have pz : π=0 := funext fun i => le_antisymm (h i) (hπ.1 i)
    have bad := hπ.2.1.tsum_eq
    simp [pz] at bad
  obtain ⟨m,hm⟩ := some
  have step {i j : ℕ} (p : 0<π i) (q : 0<transition k d i j) : 0<π j :=
    (mul_pos p q).trans_le (stationary_step (transition_kernel k d) hπ i j)
  have h0 : 0<π 0 := by
    induction m with
    | zero => exact hm
    | succ m ih => exact ih (step hm (neighbour_down hd hk.le m))
  induction x with
  | zero => exact h0
  | succ x ih => exact step ih (neighbour_up (by omega) hk x)

/-- Positive recurrence in the nondegenerate regime of the published urn model. -/
theorem recurrent {k d : ℕ} (hd : 2≤d) (hk : d<k) :
    PositiveRecurrent (transition k d) ∧ ∃ π,Stationary (transition k d) π := by
  let β : ℝ := 3/2
  have hb : 1<β := by norm_num [β]
  have hdn : (2:ℝ)≤d := by exact_mod_cast hd
  have hkc : 0≤(k:ℝ) := Nat.cast_nonneg k
  have hc : β*((k:ℝ)-d)<(d:ℝ)*((k:ℝ)-1) := by
    dsimp [β]
    nlinarith only [hdn,hkc,mul_nonneg (sub_nonneg.mpr hdn) hkc]
  obtain ⟨D,_,hD⟩ := uniform_drift hd hk hb hc
  have lower (i : ℕ) : (i:ℝ)+1≤weight β i := by
    have a : (i:ℝ)+1≤(i+1).factorial := by exact_mod_cast Nat.self_le_factorial (i+1)
    have b : (1:ℝ)≤(i+1).factorial := by exact_mod_cast (i+1).factorial_pos
    exact a.trans (by simpa [weight] using Real.rpow_le_rpow_of_exponent_le b hb.le)
  have col (y : ℕ) : ∃ b : ℕ, ∀ i : ℕ, b ≤ i → transition k d i y=0 := by
    refine ⟨y+k*d+1,fun i hi => ?_⟩
    exact le_antisymm (le_of_not_gt (fun p => by have := (transition_support p).2; omega)) (transition_nonneg ..)
  obtain ⟨π,hπ⟩ := stationary_exists (transition_kernel k d) col lower
    (fun x => (expect_finite k d x _).summable) hD
  exact ⟨recurrent_of_stationary (transition_kernel k d) hπ (stationary_positive hd hk hπ),π,hπ⟩

theorem factorial_moment {k d : ℕ} (hd : 2≤d) (hk : d<k) {β : ℝ}
    (hb : 1<β) (hc : β*((k:ℝ)-d)<(d:ℝ)*((k:ℝ)-1))
    {π : ℕ→ℝ} (hπ : Stationary (transition k d) π) :
    Summable (fun x => π x * weight β x) := by
  obtain ⟨D,hD,dr⟩ := uniform_drift hd hk hb hc
  exact (stationary_moment (transition_kernel k d) hπ (fun x => (weight_pos β x).le) hD
    (fun x => (expect_finite k d x _).summable) dr).1

end MatrixWidth
