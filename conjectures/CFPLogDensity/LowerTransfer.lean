module

public import conjectures.CFPLogDensity.Statement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section
namespace CFPLogDensity
open Finset Filter

def fullShells (S : Set ℕ) : Set ℕ := {k | ∀ x : ℕ, 2^k ≤ x → x < 2^(k+1) → x ∈ S}

noncomputable def shellCount (S : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((range n).filter (· ∈ fullShells S)).card

private theorem log_step (n : ℕ) (hn : 0 < n) :
    Real.log (n+1:ℝ) - Real.log n ≤ (n:ℝ)⁻¹ ∧
    (n+1:ℝ)⁻¹ ≤ Real.log (n+1:ℝ) - Real.log n := by
  have h : 0 < (n:ℝ) := by exact_mod_cast hn
  have p : 0 < (n:ℝ)+1 := by linarith
  have lo := Real.log_le_sub_one_of_pos (div_pos p h)
  have hi := Real.one_sub_inv_le_log_of_pos (div_pos p h)
  rw [Real.log_div p.ne' h.ne'] at lo hi
  constructor
  · convert lo using 1
    field_simp
    ring
  · convert hi using 1
    rw [inv_div]
    field_simp
    ring

private theorem logs_telescope (a b : ℕ) (ha : 0<a) (hab : a≤b) :
    Real.log b - Real.log a ≤ ∑ x ∈ Ico a b, (x:ℝ)⁻¹ ∧
    (∑ x ∈ Ico (a+1) (b+1), (x:ℝ)⁻¹) ≤ Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, Finset.sum_Ico_succ_top (Nat.succ_le_succ hb)]
    have step := log_step b (ha.trans_le hb)
    push_cast
    constructor <;> linarith [ih.1,ih.2,step.1,step.2]

private theorem dyadic_harmonic (k : ℕ) :
    Real.log 2 ≤ ∑ x ∈ Ico ((2:ℕ)^k) (2^(k+1)), (x:ℝ)⁻¹ := by
  have h := (logs_telescope (2^k) (2^(k+1)) (by positivity) (Nat.pow_le_pow_right (by decide) (by omega))).1
  simpa [Real.log_pow,add_mul] using h

private theorem mass_upper_of_pos (S : Set ℕ) (n : ℕ) (hn : 0<n) : logMass S n ≤ 1+Real.log n := by
  classical
  have sub : (Icc 1 n).filter (· ∈ S) ⊆ Icc 1 n := Finset.filter_subset ..
  apply (Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)).trans
  have split := Finset.sum_Ico_consecutive (fun x : ℕ => (x:ℝ)⁻¹) (show 1≤2 by decide) (show 2≤n+1 by omega)
  have plus := (logs_telescope 1 n (by decide) hn).2
  simp only [Nat.cast_one,Real.log_one,sub_zero] at plus
  simp only [show Ico 1 2={1} by decide,Finset.sum_singleton,Nat.cast_one,inv_one] at split
  rw [← Finset.Ico_add_one_right_eq_Icc, ← split]
  linarith

/-- Each full dyadic interval contributes at least log 2 to the logarithmic mass. -/
theorem shell_count_log_mass (S : Set ℕ) (n : ℕ) :
    (shellCount S n : ℝ)*Real.log 2 ≤ logMass S (2^n) := by
  classical
  let f (x : ℕ) : ℝ := if x∈S then (x:ℝ)⁻¹ else 0
  have nonneg (x) : 0≤f x := by dsimp [f]; split <;> positivity
  have sum : (shellCount S n : ℝ)*Real.log 2 ≤ ∑ x ∈ Ico 1 (2^n), f x := by
    induction n with
    | zero => simp [shellCount]
    | succ n ih =>
      have hn : 1 ≤ (2:ℕ)^n := Nat.one_le_pow _ _ (by decide)
      rw [← Finset.sum_Ico_consecutive f hn (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))]
      by_cases h : n∈fullShells S
      · have eq : (∑ x ∈ Ico ((2:ℕ)^n) (2^(n+1)), f x) = ∑ x ∈ Ico ((2:ℕ)^n) (2^(n+1)), (x:ℝ)⁻¹ :=
          Finset.sum_congr rfl fun x hx => by simp [f,h x (mem_Ico.mp hx).1 (mem_Ico.mp hx).2]
        have ct : shellCount S (n+1)=shellCount S n+1 := by simp [shellCount,Finset.range_add_one,Finset.filter_insert,h]
        rw [ct,Nat.cast_add,Nat.cast_one,add_mul,one_mul,eq]
        exact add_le_add ih (dyadic_harmonic n)
      · have ct : shellCount S (n+1)=shellCount S n := by simp [shellCount,Finset.range_add_one,Finset.filter_insert,h]
        rw [ct]
        exact ih.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun x _ => nonneg x))
  rw [logMass,Finset.sum_filter]
  exact sum.trans (Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by
    exact Finset.mem_Icc.mpr ⟨(mem_Ico.mp hx).1,(mem_Ico.mp hx).2.le⟩) (fun x _ _ => nonneg x))

private theorem density_ratio_bounded (S : Set ℕ) :
    atTop.IsBoundedUnder (·≤·) (fun N : ℕ => logMass S N / Real.log N) := by
  refine ⟨2,?_⟩
  change ∀ᶠ n : ℕ in atTop, logMass S n / Real.log n ≤ 2
  have tend := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [tend.eventually_ge_atTop 1,eventually_ge_atTop 1] with n h hn
  change 1 ≤ Real.log n at h
  apply (div_le_iff₀ (by linarith : 0 < Real.log n)).mpr
  linarith [mass_upper_of_pos S n hn]

/-- A strict common density bound gives an eventual bound for every dyadic shell count. -/
theorem eventual_shell_counts {ι : Type*} [Finite ι] (S : ι → Set ℕ) {c C : ℝ} (h : ∀ i, sampledDensity (S i) < c) (hC : c<C) :
    ∀ᶠ n : ℕ in atTop, ∀ i, 1+(shellCount (S i) n:ℝ) ≤ C*n := by
  let b := (c+C)/2
  have cb : c<b := by dsimp [b]; linarith
  have bC : b<C := by dsimp [b]; linarith
  have powers : Tendsto (fun n : ℕ => (2:ℕ)^n) atTop atTop := tendsto_atTop.mpr fun n =>
    (eventually_ge_atTop n).mono fun k hk => hk.trans (Nat.lt_pow_self (by decide)).le
  have large : ∀ᶠ n : ℕ in atTop, 1/(C-b) ≤ (n:ℝ) := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  apply eventually_all.mpr
  intro i
  have density := eventually_lt_of_limsup_lt ((h i).trans cb) (density_ratio_bounded (S i))
  have logpos : 0<Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [powers.eventually density, large, eventually_ge_atTop 1] with n hsum grow hn
  change logMass (S i) (2^n) / Real.log ((2^n:ℕ):ℝ) < b at hsum
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hsum
  have posN : 0<(n:ℝ) := by exact_mod_cast hn
  have above := (div_lt_iff₀ (mul_pos posN logpos)).mp hsum
  have cnt := shell_count_log_mass (S i) n
  have small : (shellCount (S i) n:ℝ) ≤ b*n := by
    apply (le_of_mul_le_mul_right _ logpos)
    exact cnt.trans (by simpa [mul_assoc] using above.le)
  have slack := (div_le_iff₀ (sub_pos.mpr bC)).mp grow
  nlinarith

private theorem square_le_pow (t : ℕ) (ht : 4≤t) : t*t ≤ 2^t := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [pow_succ]; nlinarith [Nat.mul_le_mul (by omega : 4≤n) (by omega : 1≤n)]

/-- Dense intervals at scale Kt contain a common color throughout the shorter shell interval. -/
theorem dense_to_full_shells {ι : Type*} (S : ι → Set ℕ) (K0 K : ℕ) (h0 : 0<K0) (hK : 1≤K)
    (dense : ∀ᶠ j : ℕ in atTop, ∃ i, ∀ x : ℕ, K0*2^j*(j+1) ≤ x → x ≤ (2^j)^2/K0 → x∈S i) :
    ∀ᶠ t : ℕ in atTop, ∃ i, ∀ k : ℕ, (K+1)*t≤k → k<(2*K-1)*(t+1) → k∈fullShells (S i) := by
  have scale : Tendsto (fun t : ℕ => K*t) atTop atTop := tendsto_atTop.mpr fun n =>
    (eventually_ge_atTop n).mono fun t ht => ht.trans (by simpa using Nat.mul_le_mul_right t hK)
  filter_upwards [scale.eventually dense,eventually_ge_atTop (K0*(K+1)),eventually_ge_atTop (2*K+K0),eventually_ge_atTop 4] with t denseT t1 t2 t4
  obtain ⟨i,hi⟩ := denseT
  refine ⟨i,fun k low high x hx hy => hi x ?_ ?_⟩
  · have polynomial : K0*(K*t+1) ≤ t*t := by nlinarith [Nat.mul_le_mul_right t t1]
    have exp : K*t+t≤k := by simpa [Nat.add_mul] using low
    calc
      K0*2^(K*t)*(K*t+1) = 2^(K*t)*(K0*(K*t+1)) := by ring
      _ ≤ 2^(K*t)*2^t := Nat.mul_le_mul_left _ (polynomial.trans (square_le_pow t t4))
      _ = 2^(K*t+t) := (pow_add ..).symm
      _ ≤ 2^k := Nat.pow_le_pow_right (by decide) exp
      _ ≤ x := hx
  · have sub : 2*K-1+1=2*K := by omega
    have ex : k+1+K0 ≤ 2*(K*t) := by nlinarith [congrArg (· * (t+1)) sub]
    apply (Nat.le_div_iff_mul_le h0).mpr
    calc
      x*K0 ≤ 2^(k+1)*2^K0 := Nat.mul_le_mul hy.le (Nat.lt_pow_self (by decide)).le
      _ = 2^(k+1+K0) := (pow_add ..).symm
      _ ≤ 2^(2*(K*t)) := Nat.pow_le_pow_right (by decide) ex
      _ = (2^(K*t))^2 := by rw [Nat.mul_comm 2 (K*t),pow_mul]

end CFPLogDensity
