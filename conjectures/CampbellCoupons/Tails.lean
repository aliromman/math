module

public import conjectures.CampbellCoupons.Statement
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace CampbellCoupons
open Finset Filter
open scoped Topology Polynomial

/-- The count of one coupon type has the binomial distribution. -/
private theorem fixed_count {k : ℕ} (T d : ℕ) (i : Fin k) :
    (univ.filter fun w : Fin T → Fin k => counts w i = d).card =
      (k - 1) ^ (T - d) * T.choose d := by
  classical
  let g (j : Fin k) : ℕ[X] := if j = i then Polynomial.X else 1
  have hg : ∑ j, g j = Polynomial.X + Polynomial.C (k-1 : ℕ) := by
    rw [← univ.add_sum_erase (f := g) (mem_univ i)]
    have h : ∀ j ∈ univ.erase i, g j = 1 := fun j hj => by
      simp [g, (mem_erase.mp hj).1]
    rw [sum_congr rfl h]
    simp [g]
  have hw (w : Fin T → Fin k) : (∏ j, g (w j)) = Polynomial.X^(counts w i) := by
    simp [g, counts, prod_ite]
  have H := congrArg (fun p : ℕ[X] => p.coeff d)
    (Fintype.prod_sum (fun (_ : Fin T) (j : Fin k) => g j))
  simp only [hg, prod_const, card_univ, Fintype.card_fin, hw, Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_pow] at H
  simpa [Finset.sum_boole, eq_comm] using H.symm

private def failed (m k T : ℕ) : Finset (Fin T → Fin k) :=
  univ.filter fun w => ∃ i, counts w i < m

private theorem partition (m k T : ℕ) : winning m k T + (failed m k T).card = k^T := by
  simpa [winning, failed] using card_filter_add_card_filter_not (s := univ)
    (p := fun w : Fin T → Fin k => ∀ i, m ≤ counts w i)

private theorem failure_upper {m k T : ℕ} (hk : 2 ≤ k) (hT : 0 < T) :
    (failed m k T).card ≤ k*m*T^m*(k-1)^T := by
  classical
  let few (i : Fin k) := univ.filter fun w : Fin T → Fin k => counts w i < m
  have hfail : failed m k T = univ.biUnion few := by ext w; simp [failed, few]
  have small (i : Fin k) : (few i).card ≤ m * (T^m*(k-1)^T) := by
    have h := sum_card_fiberwise_eq_card_filter (univ : Finset (Fin T → Fin k))
      (range m) (fun w => counts w i)
    simp only [mem_range] at h
    change (univ.filter fun w : Fin T → Fin k => counts w i < m).card ≤ _
    rw [← h]
    calc
      _ ≤ ∑ _j ∈ range m, T^m * (k-1)^T := by
        apply sum_le_sum
        intro j hj
        rw [fixed_count, mul_comm]
        apply Nat.mul_le_mul
        · exact (Nat.choose_le_pow T j).trans (Nat.pow_le_pow_right hT (mem_range.mp hj).le)
        · exact Nat.pow_le_pow_right (by omega) (Nat.sub_le ..)
      _ = _ := by simp
  rw [hfail]
  calc
    _ ≤ ∑ i, (few i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin k, m*(T^m*(k-1)^T) := sum_le_sum fun i _ => small i
    _ = _ := by simp [Nat.mul_assoc]

private theorem failure_lower {m k : ℕ} (hm : 0 < m) (T : ℕ) :
    k^T ≤ (failed m (k+1) T).card := by
  have h := fixed_count T 0 (0 : Fin (k+1))
  simp only [Nat.add_sub_cancel, Nat.sub_zero, Nat.choose_zero_right, mul_one] at h
  rw [← h]
  apply card_le_card
  intro w hw
  refine mem_filter.mpr ⟨mem_univ _, 0, ?_⟩
  simpa only [(mem_filter.mp hw).2] using hm

/-- For every fixed pair of requirements, the conjectured order holds strictly at late times. -/
theorem eventual_comparison {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) :
    ∀ᶠ T : ℕ in atTop, success (m-1) (k+1) T < success m k T := by
  let r : ℝ := ((k:ℝ)-1)*(k+1)/(k:ℝ)^2
  have K : (2:ℝ) ≤ k := by exact_mod_cast hk
  have kp : (0:ℝ) < k := by linarith
  have km : (0:ℝ) ≤ (k:ℝ)-1 := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hlt : r < 1 := by
    dsimp [r]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have lim := (tendsto_pow_const_mul_const_pow_of_lt_one m hr hlt).const_mul ((k:ℝ)*m)
  have small : ∀ᶠ t : ℕ in atTop, ((k:ℝ)*m)*((t:ℝ)^m*r^t) < 1 :=
    lim.eventually_lt_const (by simp)
  filter_upwards [small, eventually_ge_atTop 1] with T ht hT
  have u := failure_upper (m := m) hk hT
  have l := failure_lower (m := m-1) (k := k) (by omega) T
  have p := partition m k T
  have q := partition (m-1) (k+1) T
  have eu : ((failed m k T).card : ℝ) ≤ (k:ℝ)*m*T^m*((k:ℝ)-1)^T := by
    have step : (((k - 1 : ℕ) : ℝ)) = (k:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [← step]
    exact_mod_cast u
  have el : (k:ℝ)^T ≤ (failed (m-1) (k+1) T).card := by exact_mod_cast l
  have ep : (winning m k T : ℝ) + (failed m k T).card = (k:ℝ)^T := by exact_mod_cast p
  have eq : (winning (m-1) (k+1) T : ℝ) + (failed (m-1) (k+1) T).card = (k+1:ℝ)^T :=
    by exact_mod_cast q
  have bound : (k:ℝ)*m*T^m*((k:ℝ)-1)^T*(k+1)^T < (k:ℝ)^T*(k:ℝ)^T := by
    dsimp only [r] at ht
    rw [div_pow, mul_pow, ← pow_mul] at ht
    field_simp at ht
    simpa [pow_mul, pow_two, mul_assoc, mul_left_comm, mul_comm] using ht
  have strict : ((failed m k T).card : ℝ) * (k+1)^T <
      ((failed (m-1) (k+1) T).card : ℝ) * (k:ℝ)^T :=
    (mul_le_mul_of_nonneg_right eu (by positivity)).trans_lt
      (bound.trans_le (mul_le_mul_of_nonneg_right el (by positivity)))
  unfold success
  push_cast
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [congrArg (fun z : ℝ => z*(k+1)^T) ep, congrArg (fun z : ℝ => z*(k:ℝ)^T) eq]

end CampbellCoupons
