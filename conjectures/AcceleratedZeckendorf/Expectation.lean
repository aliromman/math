module

public import conjectures.AcceleratedZeckendorf.Drift
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace AcceleratedZeckendorf
open Finset

private def aggregate (p : Position) (f : Rule → ℕ → ℝ) : ℝ :=
  ∑ r ∈ rules p, ∑ j ∈ range (cap p r), f r j

private theorem aggregate_const (p : Position) (c : ℝ) :
    aggregate p (fun _ _ => c) = (moves p : ℝ)*c := by
  simp only [aggregate, sum_const, card_range, nsmul_eq_mul, moves, Nat.cast_sum, sum_mul]

private theorem aggregate_batch (p : Position) :
    aggregate p (fun _ j => ((j+1 : ℕ) : ℝ)) = (batches p : ℝ) := by
  simp [aggregate, batches]

private theorem aggregate_mono {p : Position} {f g : Rule → ℕ → ℝ}
    (h : ∀ r ∈ rules p, ∀ j < cap p r, f r j ≤ g r j) : aggregate p f ≤ aggregate p g :=
  sum_le_sum fun r hr => sum_le_sum fun j hj => h r hr j (mem_range.mp hj)

private theorem aggregate_add_mul (p : Position) (f g : Rule → ℕ → ℝ) (c : ℝ) :
    aggregate p (fun r j => f r j+c*g r j) = aggregate p f + c*aggregate p g := by
  simp [aggregate, sum_add_distrib, mul_sum]

private theorem log_step {w v d : ℕ} (h : w+d≤v) :
    Real.log (1+w) + (d:ℝ)/(1+v) ≤ Real.log (1+v) := by
  have hw : (0:ℝ)<1+w := by positivity
  have hv : (0:ℝ)<1+v := by positivity
  have ht := Real.log_le_sub_one_of_pos (div_pos hw hv)
  rw [Real.log_div hw.ne' hv.ne'] at ht
  have hd : (1+(w:ℝ))/(1+v) + (d:ℝ)/(1+v) ≤ 1 := by
    rw [← add_div, div_le_one hv]
    exact_mod_cast (show 1+w+d ≤ 1+v by omega)
  linarith

private theorem work_pos (p : Position) (hm : moves p ≠ 0) : 1 ≤ work p := by
  induction p using Multiset.induction_on with
  | empty => simp [moves, rules] at hm
  | cons i p _ => cases i <;> simp [work, weight] <;> omega

private noncomputable def fee (p : Position) : ℝ :=
  2*(scale (mass p) : ℝ)*Real.log (1+work p)

private theorem fee_nonneg (p : Position) : 0≤fee p := by
  exact mul_nonneg (by positivity) (Real.log_nonneg (by simp))

private theorem amortized (p : Position) (hm : moves p≠0) :
    (moves p:ℝ)+aggregate p (fun r j => fee (play p r (j+1))) ≤ (moves p:ℝ)*fee p := by
  let c := 2*(scale (mass p):ℝ)/(1+work p)
  have h : aggregate p (fun r j => fee (play p r (j+1)) + c*((j+1:ℕ):ℝ)) ≤
      aggregate p (fun _ _ => fee p) := by
    apply aggregate_mono
    intro r _ j hj
    have hk : j+1≤cap p r := hj
    have hstep := log_step (play_work hk)
    dsimp [fee]
    rw [play_mass hk]
    calc
      _ = 2*(scale (mass p):ℝ)*(Real.log (1+work (play p r (j+1)))+((j+1:ℕ):ℝ)/(1+work p)) := by
        dsimp [c]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hstep (by positivity)
  rw [aggregate_add_mul, aggregate_batch, aggregate_const] at h
  have hd : (work p:ℝ)*(moves p:ℝ) ≤ (scale (mass p):ℝ)*(batches p:ℝ) := by
    exact_mod_cast work_drift p
  have hone : (1:ℝ)≤work p := by exact_mod_cast work_pos p hm
  have hK : (moves p:ℝ) ≤ c*(batches p:ℝ) := by
    dsimp [c]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hone (Nat.cast_nonneg (α:=ℝ) (moves p))]
  linarith

theorem turns_nonneg (h : ℕ) (p : Position) : 0≤turns h p := by
  induction h generalizing p with
  | zero => exact le_rfl
  | succ h ih =>
    rw [turns]
    split
    · exact le_rfl
    · exact add_nonneg (by norm_num) (div_nonneg (sum_nonneg fun r _ => sum_nonneg fun j _ =>
        ih (play p r (j+1))) (by positivity))

private theorem turns_le_fee (h : ℕ) (p : Position) : turns h p ≤ fee p := by
  induction h generalizing p with
  | zero => exact fee_nonneg p
  | succ h ih =>
    rw [turns]
    split
    · exact fee_nonneg p
    next hm =>
      have hm' : (0:ℝ)<moves p := by exact_mod_cast Nat.pos_of_ne_zero hm
      have h₁ := aggregate_mono (p:=p) (f:=fun r j => turns h (play p r (j+1)))
        (g:=fun r j => fee (play p r (j+1))) (fun r _ j _ => ih (play p r (j+1)))
      have h₂ := amortized p hm
      change 1+aggregate p _/(moves p:ℝ)≤_
      rw [← le_sub_iff_add_le', div_le_iff₀ hm']
      linarith

/-- The finite truncations are exact once their horizon reaches the starting potential. -/
theorem turns_stable (h : ℕ) (p : Position) (hh : work p ≤ h) : turns (h+1) p = turns h p := by
  induction h generalizing p with
  | zero =>
    have hm : moves p=0 := by
      by_contra h
      have := work_pos p h
      omega
    simp [turns, hm]
  | succ h ih =>
    conv_lhs => rw [turns]
    conv_rhs => rw [turns]
    split
    · rfl
    · congr 2
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro j hj
      have hw := play_work (p:=p) (r:=r) (k:=j+1) (mem_range.mp hj)
      exact ih _ (by omega)

private theorem total_repeat (f : ℕ → ℕ) (n : ℕ) :
    total f (Multiset.replicate n 0) = n*f 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [Multiset.replicate_succ, ih, Nat.succ_mul, add_comm]

private theorem turns_mono (p : Position) : Monotone (fun h => turns h p) := by
  apply monotone_nat_of_le_succ
  intro h
  induction h generalizing p with
  | zero => exact turns_nonneg 1 p
  | succ h ih =>
    conv_lhs => rw [turns]
    conv_rhs => rw [turns]
    split
    · rfl
    · exact add_le_add le_rfl (div_le_div_of_nonneg_right
        (aggregate_mono (p:=p) (f:=fun r j => turns h (play p r (j+1)))
          (g:=fun r j => turns (h+1) (play p r (j+1))) (fun r _ j _ => ih _))
        (Nat.cast_nonneg (moves p)))

/-- By this horizon every game has ended, so the supremum equals an actual finite expectation. -/
theorem mean_exact (n : ℕ) : mean n = turns (5*n) (Multiset.replicate n 0) := by
  let p := Multiset.replicate n 0
  have hw : work p=5*n := by
    unfold p work
    rw [total_repeat]
    exact Nat.mul_comm _ _
  have ht (k : ℕ) : turns (5*n+k) p = turns (5*n) p := by
    induction k with
    | zero => rfl
    | succ k ih => exact (turns_stable (5*n+k) p (by rw [hw]; omega)).trans ih
  have hb (h : ℕ) : turns h p ≤ turns (5*n) p := by
    by_cases hh : h≤5*n
    · exact turns_mono p hh
    · convert (ht (h-5*n)).le using 2; omega
  exact le_antisymm (csSup_le (Set.range_nonempty _) (Set.forall_mem_range.mpr hb))
    (le_csSup ⟨_, Set.forall_mem_range.mpr hb⟩ (Set.mem_range_self (5*n)))

theorem mean_nonneg (n : ℕ) : 0≤mean n := by
  rw [mean_exact]
  exact turns_nonneg _ _

theorem mean_bound (n : ℕ) : mean n ≤ 2*(scale n:ℝ)*Real.log (1+5*n) := by
  have h : mean n ≤ fee (Multiset.replicate n 0) := (mean_exact n).le.trans (turns_le_fee _ _)
  have h₁ : mass (Multiset.replicate n 0)=n := by
    unfold mass
    rw [total_repeat]
    exact Nat.mul_one n
  have h₂ : work (Multiset.replicate n 0)=5*n := by
    unfold work
    rw [total_repeat]
    exact Nat.mul_comm _ _
  simpa [fee, h₁, h₂] using h

end AcceleratedZeckendorf
