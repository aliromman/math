module

public import conjectures.LeanderLinusson.Paths
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace LeanderLinusson
open Filter Finset Function
open scoped Topology

private def errorConstant (m r : ℕ) :=
  (m.descFactorial r + 1) * (2*m).descFactorial (2*r) * (2*m)^2

private theorem normalized_error {n r : ℕ} (m : ℕ) (b : Fin r × Bool ↪ Fin n) (hn : 0<n) :
    |((pathSamples m b).card : ℝ)/(n:ℝ)^(2*m-2*r) - m.descFactorial r| ≤
      (errorConstant m r : ℝ)/n := by
  let K := m.descFactorial r
  let B := (2*m).descFactorial (2*r)*(2*m)^2
  let D := 2*m-2*r
  let E := (pathSamples m b).card
  let C := (collisions (S := Fin m × Bool) b).card
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hD : 0 < (n:ℝ)^D := pow_pos hN _
  have hs : E ≤ K*n^D+C ∧ K*n^D ≤ E+K*C := by
    simpa [K,E,C,D,Fintype.card_embedding_eq] using sample_bounds m b
  have hc : C*n ≤ B*n^D := by
    simpa [C,B,D,Fintype.card_embedding_eq,Nat.mul_comm] using collisions_scaled (S := Fin m × Bool) b
  have h₁ : (E:ℝ) ≤ (K:ℝ)*(n:ℝ)^D+C := by exact_mod_cast hs.1
  have h₂ : (K:ℝ)*(n:ℝ)^D ≤ E+(K:ℝ)*C := by exact_mod_cast hs.2
  have h₃ : (C:ℝ)*n ≤ (B:ℝ)*(n:ℝ)^D := by exact_mod_cast hc
  have hb : (C:ℝ)/(n:ℝ)^D ≤ (B:ℝ)/n := (div_le_div_iff₀ hD hN).mpr h₃
  have hd : |(E:ℝ) - K*(n:ℝ)^D| ≤ ((K:ℝ)+1)*C := by
    apply abs_le.mpr
    constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) C,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) K) (Nat.cast_nonneg (α:=ℝ) C)]
  change |(E:ℝ)/(n:ℝ)^D-K| ≤ _
  calc
    _ = |(E:ℝ) - K*(n:ℝ)^D| / (n:ℝ)^D := by
      calc
        _ = |((E:ℝ)-K*(n:ℝ)^D)/(n:ℝ)^D| := by rw [sub_div,mul_div_cancel_right₀ _ hD.ne']
        _ = _ := by rw [abs_div,abs_of_pos hD]
    _ ≤ (((K:ℝ)+1)*C)/(n:ℝ)^D := div_le_div_of_nonneg_right hd hD.le
    _ ≤ ((K:ℝ)+1)*((B:ℝ)/n) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by unfold errorConstant K B; push_cast; ring

private theorem raw_limit {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (m : ℕ) {r : ℕ}
    (b : ∀ n, Fin r × Bool ↪ Fin (N n)) :
    Tendsto (fun n ↦ ((pathSamples m (b n)).card : ℝ)/(N n:ℝ)^(2*m-2*r))
      atTop (𝓝 (m.descFactorial r : ℝ)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_const_div_atTop_nhds_zero_nat (errorConstant m r : ℝ)).comp hN)
    (Eventually.of_forall fun _ ↦ dist_nonneg)
    (by filter_upwards [hN.eventually_ge_atTop 1] with n hn
        simpa [Real.dist_eq] using normalized_error m (b n) hn)

private def noTerminals (n : ℕ) : Fin 0 × Bool ↪ Fin n :=
  ⟨fun i ↦ i.1.elim0,fun i ↦ i.1.elim0⟩

@[simp] private theorem pathSamples_zero (n m : ℕ) :
    pathSamples m (noTerminals n) = samples (Fin n) m := by
  classical
  ext g
  simp [samples]

/-- For fixed `m`, the probability of `r` specified directed connections on
distinct terminals, multiplied by the vertex count to power `2*r`, tends to
the falling factorial of `m` of order `r`. -/
theorem disjoint_paths_limit {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (m : ℕ) {r : ℕ}
    (b : ∀ n, Fin r × Bool ↪ Fin (N n)) :
    Tendsto (fun n ↦ (N n:ℝ)^(2*r) * (((pathSamples m (b n)).card : ℝ)/
        (samples (Fin (N n)) m).card)) atTop (𝓝 (m.descFactorial r : ℝ)) := by
  by_cases h : r ≤ m
  · have den : Tendsto (fun n ↦ ((samples (Fin (N n)) m).card : ℝ)/(N n:ℝ)^(2*m))
        atTop (𝓝 1) := by
      simpa using raw_limit hN m (fun n ↦ noTerminals (N n))
    have div := (raw_limit hN m b).div den one_ne_zero
    simp only [div_one] at div
    apply div.congr'
    filter_upwards [hN.eventually_ge_atTop 1] with n hn
    have hpos : (N n:ℝ) ≠ 0 := by exact_mod_cast (show N n ≠ 0 by omega)
    have hp : (N n : ℝ)^(2*m) = (N n : ℝ)^(2*m-2*r)*(N n : ℝ)^(2*r) := by
      rw [← pow_add,Nat.sub_add_cancel (by omega)]
    simp only [Pi.div_apply]
    rw [hp]
    by_cases hd : (samples (Fin (N n)) m).card=0
    · simp [hd]
    · have hd' : (((samples (Fin (N n)) m).card : ℝ))≠0 := by exact_mod_cast hd
      field_simp [hpos,hd']
  · have hmr : m < r := Nat.lt_of_not_ge h
    have emp (n : ℕ) : (pathSamples m (b n)).card = 0 := by
      have hc := collisions_empty (S:=Fin m × Bool) (b n)
        (by simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] using Nat.mul_le_mul_right 2 hmr.le)
      have hb := (sample_bounds m (b n)).1
      simpa [Fintype.card_embedding_eq,Nat.descFactorial_of_lt hmr,hc] using hb
    simp [emp,Nat.descFactorial_of_lt hmr]

end LeanderLinusson
