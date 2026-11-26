module

public import conjectures.MissingSumFringes.CoreAtoms
public import conjectures.MissingSumFringes.CoreMoments
public import conjectures.MissingSumFringes.Trimming
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

private noncomputable def rate := Real.sqrt decay
private theorem rate_pos : 0<rate := Real.sqrt_pos.mpr decay_pos
private theorem rate_lt : rate<1 := by
  simpa only [rate,Real.sqrt_one] using Real.sqrt_lt_sqrt decay_pos.le decay_lt
private noncomputable def C := (decay*(1-decay))⁻¹
private theorem C_pos : 0<C := inv_pos.mpr (mul_pos decay_pos (sub_pos.mpr decay_lt))

private theorem joint_bound (n m t j s : ℕ) : joint true n m t j s ≤ C*(rate^t*rate^s) := by
  let M := max t s
  have e : joint true n m t j s ≤ C*decay^M := by
    by_cases h : M=0
    · rw [h,pow_zero,mul_one]
      calc
        _ ≤ avg (range n) (fun _ ↦ (1:ℝ)) := by apply avg_mono; intro A _; split <;> norm_num
        _ = 1 := avg_const ..
        _ ≤ C := by
          apply (le_inv_comm₀ zero_lt_one (mul_pos decay_pos (sub_pos.mpr decay_lt))).mpr
          simp only [inv_one]
          nlinarith [sq_nonneg decay,decay_lt]
    · have p : joint true n m t j s ≤ decay^(M-1)/(1-decay) := by
        rcases le_total s t with st|ts
        · apply le_trans _ (prob_far (M-1) n)
          apply prob_mono
          intro A _ ha
          rw [ha.1.2.2]
          dsimp [M] at *
          omega
        · apply le_trans _ (prob_far_right (M-1) n)
          apply prob_mono
          intro A _ ha
          rw [ha.2.2.2]
          dsimp [M] at *
          omega
      apply p.trans_eq
      rw [show M=M-1+1 by omega,pow_succ]
      unfold C
      have hd := decay_pos.ne'
      have he := (sub_pos.mpr decay_lt).ne'
      field_simp
      congr 1
  apply e.trans
  apply mul_le_mul_of_nonneg_left _ C_pos.le
  rw [←Real.sq_sqrt decay_pos.le,←pow_mul,←pow_add]
  exact pow_le_pow_of_le_one rate_pos.le rate_lt.le (by dsimp [M]; omega)

private noncomputable def weight (t : ℕ) := ((t:ℝ)+1)*rate^t
private theorem weight_nonneg (t : ℕ) : 0≤weight t := mul_nonneg (by positivity) (pow_nonneg rate_pos.le _)
private noncomputable def envelope (z : ℕ×ℕ) := (3*C)*(weight z.1*weight z.2)
private theorem envelope_summable : Summable envelope := by
  have geo := summable_geometric_of_lt_one rate_pos.le rate_lt
  have lin := summable_pow_mul_geometric_of_norm_lt_one 1
    (by simpa only [Real.norm_eq_abs,abs_of_pos rate_pos] using rate_lt : ‖rate‖<1)
  have w : Summable weight := (lin.add geo).congr fun t ↦ by dsimp [weight]; ring
  exact (Summable.mul_of_nonneg w w weight_nonneg weight_nonneg).mul_left _

private theorem cell_bound {n m t j s : ℕ} {f : Finset ℕ → ℝ}
    (bounds : ∀ A⊆range n, side true n m t A → side true (n-1) j s (reflect n A) →
      0≤f A ∧ f A≤3*((t:ℝ)+s+1)) : ‖cellWeight n m t j s f‖ ≤ envelope (t,s) := by
  have nn : 0≤cellWeight n m t j s f := by
    rw [←avg_const (range n) 0]
    apply avg_mono
    intro A hA
    split
    · next h => exact (bounds A hA h.1 h.2).1
    · rfl
  rw [Real.norm_eq_abs,abs_of_nonneg nn]
  calc
    _ ≤ (3*((t:ℝ)+s+1))*joint true n m t j s := by
      unfold joint prob avg
      rw [mul_expect]
      apply avg_mono
      intro A hA
      by_cases h : side true n m t A ∧ side true (n-1) j s (reflect n A)
      · simpa only [h,h.1,h.2,true_and,ite_true,mul_one] using (bounds A hA h.1 h.2).2
      · simp only [h,ite_false,mul_zero,le_refl]
    _ ≤ (3*((t:ℝ)+s+1))*(C*(rate^t*rate^s)) :=
      mul_le_mul_of_nonneg_left (joint_bound ..) (by positivity)
    _ ≤ _ := by
      have w : (t:ℝ)+s+1 ≤ ((t:ℝ)+1)*(s+1) := by nlinarith [Nat.cast_nonneg (α := ℝ) (t*s)]
      unfold envelope weight
      dsimp only
      have h := mul_le_mul_of_nonneg_right w (mul_nonneg (by linarith [C_pos] : 0≤3*C)
        (mul_nonneg (pow_nonneg rate_pos.le t) (pow_nonneg rate_pos.le s)))
      linarith only [h]

private theorem cell_out {n m j : ℕ} (f : Finset ℕ → ℝ) (z : ℕ × ℕ)
    (hz : z∉range (n+1) ×ˢ range (n+1)) : cellWeight n m z.1 j z.2 f=0 := by
  rw [←avg_const (range n) 0]
  apply avg_congr
  intro A _
  split
  · next h =>
      exfalso
      apply hz (mem_product.mpr ⟨mem_range.mpr ?_,mem_range.mpr ?_⟩)
      · rw [←h.1.2.2]; exact Nat.lt_succ_of_le (extent_le ..)
      · rw [←h.2.2.2]; exact Nat.lt_succ_of_le ((extent_le ..).trans (Nat.sub_le ..))
  · rfl

private theorem core_sum {n k : ℕ} (hn : 0<n) (f : Finset ℕ → ℝ) :
    coreAvg n k f = ∑ m∈range (k+1),∑' z : ℕ×ℕ,cellWeight n m z.1 (k-m) z.2 f := by
  rw [coreAvg_eq]
  change anchoredWeight n k f=_
  rw [anchored_sum hn]
  exact sum_congr rfl fun _ _ ↦ (tsum_eq_sum (cell_out f)).symm

/-- A summable bound on the two outermost missing positions permits passage from
finite words to the limiting mean of a nonnegative observable. -/
theorem core_weight_limit {f : ℕ → Finset ℕ → ℝ} {g : ℕ → ℕ → ℕ → ℕ → ℝ}
    (converges : ∀ m t j s, Tendsto (fun n ↦ cellWeight n m t j s (f n)) atTop (𝓝 (g m t j s)))
    (bounded : ∀ n, 0<n → ∀ A⊆range n, 0≤f n A ∧
      f n A≤3*((extent n A:ℝ)+extent (n-1) (reflect n A)+1)) (k : ℕ) :
    Tendsto (fun n ↦ coreAvg n k (f n)) atTop
      (𝓝 (∑ m∈range (k+1),∑' z : ℕ×ℕ,g m z.1 (k-m) z.2)) := by
  apply Tendsto.congr' (f₁ := fun n ↦ ∑ m∈range (k+1),∑' z : ℕ×ℕ,cellWeight n m z.1 (k-m) z.2 (f n))
    ((eventually_ge_atTop 1).mono fun n hn ↦ (core_sum hn _).symm)
  apply tendsto_finsetSum _
  intro m _
  apply tendsto_tsum_of_dominated_convergence envelope_summable
  · intro z; exact converges ..
  · filter_upwards [eventually_ge_atTop 1] with n hn
    intro z
    exact cell_bound (fun A hA l r ↦ by simpa only [←l.2.2,←r.2.2] using bounded n hn A hA)

theorem coreD_limit (k : ℕ) : Tendsto (fun n ↦ coreAvg n k (fun _ ↦ 1)) atTop (𝓝 (coreD (atom true) k)) := by
  apply core_weight_limit (g := fun m t j s ↦ atom true m t * atom true j s)
  · intro m t j s
    apply (joint_limit true m t j s).congr
    intro n
    apply avg_congr
    intro A _
    by_cases h : side true n m t A ∧ side true (n-1) j s (reflect n A)
    · simp only [h]
    · simp only [h,ite_false]
  · intro n _ A _
    refine ⟨by norm_num,?_⟩
    linarith [Nat.cast_nonneg (α := ℝ) (extent n A), Nat.cast_nonneg (α := ℝ) (extent (n-1) (reflect n A))]

end MissingSumFringes
