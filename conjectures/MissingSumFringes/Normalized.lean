module

public import conjectures.MissingSumFringes.WindowBound
import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
namespace MissingSumFringes
open Finset
open scoped Classical Pointwise

/-- Prefixes ending at their last gap, with their first element fixed at zero. -/
def normStrings (m t : ℕ) :=
  (range t).powerset.filter fun A => (missing t A).card=m ∧
    (t=0 ∨ t-1∈missing t A) ∧ (t=0 ∨ 0∈A)

noncomputable def normWindow (m t : ℕ) : ℝ := ((normStrings m t).card:ℝ)/(2:ℝ)^t

theorem normWindow_le (m t : ℕ) : normWindow m t≤window m t := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have inc : normStrings m t ⊆ (range t).powerset.filter fun A =>
      (missing t A).card=m ∧ (t=0 ∨ t-1∈missing t A) := by
    intro A hA
    exact mem_filter.mpr ⟨(mem_filter.mp hA).1,(mem_filter.mp hA).2.1,(mem_filter.mp hA).2.2.1⟩
  exact_mod_cast card_mono inc

private theorem normStrings_sparse {m t : ℕ} {A : Finset ℕ} (ha : A∈normStrings m t) :
    A.card≤t-m := by
  obtain ⟨sub,hm,_,first⟩ := mem_filter.mp ha
  have inc : A⊆range t \ missing t A := by
    intro x hx
    have hl := mem_powerset.mp sub hx
    refine mem_sdiff.mpr ⟨hl,?_⟩
    intro h
    apply (mem_sdiff.mp h).2
    rcases first with rfl|first
    · simp at hl
    · exact mem_add.mpr ⟨0,first,x,hx,zero_add _⟩
  have bound := card_mono inc
  rw [card_sdiff_of_subset (show missing t A⊆range t from sdiff_subset),card_range,hm] at bound
  exact bound

private theorem sparse_mass (m t : ℕ) : normWindow m t≤(8:ℝ)^(t-m)*(9/16:ℝ)^t := by
  let S := normStrings m t
  have markov : (S.card:ℝ)≤ ∑ A∈S, (8:ℝ)^(t-m)*(1/8:ℝ)^A.card := by
    have each : ∀ A∈S, (1:ℝ)≤8^(t-m)*(1/8:ℝ)^A.card := by
      intro A hA
      rw [one_div,inv_pow,← div_eq_mul_inv,le_div_iff₀ (by positivity),one_mul]
      exact pow_le_pow_right₀ (by norm_num) (normStrings_sparse hA)
    simpa using sum_le_sum each
  have all := sum_le_sum_of_subset_of_nonneg
    (show S⊆(range t).powerset from filter_subset ..)
    (f:=fun A : Finset ℕ => (1/8:ℝ)^A.card) (fun _ _ _ => by positivity)
  have gen : (∑ A∈(range t).powerset, (1/8:ℝ)^A.card)=(9/8:ℝ)^t := by
    simpa only [one_pow,mul_one,card_range,show (1/8:ℝ)+1=9/8 by norm_num] using sum_pow_mul_eq_add_pow (1/8:ℝ) 1 (range t)
  rw [← mul_sum] at markov
  have pop := markov.trans (mul_le_mul_of_nonneg_left (all.trans_eq gen) (by positivity))
  change (S.card:ℝ)/(2:ℝ)^t≤_
  apply (div_le_iff₀ (by positivity)).mpr
  rwa [mul_assoc,←mul_pow,show (9/16:ℝ)*2=9/8 by norm_num]

/-- Fixing zero makes the number of missing sums decay faster than 2^(-m/2).
The exponent also gives a summable bound on the last gap. -/
theorem normWindow_bound : ∃ K : ℝ, 0<K ∧ ∀ m t : ℕ,
    normWindow m t≤K*(2:ℝ)^(-(m:ℝ)/2-(t:ℝ)/256) := by
  obtain ⟨C,hC,uw⟩ := window_bound (1/256) (by norm_num)
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right ..),?_⟩
  intro m t
  by_cases mt : m≤t
  · by_cases apart : (t:ℝ)/16≤(t:ℝ)-m
    · apply (normWindow_le m t).trans ((uw m t).trans ?_)
      apply mul_le_mul (le_max_left ..) (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
        (by positivity) (le_trans hC.le (le_max_left ..))
      linarith
    · have fraction : (9/16:ℝ)≤(2:ℝ)^(-3/4:ℝ) := by
        apply (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (z:=4) (by norm_num)).mp
        rw [←Real.rpow_mul (by norm_num)]
        norm_num
      have arith : 3*((t-m:ℕ):ℝ)+(-3/4:ℝ)*t ≤ -(m:ℝ)/2-(t:ℝ)/256 := by
        rw [Nat.cast_sub mt]
        have tr : (m:ℝ)≤t := by exact_mod_cast mt
        linarith
      have eight : (8:ℝ)^(t-m)=(2:ℝ)^(3*((t-m:ℕ):ℝ)) := by
        rw [Real.rpow_mul (by norm_num),Real.rpow_natCast]
        norm_num
      calc
        normWindow m t ≤ (8:ℝ)^(t-m)*(9/16:ℝ)^t := sparse_mass m t
        _ ≤ (2:ℝ)^(3*((t-m:ℕ):ℝ))*((2:ℝ)^(-3/4:ℝ))^t := by
          rw [←eight]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) fraction _) (by positivity)
        _ = (2:ℝ)^(3*((t-m:ℕ):ℝ)+(-3/4:ℝ)*t) := by
          rw [Real.rpow_add (by norm_num),Real.rpow_mul (by norm_num) (-3/4:ℝ),Real.rpow_natCast]
        _ ≤ (2:ℝ)^(-(m:ℝ)/2-(t:ℝ)/256) := Real.rpow_le_rpow_of_exponent_le (by norm_num) arith
        _ ≤ _ := le_mul_of_one_le_left (by positivity) (le_max_right ..)
  · have empty : normStrings m t=∅ := eq_empty_iff_forall_notMem.mpr fun A ha => mt (by
      have cap := card_mono (show missing t A⊆range t from sdiff_subset)
      simpa only [card_range,(mem_filter.mp ha).2.1] using cap)
    simp only [normWindow,empty,card_empty,Nat.cast_zero,zero_div]
    exact mul_nonneg (le_trans hC.le (le_max_left ..)) (by positivity)

end MissingSumFringes
