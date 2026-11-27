module

public import conjectures.WeinbergerShayevitz.Bounds
public import conjectures.WeinbergerShayevitz.Majority
import Mathlib.Tactic.Linarith

@[expose] public section
namespace WeinbergerShayevitz
open Finset Filter
open scoped BigOperators

theorem majority_upper (n : ℕ) (hn : 12 ≤ n) : best n (3/4) 1 ≤ 7816/10000 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨g,v,hv⟩ := pad_alignment (3/4) (majority 12 0) (fun x ↦ (weight 12 x:ℝ)) k
  rw [majority_alignment] at hv
  let z := channel (3/4) (12+k) (signBit ∘ g)
  have hg : 3845275777343/17592186044416 ≤ alignment z z := hv.symm.le.trans (alignment_le z v)
  apply (inf'_le _ (mem_univ g)).trans
  rw [guessingRatio_one]
  have hN : (4096:ℝ) ≤ 2^(12+k) := by
    calc
      _ = (2:ℝ)^12 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hn
  have hr : 4096/4097 ≤ (2:ℝ)^(12+k)/(2^(12+k)+1) := by
    apply (le_div_iff₀ (by positivity)).mpr; linarith
  have h := mul_le_mul hr hg (by norm_num) (by positivity)
  change 1-((2:ℝ)^(12+k)/(2^(12+k)+1))*alignment z z ≤ _
  linarith

/-- For every length from twelve onward, the two optimal expected ranks have a
uniform gap after normalization by the unassisted expected rank. -/
theorem finite_gap {n : ℕ} (hn : 12 ≤ n) :
    best n (3/4) 1 + 1/10000 ≤ guessingRatio 1 (channel (3/4) n (greedy n)) := by
  linarith [greedy_lower n,majority_upper n hn]

theorem resolution : ¬ Conjecture := by
  intro h
  have he := h (3/4) (by norm_num) 1 (by norm_num)
  have upper : limsup (fun n ↦ best n (3/4) 1) atTop ≤ 7816/10000 :=
    limsup_le_of_le (isCoboundedUnder_le_of_le _ best_nonneg)
      (eventually_atTop.mpr ⟨12,majority_upper⟩)
  have lower : 7817/10000 ≤ limsup (fun n ↦ guessingRatio 1 (channel (3/4) n (greedy n))) atTop :=
    le_limsup_of_le (isBoundedUnder_of ⟨1,fun _ ↦ ratio_le_one _⟩) fun b hb ↦ by
      obtain ⟨n,hn⟩ := hb.exists
      exact (greedy_lower n).trans hn
  rw [he] at lower
  linarith

/-- info: 'WeinbergerShayevitz.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'WeinbergerShayevitz.finite_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_gap

end WeinbergerShayevitz
