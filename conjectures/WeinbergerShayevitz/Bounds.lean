module

public import conjectures.WeinbergerShayevitz.Ranks
public import conjectures.WeinbergerShayevitz.Cube
import Mathlib.Tactic.Linarith

@[expose] public section
namespace WeinbergerShayevitz
open Finset
open scoped BigOperators

private theorem channel_bound (n : ℕ) (f : Observation n → ℝ)
    (hf : ∀ y, f y ∈ Set.Icc (-1:ℝ) 1) (x : Word n) :
    channel (3/4) n f x ∈ Set.Icc (-1:ℝ) 1 := by
  induction n with
  | zero => exact hf _
  | succ n ih =>
    have h₁ := ih (fun y ↦ f (Fin.cons (some (x 0)) y)) (fun _ ↦ hf _) (Fin.tail x)
    have h₂ := ih (fun y ↦ f (Fin.cons none y)) (fun _ ↦ hf _) (Fin.tail x)
    simp only [Set.mem_Icc,channel] at *
    constructor <;> linarith

private theorem ratio_nonneg {n : ℕ} (z : Word n → ℝ) (hz : ∀ x, z x ∈ Set.Icc (-1:ℝ) 1) :
    0 ≤ guessingRatio 1 z := by
  have hc (a t : ℕ) : 0 ≤ rankCost 1 a t := by
    unfold rankCost
    refine div_nonneg (sum_nonneg fun i _ ↦ ?_) (by positivity)
    rw [Real.rpow_one]
    positivity
  unfold guessingRatio
  apply div_nonneg _ (hc ..)
  apply expect_nonneg
  intro x _
  apply add_nonneg
  · exact mul_nonneg (by linarith [(hz x).1]) (hc ..)
  · exact mul_nonneg (by linarith [(hz x).2]) (hc ..)

theorem best_nonneg (n : ℕ) : 0 ≤ best n (3/4) 1 := by
  classical
  apply le_inf'
  intro f _
  apply ratio_nonneg
  exact channel_bound n _ (fun y ↦ by cases h : f y <;> simp [h,signBit])

theorem ratio_le_one {n : ℕ} (z : Word n → ℝ) : guessingRatio 1 z ≤ 1 := by
  have hn := alignment_le z (fun _ ↦ 0)
  have hz : alignment z (fun _ ↦ 0) = 0 := by simp [alignment,cmp]
  rw [hz] at hn
  rw [guessingRatio_one]
  have h : 0≤((2:ℝ)^n/(2^n+1))*alignment z z := mul_nonneg (by positivity) hn
  linarith

theorem greedy_lower (n : ℕ) :
    7817/10000 ≤ guessingRatio 1 (channel (3/4) n (greedy n)) := by
  let z := channel (3/4) n (greedy n)
  have hv := alignment_sq z z
  have hg : (𝔼 x, z x ^ 2) ≤ 1/7 := greedy_variance n
  have ha : alignment z z ≤ 2183/10000 := by
    nlinarith [sq_nonneg (alignment z z-2183/10000)]
  have hN : (2:ℝ)^n / (2^n+1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hA := mul_le_mul ha hN (by positivity : 0 ≤ (2:ℝ)^n/(2^n+1))
    (by norm_num : (0:ℝ) ≤ 2183/10000)
  change 7817/10000 ≤ guessingRatio 1 z
  rw [guessingRatio_one]
  linarith

/-- Extra input bits can be ignored by both the helper and the guessing order. -/
theorem pad_alignment {b : ℕ} (e : ℝ) (f : Observation b → Bool) (w : Word b → ℝ) (k : ℕ) :
    ∃ g : Observation (b+k) → Bool, ∃ v : Word (b+k) → ℝ,
      alignment (channel e (b+k) (signBit ∘ g)) v =
      alignment (channel e b (signBit ∘ f)) w := by
  induction k with
  | zero => exact ⟨f,w,rfl⟩
  | succ k ih =>
    obtain ⟨g,v,h⟩ := ih
    refine ⟨fun y ↦ g (Fin.tail y),fun x ↦ v (Fin.tail x), ?_⟩
    rw [← h]
    have hd (b' : Bool) (x : Word (b+k)) :
        channel e (b+k+1) (signBit ∘ fun y ↦ g (Fin.tail y)) (Fin.cons b' x) =
        channel e (b+k) (signBit ∘ g) x := by
      simp only [channel,Fin.tail_cons,Function.comp_def]; ring
    unfold alignment
    simp only [Nat.add_succ]
    rw [expect_succ (n:=b+k)]
    have av (a : ℝ) : (a+a)/2=a := by ring
    simp only [hd,expect_succ,Fin.tail_cons,av]

end WeinbergerShayevitz
