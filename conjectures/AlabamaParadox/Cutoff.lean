module

public import conjectures.AlabamaParadox.Statement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open Finset
namespace AlabamaParadox

variable {ι : Type*}

/-- Keep the fractional cutoff fixed when the house size changes. -/
@[expose] public noncomputable def frozen (p : ι → ℝ) (n : ℕ) (c : ℝ) (j : ι) : ℤ :=
  ⌊(n : ℝ) * p j + 1 - c⌋

public theorem floor_cut (x c : ℝ) (hc : 0 < c) (hc' : c ≤ 1) :
    ⌊x + 1 - c⌋ = ⌊x⌋ + if c ≤ Int.fract x then 1 else 0 := by
  have h₁ := Int.floor_le x
  have h₂ := Int.lt_floor_add_one x
  by_cases h : c ≤ Int.fract x
  · rw [ite_eq_left h, Int.floor_eq_iff]
    simp only [Int.cast_add, Int.cast_one]
    change c ≤ x - ↑⌊x⌋ at h
    constructor <;> linarith
  · rw [ite_eq_right h, add_zero, Int.floor_eq_iff]
    change ¬ c ≤ x - ↑⌊x⌋ at h
    constructor <;> linarith

/-- If the cutoff assigns at most n seats, all these seats survive Hamilton's rule. -/
public theorem frozen_le [Fintype ι] [DecidableEq ι] {p : ι → ℝ} {n : ℕ} {a : ι → ℤ} (ha : Hamilton p n a)
    {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1) (hs : ∑ j, frozen p n c j ≤ n) :
    ∀ j, frozen p n c j ≤ a j := by
  classical
  obtain ⟨ht, w, hw, horder⟩ := ha
  intro j
  by_contra! h
  have hf (i : ι) := floor_cut ((n : ℝ) * p i) c hc hc'
  change a j < ⌊(n : ℝ) * p j + 1 - c⌋ at h
  rw [hf, hw] at h
  have hj : j ∉ w ∧ c ≤ Int.fract ((n : ℝ) * p j) := by
    by_cases A : j ∈ w <;> by_cases B : c ≤ Int.fract ((n : ℝ)*p j) <;> simp_all
  have hall (i : ι) : a i ≤ frozen p n c i := by
    rw [hw, frozen, hf]
    by_cases hi : i ∈ w
    · have hi' := hj.2.trans (horder i hi j hj.1)
      simp [hi, hi']
    · by_cases h : c ≤ Int.fract ((n : ℝ) * p i) <;> simp [hi, h]
  have hlt : ∑ i, a i < ∑ i, frozen p n c i := by
    apply sum_lt_sum (fun i _ => hall i)
    exact ⟨j, mem_univ _, by simpa only [frozen, hf, hw] using h⟩
  omega

public theorem frozen_eq [Fintype ι] [DecidableEq ι] {p : ι → ℝ} {n : ℕ} {a : ι → ℤ} (ha : Hamilton p n a)
    {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1) (hs : ∑ j, frozen p n c j = n) :
    ∀ j, frozen p n c j = a j := by
  have h := frozen_le ha hc hc' hs.le
  intro j
  by_contra hn
  have hlt := sum_lt_sum (s:=univ) (fun i _ => h i)
    ⟨j, mem_univ _, lt_of_le_of_ne (h j) hn⟩
  rw [hs, ha.1] at hlt
  exact lt_irrefl _ hlt

@[expose] public noncomputable def cutoff (p : ι → ℝ) (n : ℕ) (i : ι) := Int.fract ((n : ℝ) * p i)

@[expose] public noncomputable def offset (p : ι → ℝ) (n : ℕ) (i j : ι) :=
  (n : ℝ) * (p j - p i)

public theorem frozen_flag (p : ι → ℝ) (n : ℕ) (i j : ι) :
    frozen p n (cutoff p n i) j = ⌊offset p n i j⌋ + ⌊(n : ℝ)*p i⌋ + 1 := by
  rw [frozen, cutoff, Int.fract]
  rw [show (n : ℝ)*p j + 1 - ((n : ℝ)*p i - ↑⌊(n : ℝ)*p i⌋) =
    (offset p n i j + ↑⌊(n : ℝ)*p i⌋) + 1 by unfold offset; ring]
  rw [Int.floor_add_one, Int.floor_add_intCast]

public theorem frozen_step {p : ι → ℝ} (hp : ∀ j, 0 ≤ p j) (hp' : ∀ j, p j < 1)
    (n : ℕ) (i j : ι) :
    frozen p (n+1) (cutoff p n i) j = frozen p n (cutoff p n i) j +
      if 1 - p j ≤ Int.fract (offset p n i j) then 1 else 0 := by
  rw [frozen_flag, frozen, cutoff, Int.fract]
  have e : (↑(n+1 : ℕ) : ℝ)*p j+1-((n:ℝ)*p i-↑⌊(n:ℝ)*p i⌋) =
      (offset p n i j + 1-(1-p j))+↑⌊(n:ℝ)*p i⌋+1 := by
    push_cast
    unfold offset
    ring
  rw [e, Int.floor_add_one, Int.floor_add_intCast, floor_cut _ _ (by linarith [hp' j])
    (by linarith [hp j])]
  omega

end AlabamaParadox
