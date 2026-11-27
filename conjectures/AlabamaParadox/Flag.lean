module

public import conjectures.AlabamaParadox.Cutoff
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Tactic.Linarith

open Finset
namespace AlabamaParadox

variable {m : ℕ} {p : Fin m → ℝ}

private theorem coeff_constant (hs : ∑ i, p i = 1) (hi : IndependentShares p)
    (a : Fin m → ℤ) (t : ℤ) (h : ∑ i, (a i : ℝ)*p i = t) : ∀ j, a j = t := by
  have e : ∑ i, ((a i-t : ℤ) : ℝ)*p i = 0 := by
    simp only [Int.cast_sub, sub_mul, sum_sub_distrib, ← mul_sum, hs, h, mul_one, sub_self]
  exact fun j => sub_eq_zero.mp (hi _ e j)

public theorem cutoff_pos [Nontrivial (Fin m)] (hs : ∑ i, p i = 1)
    (hi : IndependentShares p) {n : ℕ} (hn : 0 < n) (i : Fin m) : 0 < cutoff p n i := by
  apply lt_of_le_of_ne (Int.fract_nonneg _)
  intro e
  change 0 = (n:ℝ)*p i - ↑⌊(n:ℝ)*p i⌋ at e
  let a (j : Fin m) : ℤ := if j = i then n else 0
  have h : ∑ j, (a j : ℝ)*p j = ⌊(n:ℝ)*p i⌋ := by
    simpa [a, ite_mul] using (sub_eq_zero.mp e.symm)
  have hc := coeff_constant hs hi a _ h
  obtain ⟨j, hj⟩ := exists_ne i
  have hz := hc j
  have hn' := hc i
  simp [a,hj] at hz hn'
  omega

public theorem cutoff_injective (hs : ∑ i, p i = 1) (hi : IndependentShares p)
    {n : ℕ} (hn : 0 < n) : Function.Injective (cutoff p n) := by
  intro i j e
  by_contra hij
  let a (k : Fin m) : ℤ := (if k = i then n else 0) - (if k = j then n else 0)
  let t := ⌊(n:ℝ)*p i⌋ - ⌊(n:ℝ)*p j⌋
  have h : ∑ k, (a k : ℝ)*p k = t := by
    change (n:ℝ)*p i - ↑⌊(n:ℝ)*p i⌋ = (n:ℝ)*p j - ↑⌊(n:ℝ)*p j⌋ at e
    simp [a, t, sub_mul, sum_sub_distrib, ite_mul]
    linarith
  have hc := coeff_constant hs hi a t h
  have h₁ := hc i
  have h₂ := hc j
  simp [a, hij, Ne.symm hij] at h₁ h₂
  omega

/-- Lemma 4.1 of Janson and Linusson expresses the cutoff condition by this congruence. -/
@[expose] public def Flag (p : Fin m → ℝ) (n : ℕ) (i : Fin m) : Prop :=
  (∑ j : {k : Fin m // k ≠ i}, (⌊offset p n i j⌋ : ZMod m)) = n

public theorem flag_total [Nontrivial (Fin m)] (hs : ∑ i, p i = 1)
    (hi : IndependentShares p) {n : ℕ} (hn : 0 < n) {i : Fin m} (h : Flag p n i) :
    ∑ j, frozen p n (cutoff p n i) j = ↑n := by
  classical
  let c := cutoff p n i
  let T := ∑ j, frozen p n c j
  have hc : 0 < c := cutoff_pos hs hi hn i
  have hc' : c < 1 := Int.fract_lt_one _
  have hT : (T : ZMod m) = n := by
    dsimp [T, c]
    simp only [frozen_flag, Int.cast_sum, Int.cast_add, sum_add_distrib,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← (Equiv.optionSubtypeNe i).sum_comp, Fintype.sum_option]
    simpa [Flag, offset, Equiv.optionSubtypeNe] using h
  have hd : (m : ℤ) ∣ (n : ℤ)-T :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub T n m).mp (by simpa using hT)
  have eql : ∑ j, ((n:ℝ)*p j-1) = (n:ℝ)-m := by simp [sum_sub_distrib, ← mul_sum, hs]
  have equ : ∑ j, ((n:ℝ)*p j+1) = (n:ℝ)+m := by simp [sum_add_distrib, ← mul_sum, hs]
  have low : (n:ℝ)-m < T := by
    rw [← eql]
    dsimp [T]
    push_cast
    apply sum_lt_sum_of_nonempty univ_nonempty
    intro j _
    have hfloor := Int.lt_floor_add_one ((n:ℝ)*p j+1-c)
    unfold frozen
    linarith
  have high : (T:ℝ) < n+m := by
    rw [← equ]
    dsimp [T]
    push_cast
    apply sum_lt_sum_of_nonempty univ_nonempty
    intro j _
    have hfloor := Int.floor_le ((n:ℝ)*p j+1-c)
    unfold frozen
    linarith
  have lo : (n:ℤ)-(m:ℤ) < T := by exact_mod_cast low
  have up : T < (n:ℤ)+(m:ℤ) := by exact_mod_cast high
  change T = n
  by_cases hnT : (0:ℤ) ≤ n-T
  · have := Int.eq_zero_of_dvd_of_nonneg_of_lt hnT (by omega) hd
    omega
  · have := Int.eq_zero_of_dvd_of_nonneg_of_lt (show (0:ℤ) ≤ -(n-T) by omega) (by omega)
      (dvd_neg.mpr hd)
    omega

private theorem total_strict {n : ℕ} {i j : Fin m} (hi : 0 < cutoff p n i)
    (hij : cutoff p n i < cutoff p n j) :
    ∑ k, frozen p n (cutoff p n j) k < ∑ k, frozen p n (cutoff p n i) k := by
  apply sum_lt_sum
  · exact fun k _ => Int.floor_mono (by linarith)
  · refine ⟨i, mem_univ _, ?_⟩
    rw [frozen, frozen, floor_cut _ _ (hi.trans hij) (Int.fract_lt_one _).le,
      floor_cut _ _ hi (Int.fract_lt_one _).le]
    change _ + (if cutoff p n j ≤ cutoff p n i then (1:ℤ) else 0) <
      _ + (if cutoff p n i ≤ cutoff p n i then (1:ℤ) else 0)
    simp [not_le.mpr hij]

public theorem flag_unique [Nontrivial (Fin m)] (hs : ∑ i, p i = 1)
    (hi : IndependentShares p) {n : ℕ} (hn : 0 < n) {i j : Fin m}
    (h₁ : Flag p n i) (h₂ : Flag p n j) : i = j := by
  apply cutoff_injective hs hi hn
  have a := flag_total hs hi hn h₁
  have b := flag_total hs hi hn h₂
  rcases lt_trichotomy (cutoff p n i) (cutoff p n j) with h|h|h
  · have := total_strict (cutoff_pos hs hi hn i) h
    omega
  · exact h
  · have := total_strict (cutoff_pos hs hi hn j) h
    omega

end AlabamaParadox
