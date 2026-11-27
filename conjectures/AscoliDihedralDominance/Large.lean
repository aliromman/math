module

public import conjectures.AscoliDihedralDominance.Moments

@[expose] public section
open Finset
namespace AscoliDihedral

theorem relative_fourth {m n F : ℕ} (hf : F ≤ 2*n)
    (h : m^4 ≤ 9^F * 7^(2*n-F)) :
    ((m:ℚ)/(3:ℚ)^n)^4 ≤ (7/9:ℚ)^(2*n-F) := by
  have hm : (m:ℚ)^4 ≤ 9^F * 7^(2*n-F) := by exact_mod_cast h
  have hpow : ((3:ℚ)^n)^4 = (9:ℚ)^F * 9^(2*n-F) := by
    rw [←pow_add, Nat.add_sub_of_le hf, show (9:ℚ) = 3^2 by norm_num, ←pow_mul, ←pow_mul]
    congr 1; omega
  rw [div_pow,div_pow,div_le_div_iff₀ (by positivity) (by positivity),hpow]
  calc
    (m:ℚ)^4 * 9^(2*n-F) ≤ (9^F * 7^(2*n-F)) * 9^(2*n-F) := by gcongr
    _ = _ := by ring

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem product_misses_relative {n : ℕ} (hN : Fintype.card G = 2*n) (g : G) :
    ((missingProducts g).card / (3:ℚ)^n)^4 ≤
      (7/9:ℚ)^(2*n-fixedTwice (productStep g)) := by
  have h := coloring_fourth_bound (productStep g)
  rw [←missingProducts_card,hN] at h
  apply relative_fourth _ h
  rw [←hN,fixedTwice]
  exact card_le_univ _

theorem product_misses_bound {n : ℕ} (hN : Fintype.card G = 2*n) (hn : 32 ≤ n) (g : G) :
    ((missingProducts g).card : ℚ) ≤ (3:ℚ)^n *
      (if g ∈ Subgroup.center G then 1 else 17/125) := by
  let u := ((missingProducts g).card : ℚ) / (3:ℚ)^n
  have hu : u^4 ≤ (7/9:ℚ)^(2*n-fixedTwice (productStep g)) := product_misses_relative hN g
  have den : 0 < (3:ℚ)^n := by positivity
  by_cases hc : g ∈ Subgroup.center G
  · simp only [hc,ite_true,mul_one]
    have hub : u^4 ≤ (1:ℚ)^4 := by
      have h₁ : (7/9:ℚ)^(2*n-fixedTwice (productStep g)) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      exact hu.trans (by simpa only [one_pow] using h₁)
    have := le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (by norm_num : (0:ℚ) ≤ 1) hub
    exact (div_le_iff₀ den).mp (show ((missingProducts g).card:ℚ) / (3:ℚ)^n ≤ 1 from this) |>.trans_eq (one_mul _)
  · simp only [hc,ite_false]
    rw [mul_comm]
    have hf := noncentral_fixed_le g hc
    rw [hN] at hf
    have e : n ≤ 2*n-fixedTwice (productStep g) := by omega
    have hn' : u^4 ≤ (17/125:ℚ)^4 :=
      (hu.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) e)).trans (large_ratio_bounds n hn).1.le
    have hu' := le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (by norm_num : (0:ℚ) ≤ 17/125) hn'
    exact (div_le_iff₀ den).mp hu'

theorem pair_misses_bound {n : ℕ} (hN : Fintype.card G = 2*n) (hn : 32 ≤ n)
    {g h : G} (g₀ : g ≠ 1) (h₀ : h ≠ 1) (g₂ : g*g=1) (h₂ : h*h=1) (gh : g ≠ h) :
    (3*(n:ℚ)/2) * (missingQuotients g ∩ missingQuotients h).card ≤
      (9/10:ℚ) * (3:ℚ)^n := by
  let m := (missingQuotients g ∩ missingQuotients h).card
  have h := two_missing_fourth g₀ h₀ g₂ h₂ gh
  rw [hN] at h
  have h' : ((m:ℚ)/(3:ℚ)^n)^4 ≤ (7/9:ℚ)^(2*n) := by
    apply relative_fourth (F := 0) (by omega)
    simpa [m] using h
  have hs : ((m:ℚ)/(3:ℚ)^n)^2 ≤ (7/9:ℚ)^n := by
    apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity)
    simpa [←pow_mul,mul_comm n 2] using h'
  have a := (large_ratio_bounds n hn).2
  have ha : ((3*(n:ℚ)/2)*((m:ℚ)/(3:ℚ)^n))^2 ≤ (9/10:ℚ)^2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans a.le
  have hb := le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by norm_num : (0:ℚ) ≤ 9/10) ha
  rw [←mul_div_assoc] at hb
  exact (div_le_iff₀ (by positivity)).mp hb

end AscoliDihedral
