module

public import conjectures.CampbellCoupons.Profiles
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace CampbellCoupons
open Finset

private def extra {k : ℕ} (m : ℕ) (i j : Fin k) : ℕ := m + if i = j then 1 else 0

private theorem sum_extra {k : ℕ} (m : ℕ) (i : Fin k) :
    ∑ j, extra m i j = k * m + 1 := by simp [extra, sum_add_distrib]

private theorem extra_injective {k : ℕ} (m : ℕ) : Function.Injective (@extra k m) := by
  intro i j hij
  by_contra hn
  have := congrFun hij i
  simp [extra, Ne.symm hn] at this

private theorem balanced_profiles (m k : ℕ) :
    profiles m k (k * m) = {fun _ => m} := by
  ext f
  rw [mem_profiles, mem_singleton]
  constructor
  · rintro ⟨hs, hm⟩
    have h := (sum_eq_sum_iff_of_le (s := univ) (fun i _ => hm i)).mp (by simpa using hs.symm)
    exact funext fun i => (h i (mem_univ _)).symm
  · rintro rfl
    simp

private theorem surplus_profiles (m k : ℕ) :
    profiles m k (k * m + 1) = univ.image (extra m) := by
  ext f
  rw [mem_profiles, mem_image]
  constructor
  · rintro ⟨hs, hm⟩
    have hex : ∃ i, m < f i := by
      by_contra! hn
      have he : f = fun _ => m := funext fun i => Nat.le_antisymm (hn i) (hm i)
      simp [he] at hs
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, mem_univ _, funext fun j => ?_⟩
    apply (sum_eq_sum_iff_of_le (s := univ) (f := extra m i) (g := f) ?_).mp
      ((sum_extra m i).trans hs.symm) j (mem_univ _)
    intro l _
    by_cases h : i = l
    · subst l
      simpa [extra] using hi
    · simpa [extra, h] using hm l
  · rintro ⟨i, _, rfl⟩
    exact ⟨sum_extra _ _, fun j => Nat.le_add_right ..⟩

/-- At the first possible turn there is only the constant occupancy vector. -/
theorem winning_balanced (m k : ℕ) :
    m.factorial ^ k * winning m k (k * m) = (k * m).factorial := by
  rw [winning_eq_sum, balanced_profiles, sum_singleton]
  simpa using Nat.multinomial_spec (univ : Finset (Fin k)) (fun _ => m)

/-- With one surplus draw, one type occurs once more than the other types. -/
theorem winning_surplus (m k : ℕ) :
    ((m + 1) * m.factorial ^ k) * winning m k (k * m + 1) = k * (k * m + 1).factorial := by
  rw [winning_eq_sum, surplus_profiles, sum_image (extra_injective m).injOn, mul_sum]
  apply (sum_congr rfl (g := fun _ => (k * m + 1).factorial) ?_).trans (by simp)
  intro i _
  have hprod : ∏ j, (extra m i j).factorial = (m + 1) * m.factorial ^ k := by
    have h (j : Fin k) : (extra m i j).factorial = m.factorial * (if i = j then m + 1 else 1) := by
      by_cases e : i = j <;> simp [extra, e, Nat.factorial_succ, Nat.mul_comm]
    simp only [h, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
      prod_ite_eq, mem_univ, ite_true]
    exact Nat.mul_comm ..
  simpa only [hprod, sum_extra] using Nat.multinomial_spec univ (extra m i)

/-- The probability ratio at the common comparison time T = k². -/
noncomputable def ratio (k : ℕ) : ℝ :=
  success (k - 1) (k + 1) (k * k) / success k k (k * k)

theorem ratio_formula {k : ℕ} (hk : 0 < k) :
    ratio k = (k + 1 : ℝ) * (k : ℝ)^k / k.factorial * ((k : ℝ) / (k+1)) ^ (k*k) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let k := l + 1
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hfac : (k.factorial : ℝ) = k * l.factorial := by
    exact_mod_cast Nat.factorial_succ l
  have htotal : (k+1)*l+1 = k*k := by dsimp [k]; ring
  have hp : (k.factorial : ℝ)^k * winning k k (k*k) = (k*k).factorial := by
    exact_mod_cast winning_balanced k k
  have hq : ((k : ℝ) * (l.factorial : ℝ)^(k+1)) * winning l (k+1) (k*k) =
      (k+1 : ℝ) * (k*k).factorial := by
    have h := winning_surplus l (k+1)
    rw [htotal] at h
    exact_mod_cast h
  have pf : (winning k k (k*k) : ℝ) = (k*k).factorial / (k.factorial : ℝ)^k :=
    (eq_div_iff (by positivity)).mpr (mul_comm .. |>.trans hp)
  have qf : (winning l (k+1) (k*k) : ℝ) =
      (k+1 : ℝ) * (k*k).factorial / (k * (l.factorial : ℝ)^(k+1)) :=
    (eq_div_iff (by positivity)).mpr (mul_comm .. |>.trans hq)
  change (winning l (k+1) (k*k) / ((k+1 : ℕ) : ℝ)^(k*k)) /
    (winning k k (k*k) / (k : ℝ)^(k*k)) = _
  change _ = (k+1 : ℝ) * (k : ℝ)^k / k.factorial * ((k : ℝ) / (k+1)) ^ (k*k)
  rw [pf, qf, hfac, mul_pow, div_pow, pow_succ (l.factorial : ℝ)]
  push_cast
  field_simp

end CampbellCoupons
