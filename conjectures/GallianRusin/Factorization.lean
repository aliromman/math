module

public import conjectures.GallianRusin.Die
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public section
namespace GallianRusin
open Polynomial Finset

theorem standard_factors {m} (pos : 0 < m) (s : List ℕ) (hs : s.Nodup)
    (eq : s.toFinset = m.divisors.erase 1) : (s.map (cyclotomic · ℤ)).prod = standard m := by
  rw [←List.prod_toFinset _ hs, eq, prod_cyclotomic_eq_geom_sum pos ℤ]
  rfl

/-- Remove the copies of the prime `p` from a product and retain the remaining factors. -/
theorem peel {p : ℤ[X]} (prime : Prime p) (k : ℕ) {A B T : ℤ[X]}
    (h : A * B = p ^ k * T) : ∃ n U V, A = p ^ n * U ∧ U * V = T := by
  induction k generalizing A B with
  | zero => exact ⟨0, A, B, by simp, by simpa using h⟩
  | succ k ih =>
    rw [pow_succ', mul_assoc] at h
    obtain ⟨Y, e⟩|⟨Y, e⟩ := prime.dvd_or_dvd (h ▸ dvd_mul_right p _)
    · rw [e, mul_assoc] at h
      obtain ⟨n, U, V, nu, uv⟩ := ih (mul_left_cancel₀ prime.ne_zero h)
      exact ⟨n + 1, U, V, by rw [e, nu, pow_succ', mul_assoc], uv⟩
    · rw [e, mul_left_comm] at h
      exact ih (mul_left_cancel₀ prime.ne_zero h)

end GallianRusin
