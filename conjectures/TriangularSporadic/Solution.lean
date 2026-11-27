module

public import conjectures.TriangularSporadic.Statement
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace TriangularSporadic

private def Split (d : ℕ) : Prop := d % 8 = 1 ∨ d % 8 = 7

private theorem odd_divisor {T : ℕ}
    (primes : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ T → Split p)
    (d : ℕ) (odd : d % 2 = 1) (hd : d ∣ T) : Split d := by
  induction d using induction_on_primes with
  | zero => simp at odd
  | one => exact Or.inl rfl
  | prime_mul p d hp ih =>
    have hop : p % 2 = 1 ∧ d % 2 = 1 := by
      rw [Nat.mul_mod] at odd
      have hp2 := Nat.mod_lt p (by decide : 0 < 2)
      have hd2 := Nat.mod_lt d (by decide : 0 < 2)
      by_cases zp : p % 2 = 0 <;> by_cases zd : d % 2 = 0 <;> simp_all
    have h1 := primes p hp (by intro he; subst p; norm_num at hop) ((dvd_mul_right p d).trans hd)
    have h2 := ih hop.2 ((dvd_mul_left d p).trans hd)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      simp [Split, Nat.mul_mod p d, h1, h2]

private theorem prime_residue {u v p k : ℕ} {c : ℤ}
    (he : (u : ℤ) * v + 2 * ((7 : ℤ) ^ k) ^ 2 = c ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hu : p ∣ u) : Split p := by
  by_cases hp7 : p = 7
  · subst p; exact Or.inr rfl
  have : Fact p.Prime := ⟨hp⟩
  have hn : (7 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 7 p).mp (show ((7 : ℕ) : ZMod p) = 0 from hzero)
    exact hp7 (((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hdiv).resolve_left hp.ne_one)
  have hu0 := (ZMod.natCast_eq_zero_iff u p).mpr hu
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) he
  push_cast at hz
  rw [hu0, zero_mul, zero_add] at hz
  apply (ZMod.exists_sq_eq_two_iff hp2).mp
  refine ⟨(c : ZMod p) / 7 ^ k, ?_⟩
  field_simp [hn]
  linear_combination hz

private theorem product_residue {r s : ℕ}
    (near : 2*r+1 = s ∨ 2*r = s+1) (hs : Split s)
    (hr : r % 2 = 1 → Split r) :
    (r*s)%8 = 0 ∨ (r*s)%8 = 1 ∨ (r*s)%8 = 4 := by
  unfold Split at *
  rw [Nat.mul_mod]
  rcases hs with hs | hs
  · have hr' : r%8=0 ∨ r%8=1 ∨ r%8=4 := by omega
    rcases hr' with h | h | h <;> simp [h, hs]
  · have hr' : r%8=0 ∨ r%8=7 ∨ r%8=4 := by omega
    rcases hr' with h | h | h <;> simp [h, hs]

private theorem triangular_residue (a : ℕ)
    (h : ∀ d : ℕ, d % 2 = 1 → d ∣ triangular a → Split d) :
    triangular a % 8 = 0 ∨ triangular a % 8 = 1 ∨ triangular a % 8 = 4 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' a <;> subst a
  · have e : triangular (2*m) = m*(2*m+1) := by
      simp [triangular, mul_assoc]
    rw [e]
    exact product_residue (Or.inl rfl)
      (h _ (by omega) (by rw [e]; exact dvd_mul_left ..))
      (fun ho => h _ ho (by rw [e]; exact dvd_mul_right ..))
  · have e : triangular (2*m+1) = (m+1)*(2*m+1) := by
      rw [triangular, show 2*m+1+1 = (m+1)*2 by omega, ← mul_assoc,
        Nat.mul_div_cancel _ (by decide : 0 < 2), Nat.mul_comm]
    rw [e]
    exact product_residue (Or.inr (by omega))
      (h _ (by omega) (by rw [e]; exact dvd_mul_left ..))
      (fun ho => h _ ho (by rw [e]; exact dvd_mul_right ..))


private theorem cast_possible (u : ℕ) (h : u%8 = 0 ∨ u%8 = 1 ∨ u%8 = 4) :
    (u : ZMod 8) = 0 ∨ (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 4 := by
  rw [← ZMod.natCast_mod u 8]
  rcases h with h | h | h <;> simp [h]

/-- No triangular pair exists for a power of seven squared and doubled. -/
public theorem no_pair (k : ℕ) : ¬ HasPair (2 * ((7 : ℤ) ^ k) ^ 2) := by
  rintro ⟨a, b, _, _, _, c, he⟩
  have he' : (triangular b : ℤ) * triangular a + 2 * ((7 : ℤ) ^ k) ^ 2 = c ^ 2 := by
    rwa [mul_comm (triangular b : ℤ)]
  have ha := cast_possible _ (triangular_residue a (odd_divisor (fun _ => prime_residue he)))
  have hb := cast_possible _ (triangular_residue b (odd_divisor (fun _ => prime_residue he')))
  have hz := congrArg (fun z : ℤ => (z : ZMod 8)) he
  push_cast at hz
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul, show (7 : ZMod 8)^2 = 1 by decide,
    one_pow, mul_one] at hz
  exact (show ∀ x y z : ZMod 8, (x=0 ∨ x=1 ∨ x=4) → (y=0 ∨ y=1 ∨ y=4) →
    x*y+2 ≠ z^2 from by decide) _ _ _ ha hb hz

/-- Infinitely many positive exceptions lie in the single residue class 8 modulo 9. -/
public theorem positive_exceptions : Set.Infinite {n : ℤ | 0 < n ∧ n%9 = 8 ∧ ¬ HasPair n} := by
  let f (k : ℕ) : ℤ := 2 * 7 ^ (6*k+2)
  have mono : StrictMono f := by
    intro i j hij
    exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by decide : 1 < (7 : ℤ)) (by omega)) (by decide)
  apply (Set.infinite_range_of_injective mono.injective).mono
  rintro _ ⟨k, rfl⟩
  change 0 < 2*(7 : ℤ)^(6*k+2) ∧ f k % 9 = 8 ∧ ¬ HasPair (f k)
  refine ⟨by positivity, ?_, ?_⟩
  · apply (ZMod.intCast_eq_intCast_iff' (f k) 8 9).mp
    dsimp [f]
    push_cast
    rw [pow_add, pow_mul, show (7 : ZMod 9)^6 = 1 by decide, one_pow, one_mul]
    decide
  · have eq : f k = 2 * ((7 : ℤ)^(3*k+1))^2 := by
      rw [← pow_mul]
      dsimp [f]
      congr 2
      omega
    exact eq ▸ no_pair (3*k+1)

public theorem resolution : Conjecture := by
  apply positive_exceptions.mono
  rintro n ⟨_, hn, h⟩
  exact ⟨by omega, by omega, h⟩

/-- info: 'TriangularSporadic.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end TriangularSporadic
