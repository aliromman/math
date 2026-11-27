module

public import conjectures.UlasStern.Solution
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section
namespace UlasStern

private def normForm {R : Type*} [CommRing R] (t a b : R) : R :=
  let u := b + (t+1)*a
  let v := t*a
  u^2 + u*v + v^2

private theorem norm_mod_three (n : ℕ) (t : ZMod 3) :
    normForm t (coeff t n).1 (coeff t n).2 = 1 := by
  let P (a b : ZMod 3) := (a+b)^2 = 1 ∧ (t = 1 → a*b = 0)
  have step : ∀ x a b : ZMod 3, (a+b)^2 = 1 ∧ (x=1 → a*b=0) →
      let c := (2*x+1)*a + b
      let d := -x^2*a
      (c+d)^2 = 1 ∧ (x=1 → c*d=0) := by decide +kernel
  have hs (k : ℕ) : P (coeff t k).1 (coeff t k).2 := by
    induction k with
    | zero => simp [P, coeff]
    | succ k ih => exact step t _ _ ih
  have norm : ∀ x a b : ZMod 3, normForm x a b = (a+b)^2 := by decide +kernel
  exact (norm t _ _).trans (hs n).1

private theorem root_implies_mod (p : ℕ) [Fact p.Prime] (hp : p ≠ 3) (t : ZMod p) (n : ℕ)
    (h : normForm t (coeff t n).1 (coeff t n).2 = 0) : p % 3 = 1 := by
  let a := (coeff t n).1
  let b := (coeff t n).2
  let u := b+(t+1)*a
  let v := t*a
  change u^2 + u*v + v^2 = 0 at h
  have hv : v ≠ 0 := by
    intro hv
    have hu : u = 0 := by simpa [hv] using h
    by_cases ht : t = 0
    · subst t
      have hs := coeff_at_zero (R := ZMod p) n
      simp [u, a, b, add_comm] at hu
      exact one_ne_zero (hs.symm.trans hu)
    · have ha : a = 0 := (mul_eq_zero.mp hv).resolve_left ht
      exact coeff_nonsingular ht n ha (by simpa [u,ha] using hu)
  let z := u/v
  have hz : z^2+z+1=0 := by
    dsimp [z]
    field_simp [hv]
    linear_combination h
  have hzero : z ≠ 0 := by intro he; simp [he] at hz
  have hone : z ≠ 1 := by
    intro he
    have h3 : (3 : ZMod p) = 0 := by rw [he] at hz; linear_combination hz
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
    exact hp (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left (Fact.out (p := p.Prime)).ne_one)
  have hcube : z^3 = 1 := by linear_combination (z-1)*hz
  have hord : orderOf z = 3 := orderOf_eq_prime hcube hone
  have hd := ZMod.orderOf_dvd_card_sub_one hzero
  rw [hord] at hd
  have hpos := (Fact.out (p := p.Prime)).pos
  omega

/-- Evaluation at any index in this family commutes with a ring homomorphism. -/
theorem map_family {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : R) (n : ℕ) :
    f (stern (index n) t) = stern (index n) (f t) := by
  have hc (k : ℕ) : f (coeff t k).1 = (coeff (f t) k).1 ∧
      f (coeff t k).2 = (coeff (f t) k).2 := by
    induction k with
    | zero => simp [coeff]
    | succ k ih => simp [coeff, ih.1, ih.2, map_ofNat]
  rw [eisenstein_identity, eisenstein_identity]
  simp [(hc n).1, (hc n).2]

/-- Over a prime field a root can occur only in characteristic one modulo three. -/
theorem root_characteristic (n : ℕ) (p : ℕ) (hp : p.Prime) (t : ZMod p)
    (h : stern (index n) t = 0) : p % 3 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [eisenstein_identity] at h
  by_cases hp3 : p = 3
  · subst p
    exact (one_ne_zero ((norm_mod_three n t).symm.trans h)).elim
  · exact root_implies_mod p hp3 t n h

/-- Every prime divisor of any integer value in the family is one modulo three. -/
theorem prime_divisor (n : ℕ) (t : ℤ) (p : ℕ) (hp : p.Prime)
    (hd : (p : ℤ) ∣ stern (index n) t) : p % 3 = 1 := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
  change (Int.castRingHom (ZMod p)) (stern (index n) t) = 0 at h
  rw [map_family] at h
  exact root_characteristic n p hp _ h

/-- Every prime that is one modulo three occurs at index 19. -/
theorem prime_dvd_nineteen_iff (p : ℕ) (hp : p.Prime) :
    (∃ t : ℤ, (p : ℤ) ∣ stern 19 t) ↔ p % 3 = 1 := by
  have hi : index 1 = 19 := by decide
  constructor
  · rintro ⟨t, ht⟩
    exact prime_divisor 1 t p hp (hi ▸ ht)
  · intro hp3
    have : Fact p.Prime := ⟨hp⟩
    have hd : 3 ∣ Fintype.card (ZMod p)ˣ := by
      rw [Fintype.card_units, ZMod.card]
      omega
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card 3 hd
    obtain ⟨hpow, hone⟩ := orderOf_eq_prime_iff.mp hζ
    let z : ZMod p := ζ
    have hcube : z^3=1 := congrArg Units.val hpow
    have hne : z ≠ 1 := fun h ↦ hone (Units.ext h)
    have hquad : z^2+z+1=0 := by
      apply (mul_eq_zero.mp (show (z-1)*(z^2+z+1)=0 by linear_combination hcube)).resolve_left
      exact sub_ne_zero.mpr hne
    let x := (z-1)⁻¹
    have hx : stern (index 1) x=0 := by
      rw [eisenstein_identity]
      simp [coeff, x]
      field_simp [sub_ne_zero.mpr hne]
      linear_combination hquad
    refine ⟨(x.val : ℤ), (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ?_⟩
    change (Int.castRingHom (ZMod p)) (stern 19 (x.val : ℤ)) = 0
    rw [← hi, map_family]
    simpa using hx

/-- The possible prime divisors in the entire family are exactly the primes one modulo three. -/
theorem prime_divisor_iff (p : ℕ) (hp : p.Prime) :
    (∃ (n : ℕ) (t : ℤ), (p : ℤ) ∣ stern (index n) t) ↔ p % 3 = 1 := by
  constructor
  · rintro ⟨n, t, hd⟩
    exact prime_divisor n t p hp hd
  · intro h
    obtain ⟨t, hd⟩ := (prime_dvd_nineteen_iff p hp).2 h
    exact ⟨1, t, hd⟩

/-- info: 'UlasStern.prime_divisor_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prime_divisor_iff

end UlasStern
