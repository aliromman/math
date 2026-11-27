module

public import conjectures.GallianRusinPrimeSquare.Progressions
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import conjectures.GallianRusin.Factorization
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace GallianRusinPrimeSquare
open GallianRusin Polynomial Finset

noncomputable abbrev F (j : ℕ) : ℤ[X] := cyclotomic j ℤ

theorem prime_geom {p : ℕ} (hp : p.Prime) : F p=geom p 1 := by
  let : Fact p.Prime := ⟨hp⟩
  simp [F,geom,cyclotomic_prime]

theorem square_geom {p : ℕ} (hp : p.Prime) : F (p^2)=geom p p := by
  simpa [F,geom,pow_mul] using (cyclotomic_prime_pow_eq_geom_sum (R:=ℤ) (n:=1) hp)

theorem pair_geom {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    F (p*q) * geom p 1=geom p q := by
  have nd : ¬q∣p := fun h ↦ hne ((Nat.dvd_prime hp).mp h |>.resolve_left hq.ne_one).symm
  rw [←prime_geom hp,←cyclotomic_expand_eq_cyclotomic_mul hq nd ℤ]
  change expand ℤ q (F p)=_
  rw [prime_geom hp,expand_geom,mul_one]

theorem pair_geom' {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    F (p*q) * geom q 1=geom q p := by
  simpa only [Nat.mul_comm q p] using pair_geom hq hp hne.symm

theorem tall_expand {p q : ℕ} (hp : p.Prime) :
    expand ℤ p (F (p*q))= F (p^2*q) := by
  convert cyclotomic_expand_eq_cyclotomic hp (dvd_mul_right p q) ℤ using 2; ring

theorem tall_geom {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    F (p^2*q) * geom p p=geom p (p*q) := by
  have e := congrArg (expand ℤ p) (pair_geom hp hq hne)
  simpa only [map_mul,expand_geom,mul_one,tall_expand hp] using e

theorem tall_geom' {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    F (p^2*q) * geom q p=geom q (p^2) := by
  have e := congrArg (expand ℤ p) (pair_geom' hp hq hne)
  simpa only [map_mul,expand_geom,mul_one,tall_expand hp,pow_two] using e

structure Code where
  a : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq

noncomputable def product (p q a b c d : ℕ) : ℤ[X] :=
  geom q 1 * geom p 1 ^ a * geom p p ^ b * F (p*q)^c * F (p^2*q)^d

noncomputable def assemble (p q : ℕ) (x : Code) : ℤ[X] := product p q x.a (2-x.a) x.c x.d

theorem standard_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    standard (p^2*q)=product p q 1 1 1 1 := by
  have e : geom (p^2) 1=geom p 1*geom p p := by rw [geom_one,pow_two,standard_split]
  rw [standard_split,e]
  simp only [pow_one,product]
  rw [←tall_geom' hp hq hne,←pair_geom' hp hq hne]
  ring

theorem pair_eval {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    (F (p*q)).eval 1=1 := by
  have e := congrArg (eval (1:ℤ)) (pair_geom hp hq hne)
  simp only [eval_mul,geom_eval] at e
  exact mul_right_cancel₀ (show (p:ℤ)≠0 by exact_mod_cast hp.ne_zero) (e.trans (one_mul _).symm)

theorem tall_eval {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    (F (p^2*q)).eval 1=1 := by
  have e := congrArg (eval (1:ℤ)) (tall_geom hp hq hne)
  simp only [eval_mul,geom_eval] at e
  exact mul_right_cancel₀ (show (p:ℤ)≠0 by exact_mod_cast hp.ne_zero) (e.trans (one_mul _).symm)

theorem product_eval {p q a b c d : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (hab : a+b=2) : (product p q a b c d).eval 1=p^2*q := by
  simp only [product,eval_mul,eval_pow,geom_eval,pair_eval hp hq hne,tall_eval hp hq hne,one_pow,mul_one]
  rw [mul_assoc,←pow_add,hab,mul_comm]

private theorem faces {p q a b z : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    {s : ℤ} (unit : IsUnit s) (val : (p:ℤ)^a*((p:ℤ)^b*((q:ℤ)^z*s))=(p:ℤ)^2*q) :
    a+b=2 ∧ z=1 ∧ s=1 := by
  have pz : 0<(p:ℤ) := by exact_mod_cast hp.pos
  have qz : 0<(q:ℤ) := by exact_mod_cast hq.pos
  rcases Int.isUnit_iff.mp unit with rfl|rfl
  · simp only [mul_one,←mul_assoc,←pow_add] at val
    have n : p^(a+b)*q^z=p^2*q := by exact_mod_cast val
    have atP := congrArg (fun n : ℕ ↦ n.factorization p) n
    have atQ := congrArg (fun n : ℕ ↦ n.factorization q) n
    have f := Nat.factorization_mul (pow_ne_zero (a+b) hp.ne_zero) (pow_ne_zero z hq.ne_zero)
    have g := Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) hq.ne_zero
    simp [f,g,hp.factorization_pow,hq.factorization_pow,hq.factorization,hne,hne.symm] at atP atQ
    exact ⟨atP,atQ,rfl⟩
  · have left : (p:ℤ)^a*((p:ℤ)^b*((q:ℤ)^z*(-1)))<0 := by simp only [mul_neg,neg_lt_zero]; positivity
    have right : 0<(p:ℤ)^2*q := by positivity
    exact (left.not_ge (val ▸ right.le)).elim

/-- A game of any size can use only these five irreducible factors. -/
theorem extraction {p q : ℕ} {P : ℤ[X]} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (game : SolutionDie (p^2*q) P) : ∃ a b c d, a+b=2 ∧ P=product p q a b c d := by
  obtain ⟨others,_,_,h⟩ := game.2
  let k := others.length+1
  have base : standard (p^2*q)=F p*(F (p^2)*(F q*(F (p*q)*F (p^2*q)))) := by
    rw [standard_eq hp hq hne,product]
    simp only [pow_one,←prime_geom hp,←prime_geom hq,←square_geom hp]
    ac_rfl
  rw [base] at h
  simp only [mul_pow] at h
  have prime (j : ℕ) (pos : 0<j) : Prime (F j) := (cyclotomic.irreducible pos).prime
  obtain ⟨a,A,B,r1,h⟩ := peel (prime _ hp.pos) k h
  obtain ⟨b,A,B,r2,h⟩ := peel (prime _ (pow_pos hp.pos _)) k h
  obtain ⟨z,A,B,r3,h⟩ := peel (prime _ hq.pos) k h
  obtain ⟨c,A,B,r4,h⟩ := peel (prime _ (Nat.mul_pos hp.pos hq.pos)) k h
  rw [←mul_one (F (p^2*q)^k)] at h
  obtain ⟨d,A,B,r5,h⟩ := peel (prime _ (Nat.mul_pos (pow_pos hp.pos _) hq.pos)) k h
  obtain ⟨s,su,eq⟩ := Polynomial.isUnit_iff.mp (isUnit_iff_dvd_one.mpr ⟨B,h.symm⟩)
  rw [←eq] at r5
  rw [r2,r3,r4,r5,prime_geom hp,square_geom hp,prime_geom hq] at r1
  have val := game.1.2
  rw [r1] at val
  simp only [eval_mul,eval_pow,eval_C,geom_eval,pair_eval hp hq hne,tall_eval hp hq hne,one_pow,
    one_mul,Nat.cast_mul,Nat.cast_pow] at val
  obtain ⟨sum,rfl,rfl⟩ := faces hp hq hne su val
  refine ⟨a,b,c,d,sum,?_⟩
  rw [r1,product]
  simp only [pow_one,map_one,mul_one]
  ac_rfl

end GallianRusinPrimeSquare
