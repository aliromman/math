module

public import conjectures.GallianRusinPrimeSquare.Factors
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.Ring

@[expose] public section
namespace GallianRusinPrimeSquare
open Polynomial Finset

def choices : List Code :=
  (List.range 3).flatMap fun a ↦ (List.range (a+2)).flatMap fun c ↦
    (List.range (2-a+(if c=0 then 0 else 1)+1)).map fun d ↦ ⟨a,c,d⟩

theorem mem_choices (x : Code) : x∈choices ↔
    x.a≤2 ∧ x.c≤x.a+1 ∧ x.d≤2-x.a+(if x.c=0 then 0 else 1) := by
  obtain ⟨a,c,d⟩ := x
  simp only [choices,List.mem_flatMap,List.mem_range,List.mem_map,Code.mk.injEq]
  constructor
  · rintro ⟨a',ha,c',hc,d',hd,rfl,rfl,rfl⟩
    omega
  · rintro ⟨ha,hc,hd⟩
    exact ⟨a,by omega,c,by omega,d,by omega,rfl,rfl,rfl⟩

theorem number : choices.toFinset.card=22 := by decide

theorem partners : ∀ x∈choices, ∃ y∈choices, ∃ z∈choices,
    x.a+y.a+z.a=3 ∧ (2-x.a)+(2-y.a)+(2-z.a)=3 ∧
    x.c+y.c+z.c=3 ∧ x.d+y.d+z.d=3 := by decide

theorem choices_are_dice {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    {x : Code} (hx : x∈choices) : Die (p^2*q) (assemble p q x) := by
  obtain ⟨a,c,d⟩ := x
  have ⟨ha,hc,hd⟩ := (mem_choices _).mp hx
  simp only at ha hc hd
  let b := 2-a
  change d≤b+_ at hd
  refine ⟨?_,?_⟩
  · change NN (product p q a b c d)
    have Ap := geom_nn (r:=p) (by decide : 0<1)
    have Bp := geom_nn (r:=p) hp.pos
    have Q := geom_nn (r:=q) (by decide : 0<1)
    have H := geom_nn (r:=p) (Nat.mul_pos hp.pos hq.pos)
    by_cases c0 : c=0
    · subst c
      simp only [ite_true,add_zero] at hd
      obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hd
      have eq : product p q a b 0 d=geom q 1*geom p 1^a*geom p p^v*geom p (p*q)^d := by
        rw [product,hv,←tall_geom hp hq hne]
        simp only [pow_zero,mul_one,mul_pow,pow_add]
        ac_rfl
      rw [eq]
      exact ((Q.mul (Ap.pow a)).mul (Bp.pow v)).mul (H.pow d)
    · let u := c-1
      let t := a-u
      have hc' : c=u+1 := by dsimp [u]; omega
      have ha' : a=t+u := by dsimp [t,u]; omega
      have A1 := geom_nn (r:=p) hq.pos
      by_cases db : d≤b
      · obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le db
        have eq : product p q a b c d=
            geom q p*geom p 1^t*geom p q^u*geom p p^v*geom p (p*q)^d := by
          rw [product,hv,ha',hc',←pair_geom' hp hq hne,←pair_geom hp hq hne,←tall_geom hp hq hne]
          simp only [pow_add,pow_one,mul_pow]
          ring
        rw [eq]
        exact ((((geom_nn hp.pos).mul (Ap.pow t)).mul (A1.pow u)).mul (Bp.pow v)).mul (H.pow d)
      · have dd : d=b+1 := by simp only [ite_eq_right c0] at hd; omega
        have eq : product p q a b c d=
            geom q (p^2)*geom p 1^t*geom p q^u*geom p (p*q)^b := by
          rw [product,dd,ha',hc',←tall_geom' hp hq hne,←pair_geom' hp hq hne,
            ←pair_geom hp hq hne,←tall_geom hp hq hne]
          simp only [pow_add,pow_one,mul_pow]
          ring
        rw [eq]
        exact (((geom_nn (pow_pos hp.pos 2)).mul (Ap.pow t)).mul (A1.pow u)).mul (H.pow b)
  · push_cast
    exact product_eval hp hq hne (by dsimp [b]; omega)

private theorem factor_count {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (n : ℕ) :
    emultiplicity (F i) (F j^n)=if i=j then (n:ℕ∞) else 0 := by
  by_cases e : i=j
  · subst j
    simpa using emultiplicity_pow_self_of_prime (cyclotomic.irreducible hi).prime n
  · have nd : ¬F i∣F j := fun h ↦ e (cyclotomic_injective (R:=ℤ) <|
      eq_of_monic_of_associated (cyclotomic.monic _ ℤ) (cyclotomic.monic _ ℤ) <|
      (cyclotomic.irreducible hi).associated_of_dvd (cyclotomic.irreducible hj) h)
    simp [e,emultiplicity_pow (cyclotomic.irreducible hi).prime,emultiplicity_eq_zero.mpr nd]

theorem assemble_injective {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    Function.Injective (assemble p q) := by
  intro x y eq
  let V (x : Code) := F p^x.a * F (p^2)^(2-x.a) * F (p*q)^x.c * F (p^2*q)^x.d
  have shape (x : Code) : assemble p q x=geom q 1*V x := by
    simp only [assemble,product,V,prime_geom hp,square_geom hp,mul_assoc]
  have e : V x=V y := mul_left_cancel₀ (geom_ne hq.pos (by decide : 0<1)) (by simpa only [←shape] using eq)
  have p2 := pow_pos hp.pos 2
  have pq := Nat.mul_pos hp.pos hq.pos
  have p2q := Nat.mul_pos p2 hq.pos
  have count (i : ℕ) := congrArg (emultiplicity (F i)) e
  have m1 : p<p^2 := by rw [pow_two]; exact lt_mul_of_one_lt_right hp.pos hp.one_lt
  have m2 : p<p*q := lt_mul_of_one_lt_right hp.pos hq.one_lt
  have m3 : p^2<p^2*q := lt_mul_of_one_lt_right p2 hq.one_lt
  have m4 : p*q<p^2*q := Nat.mul_lt_mul_of_pos_right m1 hq.pos
  have m5 : p^2≠p*q := by rw [pow_two]; exact fun e ↦ hne (Nat.eq_of_mul_eq_mul_left hp.pos e)
  have a := count p
  have c := count (p*q)
  have d := count (p^2*q)
  simp only [V,emultiplicity_mul (cyclotomic.irreducible hp.pos).prime] at a
  simp only [V,emultiplicity_mul (cyclotomic.irreducible pq).prime] at c
  simp only [V,emultiplicity_mul (cyclotomic.irreducible p2q).prime] at d
  simp [factor_count hp.pos hp.pos,factor_count hp.pos p2,factor_count hp.pos pq,
    factor_count hp.pos p2q,m1.ne,m2.ne,(m1.trans m3).ne] at a
  simp [factor_count pq hp.pos,factor_count pq p2,factor_count pq pq,
    factor_count pq p2q,m2.ne',m5.symm,m4.ne] at c
  simp [factor_count p2q hp.pos,factor_count p2q p2,factor_count p2q pq,
    factor_count p2q p2q,(m1.trans m3).ne',m3.ne',m4.ne'] at d
  cases x; cases y
  congr

end GallianRusinPrimeSquare
