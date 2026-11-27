module

public import conjectures.GallianRusinPrimeSquare.Choices
public import conjectures.GallianRusinPrimeSquare.Obstructions
import Mathlib.Tactic.Ring

public section
namespace GallianRusinPrimeSquare
open Polynomial Finset

private theorem triple {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    {x y z : Code} (a : x.a+y.a+z.a=3) (b : (2-x.a)+(2-y.a)+(2-z.a)=3)
    (c : x.c+y.c+z.c=3) (d : x.d+y.d+z.d=3) :
    assemble p q x*assemble p q y*assemble p q z=standard (p^2*q)^3 := by
  rw [standard_eq hp hq hne]
  unfold assemble product
  calc
    _ = geom q 1 ^ 3 * geom p 1 ^ (x.a+y.a+z.a) *
      geom p p ^ ((2-x.a)+(2-y.a)+(2-z.a)) * F (p*q) ^ (x.c+y.c+z.c) *
      F (p^2*q) ^ (x.d+y.d+z.d) := by simp only [pow_add]; ring
    _ = _ := by rw [a,b,c,d]; ring

/-- The inequalities on the three exponents describe every solution die. -/
theorem classification {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) (P : ℤ[X]) :
    SolutionDie (p^2*q) P ↔ ∃ x∈choices, assemble p q x=P := by
  constructor
  · intro game
    obtain ⟨a,b,c,d,hab,rfl⟩ := extraction hp hq hne game
    refine ⟨⟨a,c,d⟩,(mem_choices _).mpr ⟨by change a≤2; omega,first_bound hp hq hne game.1.1,?_⟩,?_⟩
    · change d≤2-a+(if c=0 then 0 else 1)
      by_cases h : c=0
      · subst c
        have le := upper_zero hp hq hne hab game.1.1
        simp
        omega
      · have le := upper_positive hp hq hne hab (by omega) game.1.1
        simp only [ite_eq_right h]
        omega
    · change product p q a (2-a) c d=_
      rw [show 2-a=b by omega]
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,z,hz,a,b,c,d⟩ := partners x hx
    refine ⟨choices_are_dice hp hq hne hx,[assemble p q y,assemble p q z],by simp,?_,?_⟩
    · intro Q mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl
      · exact choices_are_dice hp hq hne hy
      · exact choices_are_dice hp hq hne hz
    · simpa [mul_assoc] using triple hp hq hne a b c d

/-- Three dice suffice for every labeling, for all distinct primes p and q. -/
theorem three_dice {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) {P : ℤ[X]}
    (game : SolutionDie (p^2*q) P) : ∃ Q R, Die (p^2*q) Q ∧ Die (p^2*q) R ∧
      P*Q*R=standard (p^2*q)^3 := by
  obtain ⟨x,hx,rfl⟩ := (classification hp hq hne P).mp game
  obtain ⟨y,hy,z,hz,a,b,c,d⟩ := partners x hx
  exact ⟨_,_,choices_are_dice hp hq hne hy,choices_are_dice hp hq hne hz,triple hp hq hne a b c d⟩

theorem resolution : Conjecture := by
  classical
  intro p q hp hq hne
  have exactSet : {P : ℤ[X] | SolutionDie (p^2*q) P} =
      (choices.toFinset.image (assemble p q) : Finset ℤ[X]) := by
    ext P
    simpa using classification hp hq hne P
  rw [exactSet,Set.ncard_coe_finset,Finset.card_image_of_injective _ (assemble_injective hp hq hne)]
  exact number

/-- info: 'GallianRusinPrimeSquare.classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms classification

/-- info: 'GallianRusinPrimeSquare.three_dice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_dice

/-- info: 'GallianRusinPrimeSquare.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end GallianRusinPrimeSquare
