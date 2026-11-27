module

public import conjectures.GallianRusinDice.Progressions
public import conjectures.GallianRusinDice.Extraction
import Mathlib.Tactic.Ring

public section
namespace GallianRusinDice
open Polynomial Finset

private theorem triple {t u v : Code} (a : t.a+u.a+v.a=3) (b : t.b+u.b+v.b=3)
    (c : t.c+u.c+v.c=3) (d : t.d+u.d+v.d=3) :
    assemble t*assemble u*assemble v=standard 105^3 := by
  rw [standard_eq,assemble_eq,assemble_eq,assemble_eq,assemble_eq]
  calc
    _ = (cyclotomic 3 ℤ * cyclotomic 5 ℤ * cyclotomic 7 ℤ)^3 *
      (cyclotomic 15 ℤ)^(t.a+u.a+v.a) * (cyclotomic 21 ℤ)^(t.b+u.b+v.b) *
      (cyclotomic 35 ℤ)^(t.c+u.c+v.c) * (cyclotomic 105 ℤ)^(t.d+u.d+v.d) := by
        simp only [pow_add]
        ring
    _ = _ := by rw [a,b,c,d]; ring

/-- Every admissible die occurs in a game of exactly three dice. -/
theorem three_dice {P : ℤ[X]} (game : SolutionDie 105 P) : ∃ Q R,Die 105 Q ∧ Die 105 R ∧
    P*Q*R=standard 105^3 := by
  obtain ⟨t,h₁,h₂,h₃,h₄,rfl⟩ := extraction game
  have tgood := valid_choice game.1 h₁ h₂ h₃ h₄
  obtain ⟨u,hu,v,hv,a,b,c,d⟩ := partners t tgood
  exact ⟨_,_,choices_are_dice hu,choices_are_dice hv,triple a b c d⟩

private theorem solution_iff (P : ℤ[X]) : SolutionDie 105 P ↔ ∃ t∈choices,assemble t=P := by
  constructor
  · intro h
    obtain ⟨t,a,b,c,d,rfl⟩ := extraction h
    exact ⟨_,valid_choice h.1 a b c d,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨u,hu,v,hv,a,b,c,d⟩ := partners t ht
    refine ⟨choices_are_dice ht,[assemble u,assemble v],by simp,?_,?_⟩
    · intro Q hQ
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
      rcases hQ with rfl|rfl
      · exact choices_are_dice hu
      · exact choices_are_dice hv
    · simpa [mul_assoc] using triple a b c d

theorem classification (P : ℤ[X]) : SolutionDie 105 P ↔ ∃ a b c : ℕ, a∣35 ∧ b∣21 ∧ c∣15 ∧
    P=progression 3 a*(progression 5 b*progression 7 c) :=
  (solution_iff P).trans (choices_iff_progression P)

theorem resolution : Conjecture := by
  classical
  have eq : {P : ℤ[X] | SolutionDie 105 P}=(choices.image assemble : Finset ℤ[X]) := by
    ext P
    simpa using solution_iff P
  unfold Conjecture
  rw [eq,Set.ncard_coe_finset,Finset.card_image_of_injOn]
  · exact number
  · intro t ht u hu h
    apply distinct_keys t ht u hu
    rw [key_eq,key_eq,h]

/-- info: 'GallianRusinDice.odd_multiplicity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_multiplicity_bound

/-- info: 'GallianRusinDice.three_dice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_dice

/-- info: 'GallianRusinDice.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end GallianRusinDice
