module

public import conjectures.GallianRusinDice.Factors
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace GallianRusinDice
open GallianRusin Polynomial Finset

def key (c : Code) : ℤ := horner 256 (table 3) * (horner 256 (table 5) *
  (horner 256 (table 7) * (horner 256 (table 15)^c.a * (horner 256 (table 21)^c.b *
  (horner 256 (table 35)^c.c * horner 256 (table 105)^c.d)))))

theorem key_eq (c : Code) : key c=(assemble c).eval 256 := by
  rw [assemble_eq,←table3,←table5,←table7,←table15,←table21,←table35,←table105]
  simp [key,eval_pow]

export GallianRusin (shape)

def choices : Finset Code := (range 64).image shape

set_option maxRecDepth 4096

theorem number : choices.card=40 := by decide

set_option maxHeartbeats 2000000 in
private theorem byte_certificate : ∀ a b c d : Fin 7,
    smallBytes 48 (key ⟨a,b,c,d⟩).toNat=true → (⟨a,b,c,d⟩ : Code)∈choices := by decide

theorem valid_choice {c : Code} (p : Die 105 (assemble c))
    (a : c.a<7) (b : c.b<7) (k : c.c<7) (d : c.d<7) : c∈choices := by
  have non := (nonnegative_iff _).mp p.1
  have sum : (coefficients c).sum≤105 := by
    rw [←horner_one,←evaluate_list]
    exact p.2.le
  have digit := admissible_bytes non (by omega) 48
  have eq : key c=horner 256 (coefficients c) := (key_eq c).trans (evaluate_list ..)
  rw [←eq] at digit
  exact byte_certificate ⟨_,a⟩ ⟨_,b⟩ ⟨_,k⟩ ⟨_,d⟩ digit

set_option maxHeartbeats 4000000 in
private theorem face_certificate : ∀ c∈choices,
    (coefficients c).all (fun z ↦ decide (0≤z))=true ∧ (coefficients c).sum=105 := by decide

theorem choices_are_dice {c : Code} (h : c∈choices) : Die 105 (assemble c) :=
  die_of_counts _ (face_certificate c h)

theorem distinct_keys : ∀ c∈choices,∀ b∈choices,key c=key b → c=b := by decide

theorem partners : ∀ t∈choices, ∃ u∈choices,∃ v∈choices,
    t.a+u.a+v.a=3 ∧ t.b+u.b+v.b=3 ∧ t.c+u.c+v.c=3 ∧ t.d+u.d+v.d=3 := by decide

end GallianRusinDice
