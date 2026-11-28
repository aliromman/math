module

public import conjectures.GallianRusinGame.Factors
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace GallianRusinGame
open GallianRusin Polynomial Finset

def key (c : Code) : ℤ := horner 256 (table 2) * (horner 256 (table 3) *
  (horner 256 (table 5) * (horner 256 (table 6)^c.a * (horner 256 (table 10)^c.b *
  (horner 256 (table 15)^c.c * horner 256 (table 30)^c.d)))))

theorem key_eq (c : Code) : key c=(assemble c).eval 256 := by
  rw [assemble_eq,←table2,←table3,←table5,←table6,←table10,←table15,←table30]
  simp [key,eval_pow]

export GallianRusin (shape)

def exception : Code := ⟨3,0,0,0⟩

def choices : Finset Code := (range 64).image shape ∪
  {exception,⟨3,0,1,1⟩,⟨3,1,0,1⟩,⟨3,1,1,2⟩}

set_option maxRecDepth 4096

theorem number : choices.card=44 := by decide

set_option maxHeartbeats 2000000 in
private theorem byte_certificate : ∀ a b c d : Fin 11,
    smallBytes 16 (key ⟨a,b,c,d⟩).toNat=true → (⟨a,b,c,d⟩ : Code)∈choices := by decide

theorem valid_choice {c : Code} (p : Die 30 (assemble c))
    (a : c.a<11) (b : c.b<11) (k : c.c<11) (d : c.d<11) : c∈choices := by
  have non := (nonnegative_iff _).mp p.1
  have sum : (coefficients c).sum≤30 := by
    rw [←horner_one,←evaluate_list]
    exact p.2.le
  have digit := admissible_bytes non (by omega) 16
  have eq : key c=horner 256 (coefficients c) := (key_eq c).trans (evaluate_list ..)
  rw [←eq] at digit
  exact byte_certificate ⟨_,a⟩ ⟨_,b⟩ ⟨_,k⟩ ⟨_,d⟩ digit

set_option maxHeartbeats 4000000 in
private theorem face_certificate : ∀ c∈choices,
    (coefficients c).all (fun z ↦ decide (0≤z))=true ∧ (coefficients c).sum=30 := by decide

theorem choices_are_dice {c : Code} (h : c∈choices) : Die 30 (assemble c) :=
  die_of_counts _ (face_certificate c h)

theorem distinct_keys : ∀ c∈choices,∀ b∈choices,key c=key b → c=b := by decide

theorem partners : ∀ t∈choices, t≠exception → ∃ u∈choices,∃ v∈choices,
    t.a+u.a+v.a=3 ∧ t.b+u.b+v.b=3 ∧ t.c+u.c+v.c=3 ∧ t.d+u.d+v.d=3 := by decide

theorem exception_no_triple : ∀ u∈choices, ∀ v∈choices,
    key exception * key u * key v ≠ key ⟨1,1,1,1⟩^3 := by decide

end GallianRusinGame
