module

public import conjectures.GallianRusinDice.Enumeration

@[expose] public section
namespace GallianRusinDice
open Polynomial Finset

/-- A die on an arithmetic progression after subtracting one from its labels. -/
noncomputable def progression (p step : ℕ) : ℤ[X] := ∑ j ∈ range p,X^(j*step)

private def monomialList (n : ℕ) := List.replicate n (0:ℤ) ++ [1]

private theorem polynomial_term (n : ℕ) : polynomial (monomialList n)=X^n := by
  induction n with
  | zero => simp [monomialList,polynomial]
  | succ n ih => simpa [monomialList,List.replicate_succ,polynomial,pow_succ'] using congrArg (X*·) ih

private def segment : ℕ → ℕ → List ℤ
  | 0,_ => []
  | p+1,s => plus (monomialList (p*s)) (segment p s)

private theorem polynomial_segment (p s : ℕ) : polynomial (segment p s)=progression p s := by
  induction p with
  | zero => simp [segment,polynomial,progression]
  | succ p ih => simp [segment,polynomial_add,polynomial_term,ih,progression,sum_range_succ,add_comm]

private def step (m i p q : ℕ) := (if m/2^i%2=1 then p else 1) *
    (if m/2^(i+1)%2=1 then q else 1)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem product_certificate : ∀ m : Fin 64, coefficients (shape m)=multiply
    [segment 3 (step m 0 5 7),segment 5 (step m 2 3 7),segment 7 (step m 4 3 5)] := by decide

private theorem assemble_shape (m : Fin 64) : assemble (shape m) =
    progression 3 (step m 0 5 7) * (progression 5 (step m 2 3 7) * progression 7 (step m 4 3 5)) := by
  rw [assemble,product_certificate,polynomial_multiply]
  simp [polynomial_segment]

private theorem step_divides (m i p q : ℕ) : step m i p q∣p*q := by
  unfold step
  split <;> split <;> simp

set_option maxRecDepth 4096 in
private theorem divisors_complete : ∀ a∈(35:ℕ).divisors,∀ b∈(21:ℕ).divisors,∀ c∈(15:ℕ).divisors,
    ∃ m∈range 64,a=step m 0 5 7 ∧ b=step m 2 3 7 ∧ c=step m 4 3 5 := by decide

theorem choices_iff_progression (P : ℤ[X]) : (∃ t∈choices,assemble t=P) ↔
    ∃ a b c : ℕ,a∣35 ∧ b∣21 ∧ c∣15 ∧ P=progression 3 a*(progression 5 b*progression 7 c) := by
  constructor
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨_,_,_,step_divides i 0 5 7,step_divides i 2 3 7,step_divides i 4 3 5,
      assemble_shape ⟨i,mem_range.mp hi⟩⟩
  · rintro ⟨a,b,c,ha,hb,hc,rfl⟩
    obtain ⟨i,hi,rfl,rfl,rfl⟩ := divisors_complete a (Nat.mem_divisors.mpr ⟨ha,by decide⟩)
      b (Nat.mem_divisors.mpr ⟨hb,by decide⟩) c (Nat.mem_divisors.mpr ⟨hc,by decide⟩)
    exact ⟨_,Finset.mem_image_of_mem shape hi,assemble_shape ⟨i,mem_range.mp hi⟩⟩

end GallianRusinDice
