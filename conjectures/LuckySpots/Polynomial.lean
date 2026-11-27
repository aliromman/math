module

public import conjectures.LuckySpots.Statement
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
namespace LuckySpots
open Finset Polynomial

noncomputable def weight (j h : ℕ) : ℚ := (j:ℚ)^h/(2*j*h.factorial)

noncomputable def basis (j h : ℕ) : ℚ[X] :=
  descPochhammer ℚ h * (X+C (1-(j:ℚ)))^(j-2-h)

/-- The correction to the lucky-spot count, as a polynomial in the street length. -/
noncomputable def correction (j : ℕ) : ℚ[X] :=
  ∑ h ∈ range (j-1), C (weight j h) * basis j h

private theorem shape (j h : ℕ) (hh : h≤j-2) : (basis j h).natDegree=j-2 ∧ (basis j h).Monic := by
  have m := (monic_X_add_C (1-(j:ℚ))).pow (j-2-h)
  refine ⟨?_, (monic_descPochhammer ℚ h).mul m⟩
  rw [basis,natDegree_mul (monic_descPochhammer ℚ h).ne_zero m.ne_zero,descPochhammer_natDegree,
    (monic_X_add_C _).natDegree_pow,natDegree_X_add_C]
  omega

private theorem positive_weight {j : ℕ} (hj : 0<j) (h : ℕ) : 0<weight j h := by
  unfold weight
  positivity

theorem degree_correction {j : ℕ} (hj : 2≤j) : (correction j).natDegree=j-2 ∧ correction j ≠ 0 := by
  have top (h) (hh : h∈range (j-1)) := shape j h (by have := mem_range.mp hh; omega)
  have positive : 0 < (correction j).coeff (j-2) := by
    simp only [correction,finsetSum_coeff,coeff_C_mul]
    apply sum_pos
    · intro h hh
      obtain ⟨deg,m⟩ := top h hh
      rw [←deg,m.coeff_natDegree,mul_one]
      exact positive_weight (by omega) h
    · exact ⟨0,mem_range.mpr (by omega)⟩
  refine ⟨natDegree_eq_of_le_of_coeff_ne_zero ?_ positive.ne',fun h ↦ ?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro h hh
    exact (natDegree_C_mul_le _ _).trans (top h hh).1.le
  · simp [h] at positive

theorem correction_identity {n j : ℕ} (hj : 2≤j) (hn : j≤n) :
    2*(j:ℚ)*((correction j).eval (n:ℚ)*((n-j+1:ℕ):ℚ)^(n-j+1)) =
    ∑ h∈range (j-1), (n.choose h:ℚ)*(j:ℚ)^h*((n-j+1:ℕ):ℚ)^(n-1-h) := by
  have cast : ((n-j+1:ℕ):ℚ)=(n:ℚ)+(1-j) := by rw [Nat.cast_add,Nat.cast_sub hn]; ring
  simp only [correction,eval_finsetSum,eval_mul,eval_C,basis,eval_pow,eval_add,eval_X]
  rw [sum_mul,mul_sum]
  apply sum_congr rfl
  intro h hh
  have dh := mem_range.mp hh
  rw [Nat.cast_choose_eq_descPochhammer_div,show n-1-h=(j-2-h)+(n-j+1) by omega,pow_add,cast]
  have hj' : (j:ℚ)≠0 := by positivity
  have hf : (h.factorial:ℚ)≠0 := by positivity
  unfold weight
  field_simp
  rw [pow_add,pow_succ]
  ring

end LuckySpots
