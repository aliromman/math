module

public import conjectures.AlabamaParadox.Boxes
public import conjectures.AlabamaParadox.Bernoulli
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset
namespace AlabamaParadox

variable {m : ℕ} {p : Fin m → ℝ}

private theorem omit_sum (i : Fin m) (hlt : ∀ j, p j < 1) :
    ∑ t : Option (Other i), weight p ⟨i,t⟩ =
      (∏ j : Other i, (1-p j))*(1+∑ j : Other i, p j/(1-p j))/m := by
  classical
  let P := ∏ j : Other i, (1-p j)
  have none_weight : weight p ⟨i,none⟩ = P/m := by simp [weight, upper, lower, P]
  have some_weight (k : Other i) : weight p ⟨i,some k⟩ = P*(p k/(1-p k))/m := by
    have h (j : Other i) : upper p (some k) j - lower p (some k) j =
        (1-p j)*(if k=j then p k/(1-p k) else 1) := by
      by_cases e : k = j
      · subst j
        simp [upper,lower]
        field_simp [show 1-p k ≠ 0 by linarith [hlt k]]
      · simp [upper,lower,e]
    unfold weight
    dsimp only
    simp_rw [h, prod_mul_distrib]
    simp [P]
  rw [Fintype.sum_option, none_weight]
  simp_rw [some_weight]
  rw [← sum_div, ← mul_sum, ← add_div]
  dsimp [P]
  ring

public theorem weights_bound [NeZero m] (hpos : ∀ j, 0 < p j) (hlt : ∀ j, p j < 1)
    (hs : ∑ j, p j = 1) : 2/Real.exp 1 ≤ ∑ b : Label m, weight p b := by
  let Q := ∏ j, (1-p j)
  let R := ∑ j, p j/(1-p j)
  have W (i : Fin m) : Q*(1+R)/m ≤ ∑ t : Option (Other i), weight p ⟨i,t⟩ := by
    rw [omit_sum i hlt]
    apply div_le_div_of_nonneg_right _ (by positivity)
    let e := Equiv.optionSubtypeNe i
    have qp : Q = (1-p i)*∏ j : Other i, (1-p j) := by
      dsimp [Q]; rw [← e.prod_comp, Fintype.prod_option]; rfl
    have rs : R = p i/(1-p i) + ∑ j : Other i, p j/(1-p j) := by
      dsimp [R]; rw [← e.sum_comp, Fintype.sum_option]; rfl
    have Z : 0 ≤ ∏ j : Other i, (1-p j) := prod_nonneg (fun j _ => by linarith [hlt j])
    have S : 0 ≤ ∑ j : Other i, p j/(1-p j) :=
      sum_nonneg (fun j _ => div_nonneg (hpos j).le (by linarith [hlt j]))
    rw [qp,rs]
    have h := mul_nonneg (hpos i).le S
    have E : (1-p i)*(p i/(1-p i)) = p i := by
      field_simp [show 1-p i ≠ 0 by linarith [hlt i]]
    rw [mul_assoc, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ Z
    nlinarith
  have all := sum_le_sum (s:=univ) (fun i _ => W i)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel₀ _ (by exact_mod_cast (NeZero.ne m)), ← Fintype.sum_sigma] at all
  exact (at_most_one p hpos hlt hs).trans all

end AlabamaParadox
