module

public import conjectures.CampbellCoupons.Statement
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace CampbellCoupons
open Finset MvPolynomial

theorem counts_sum {k T : ℕ} (w : Fin T → Fin k) : ∑ i, counts w i = T := by
  simpa [counts] using sum_card_fiberwise_eq_card_filter (univ : Finset (Fin T))
    (univ : Finset (Fin k)) w

private theorem word_monomial {k T : ℕ} (w : Fin T → Fin k) :
    (∏ j, X (w j) : MvPolynomial (Fin k) ℕ) =
      monomial (Finsupp.equivFunOnFinite.symm (counts w)) 1 := by
  rw [show (∏ j, X (w j) : MvPolynomial (Fin k) ℕ) =
      monomial (∑ j, Finsupp.single (w j) 1) 1 from
    (monomial_sum_one univ (fun j => Finsupp.single (w j) 1)).symm]
  apply congrArg (fun d => (monomial d 1 : MvPolynomial (Fin k) ℕ))
  ext i
  simp [counts, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm,
    Finset.sum_boole]

/-- The coefficient of each occupancy vector counts the corresponding words. -/
theorem fiber_card {k T : ℕ} (f : Fin k → ℕ) (hf : ∑ i, f i = T) :
    (univ.filter fun w : Fin T → Fin k => counts w = f).card = Nat.multinomial univ f := by
  classical
  let d := Finsupp.equivFunOnFinite.symm f
  have hs : d.sum (fun _ n => n) = T := by
    rw [Finsupp.sum_of_support_subset d (Finset.subset_univ _) _ (by simp)]
    exact hf
  have h := coeff_sum_X_pow_of_fintype (R := ℕ) d T
  rw [ite_eq_left hs, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at h
  have hpow : (∑ i : Fin k, X i : MvPolynomial (Fin k) ℕ) ^ T =
      ∑ w : Fin T → Fin k, ∏ j, X (w j) := by
    simpa using Fintype.prod_sum (fun (_ : Fin T) (i : Fin k) => (X i : MvPolynomial (Fin k) ℕ))
  rw [hpow, coeff_sum] at h
  simpa [word_monomial, coeff_monomial, d, Finset.sum_boole] using h

def profiles (m k T : ℕ) : Finset (Fin k → ℕ) :=
  (piAntidiag univ T).filter fun f => ∀ i, m ≤ f i

@[simp] theorem mem_profiles {m k T : ℕ} {f : Fin k → ℕ} :
    f ∈ profiles m k T ↔ (∑ i, f i = T) ∧ ∀ i, m ≤ f i := by
  simp [profiles]

theorem winning_eq_sum (m k T : ℕ) :
    winning m k T = ∑ f ∈ profiles m k T, Nat.multinomial univ f := by
  classical
  calc
    winning m k T = (univ.filter fun w : Fin T → Fin k => counts w ∈ profiles m k T).card := by
      simp [winning, counts_sum]
    _ = ∑ f ∈ profiles m k T, (univ.filter fun w : Fin T → Fin k => counts w = f).card :=
      (sum_card_fiberwise_eq_card_filter _ _ _).symm
    _ = _ := sum_congr rfl fun f hf => fiber_card f (mem_profiles.mp hf).1

end CampbellCoupons
