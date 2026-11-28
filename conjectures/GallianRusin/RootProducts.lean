module

public import conjectures.GallianRusin.Die
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section
namespace GallianRusin
open Polynomial Finset
open scoped BigOperators

/-- Evaluate an integer polynomial at a complex number. -/
abbrev evalC (P : ℤ[X]) (z : ℂ) := P.eval₂ (Int.castRingHom ℂ) z

/-- A die polynomial on the unit circle has norm at most its number of faces. -/
theorem die_bound {P : ℤ[X]} {m} (h : Die m P) {z : ℂ} (unit : ‖z‖ = 1) :
    ‖evalC P z‖ ≤ m := by
  have total : (m : ℝ) = ((P.eval 1 : ℤ) : ℝ) := by exact_mod_cast h.2.symm
  rw [total, eval_eq_sum_range]
  change ‖P.eval₂ _ z‖ ≤ _
  rw [eval₂_eq_sum_range]
  apply (norm_sum_le ..).trans
  push_cast
  apply sum_le_sum
  intro i _
  have nonneg : (0 : ℝ) ≤ P.coeff i := by exact_mod_cast h.1 i
  simp [norm_pow, unit, Complex.norm_intCast, abs_of_nonneg nonneg]

/-- The product of the norms of the values of `H` at all complex roots of `f`, with multiplicity. -/
noncomputable abbrev normProduct (f H : ℤ[X]) : ℝ :=
  ((f.map (Int.castRingHom ℂ)).roots.map (fun z ↦ ‖evalC H z‖)).prod

/-- For monic `f`, the product over its roots is the absolute value of the resultant. -/
theorem normProduct_eq (f H : ℤ[X]) (mf : f.Monic) :
    normProduct f H = |(f.resultant H : ℝ)| := by
  let φ := Int.castRingHom ℂ
  have mf' := mf.map φ
  have eq : ((f.resultant H : ℤ) : ℂ) = ((f.map φ).roots.map (evalC H)).prod := by
    change φ (f.resultant H) = _
    rw [← resultant_map_map f H _ _ φ, ← mf.natDegree_map φ,
      resultant_eq_prod_eval _ _ _ (natDegree_map_le ..) (IsAlgClosed.splits _), mf'.leadingCoeff]
    simp [eval_map, φ, evalC]
  rw [← Complex.norm_intCast, eq]
  simp [normProduct, φ]

/-- If `H` has no zero among the roots of monic `f`, the product is at least one. -/
theorem one_le_normProduct {f H : ℤ[X]} (mf : f.Monic)
    (nonzero : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, evalC H z ≠ 0) :
    1 ≤ normProduct f H := by
  have hn : normProduct f H ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro bad
    obtain ⟨z, hz, e⟩ := Multiset.mem_map.mp bad
    exact nonzero z hz (norm_eq_zero.mp e)
  rw [normProduct_eq _ _ mf] at hn ⊢
  have nz : f.resultant H ≠ 0 := fun h ↦ hn (by simp [h])
  exact_mod_cast Int.one_le_abs nz

end GallianRusin
