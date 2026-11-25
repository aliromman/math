module

public import conjectures.HwangPermanent.Statement
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

public section

namespace HwangPermanent

open Finset

private theorem memInf {ι α : Type*} [Fintype α] [DecidableEq α] (s : Finset ι)
    (f : ι → Finset α) (x : α) : x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  classical
  induction s using Finset.induction_on <;> simp_all

/-- Ryser's formula counts bijections by excluding maps that miss a row. -/
private theorem ryser {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    M.permanent = ∑ S ∈ (univ : Finset (Fin n)).powerset,
      (-1 : ℤ) ^ S.card * ∏ i, ∑ j ∈ Sᶜ, M j i := by
  classical
  let miss (j : Fin n) := (univ : Finset (Fin n → Fin n)).filter fun f ↦ ∀ i, f i ≠ j
  let w (f : Fin n → Fin n) := ∏ i, M (f i) i
  have hperm : univ.inf (fun j : Fin n ↦ (miss j)ᶜ) =
      (univ : Finset (Fin n → Fin n)).filter Function.Bijective := by
    ext f
    simp only [memInf, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
      true_and, forall_const, not_forall, not_not, miss]
    exact Finite.surjective_iff_bijective
  have hsub (S : Finset (Fin n)) : S.inf miss = Fintype.piFinset (fun _ : Fin n ↦ Sᶜ) := by
    ext f
    simp only [memInf, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset, Finset.mem_compl, miss]
    grind
  calc
    M.permanent = ∑ f ∈ univ.filter Function.Bijective, w f := by
      unfold Matrix.permanent
      refine Finset.sum_bij' (fun (σ : Equiv.Perm (Fin n)) _ ↦ (σ : Fin n → Fin n))
        (fun f hf ↦ Equiv.ofBijective f (Finset.mem_filter.mp hf).2) ?_ ?_ ?_ ?_ ?_
      · intro σ _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩
      · simp
      · intro σ _
        exact Equiv.ext fun _ ↦ rfl
      · intro f _
        rfl
      · intro σ _
        rfl
    _ = ∑ S ∈ (univ : Finset (Fin n)).powerset, (-1 : ℤ) ^ S.card • ∑ f ∈ S.inf miss, w f := by
      rw [← hperm]
      exact Finset.inclusion_exclusion_sum_inf_compl _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      rw [hsub, Int.zsmul_eq_mul, ← Finset.sum_prod_piFinset]

/-- The four cells of the counterexample, in zero-based coordinates. -/
def witness : Finset (Fin 8 × Fin 8) := {(0, 7), (1, 5), (1, 6), (2, 6)}

set_option maxRecDepth 100000 in
theorem exact_permanents :
    (board 8 (antidiagonal 8 4)).permanent = 584 ∧ (board 8 witness).permanent = 589 := by
  rw [ryser, ryser]
  decide +kernel

theorem resolution : ¬ Conjecture := by
  intro h
  have hle := h 8 4 (by decide) (by decide) witness (by decide) (by decide)
  rw [exact_permanents.1, exact_permanents.2] at hle
  contradiction

/-- info: 'HwangPermanent.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end HwangPermanent
