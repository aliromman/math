module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card

public section
namespace SidonSetSystems

open Classical in
/-- A proper rational subspace contains at most `n ^ m` grid points in dimension `m + 1`. -/
theorem proper_row_count (m n : ℕ) (S : Submodule ℚ (Fin (m + 1) → ℚ)) (proper : S ≠ ⊤) :
    ((Finset.univ : Finset (Fin (m + 1) → Fin n)).filter
      (fun v : Fin (m + 1) → Fin n => (fun i => ((v i).val : ℚ)) ∈ S)).card ≤ n ^ m := by
  classical
  have omitted : ∃ i, Pi.single i (1 : ℚ) ∉ S := by
    by_contra! all
    apply proper
    apply top_unique
    intro v _
    rw [← LinearMap.sum_single_apply (fun _ : Fin (m + 1) => ℚ) v]
    apply S.sum_mem
    intro i _
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using S.smul_mem (v i) (all i)
  obtain ⟨i, hi⟩ := omitted
  let drop (v : Fin (m + 1) → Fin n) : Fin m → Fin n := fun j => v (i.succAbove j)
  have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (m + 1) → Fin n)).filter
      (fun v : Fin (m + 1) → Fin n => (fun k => ((v k).val : ℚ)) ∈ S))
    (t := Finset.univ) drop (fun _ _ => Finset.mem_univ _) (by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have common (j : Fin m) : a (i.succAbove j) = b (i.succAbove j) := congrFun hab j
      have pivot : a i = b i := by
        by_contra distinct
        let u : Fin (m + 1) → ℚ := fun j => ((a j).val : ℚ) - ((b j).val : ℚ)
        have uin : u ∈ S := S.sub_mem ha' hb'
        have ui : u i ≠ 0 := by
          dsimp [u]
          exact sub_ne_zero.mpr (by exact_mod_cast Fin.val_ne_of_ne distinct)
        apply hi
        convert S.smul_mem (u i)⁻¹ uin using 1
        funext j
        refine (Fin.forall_iff_succAbove (P := fun j => (Pi.single i (1 : ℚ) : Fin (m + 1) → ℚ) j = ((u i)⁻¹ • u) j) i).2 ⟨?_, ?_⟩ j
        · simp [ui]
        · intro k
          simp [u, common k, Fin.succAbove_ne]
      funext j
      exact (Fin.forall_iff_succAbove (P := fun j => a j = b j) i).2 ⟨pivot, common⟩ j)
  simpa [Fintype.card_fun] using hcard

end SidonSetSystems
