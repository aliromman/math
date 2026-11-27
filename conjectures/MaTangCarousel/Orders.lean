module

public import conjectures.MaTangCarousel.Colours
public import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.NormNum

@[expose] public section
namespace MaTangCarousel
open Finset

private def trueCount (b : Fin 6→Bool) : ℕ := (univ.filter (fun i ↦ b i=true)).card

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem colour_formula : ∀ b : Fin 6→Bool, colours b =
    3*(1+(trueCount b).choose 3+(if ∀ i,b i=true then 1 else 0)) := by
  decide +kernel

/-- The sum over the 720 orders of six distinct ranks. -/
private theorem sorted_orders :
    ∑ p : Equiv.Perm (Fin 6), colours (ascents (p : Fin 6→Fin 6)) = 5400 := by
  simp_rw [colour_formula]
  decide +kernel

private theorem order_average {m : ℕ} (r : Fin 6→Fin m) :
    (∑ p : Equiv.Perm (Fin 6), colours (ascents (r ∘ p))) ≤ 5400 := by
  let s := (Tuple.sort r).symm
  have ord {i j : Fin 6} (h : r i<r j) : s i<s j := by
    by_contra! hn
    have le := Tuple.monotone_sort r hn
    change r (Tuple.sort r (s j)) ≤ r (Tuple.sort r (s i)) at le
    simp only [s,Equiv.apply_symm_apply] at le
    exact h.not_ge le
  calc
    _ ≤ ∑ p : Equiv.Perm (Fin 6),colours (ascents ((s*p : Equiv.Perm (Fin 6)) : Fin 6→Fin 6)) := by
      apply sum_le_sum
      intro p _
      apply colours_mono
      intro i h
      exact decide_eq_true (ord (of_decide_eq_true h))
    _ = _ := (Equiv.sum_comp (Equiv.mulLeft s) (fun p : Equiv.Perm (Fin 6) ↦ colours (ascents (p : Fin 6→Fin 6)))).trans sorted_orders

private theorem exact_average {m : ℕ} (r : Fin 6↪Fin m) :
    (∑ p : Equiv.Perm (Fin 6), colours (ascents (r ∘ p))) = 5400 := by
  let s := (Tuple.sort (r : Fin 6→Fin m)).symm
  have strict := (Tuple.monotone_sort (r : Fin 6→Fin m)).strictMono_of_injective
    (r.injective.comp (Tuple.sort (r : Fin 6→Fin m)).injective)
  have rel (i j : Fin 6) : r i<r j ↔ s i<s j := by
    simpa only [s,Function.comp_apply,Equiv.apply_symm_apply] using
      (strict.lt_iff_lt (a:=s i) (b:=s j))
  calc
    _ = ∑ p : Equiv.Perm (Fin 6), colours (ascents ((s*p : Equiv.Perm (Fin 6)) : Fin 6→Fin 6)) := by
      apply sum_congr rfl
      intro p _
      apply congrArg colours
      funext i
      simp only [ascents,Function.comp_apply,rel,Equiv.Perm.mul_apply]
      rfl
    _ = _ := (Equiv.sum_comp (Equiv.mulLeft s) (fun p : Equiv.Perm (Fin 6) ↦ colours (ascents (p : Fin 6→Fin 6)))).trans sorted_orders

private theorem sum_orders (m : ℕ) :
    (∑ r : Fin 6→Fin m, ∑ p : Equiv.Perm (Fin 6),colours (ascents (r ∘ p))) =
      720*homCount (threeParts m) 6 := by
  rw [count_colours,sum_comm]
  have reindex (p : Equiv.Perm (Fin 6)) :
      (∑ r : Fin 6→Fin m,colours (ascents (r ∘ p))) = ∑ r : Fin 6→Fin m, colours (ascents r) :=
    (p.symm.arrowCongr (Equiv.refl (Fin m))).sum_comp (fun r ↦ colours (ascents r))
  simp only [reindex,sum_const,card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  norm_num [Nat.factorial]

/-- Ties in the ranks can only remove cycles. -/
theorem six_count (m : ℕ) : 2*homCount (threeParts m) 6 ≤ 15*m^6 := by
  have h := sum_le_sum (s:=univ) (fun (r : Fin 6→Fin m) _ ↦ order_average r)
  rw [sum_orders] at h
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul] at h
  change 720*homCount (threeParts m) 6 ≤ m^6*5400 at h
  omega

/-- Tuples with six distinct ranks give a lower bound with the same leading coefficient. -/
theorem six_count_lower (m : ℕ) : 15*(m+1-6)^6 ≤ 2*homCount (threeParts m) 6 := by
  classical
  let e : (Fin 6↪Fin m) ↪ (Fin 6→Fin m) := ⟨(⇑), DFunLike.coe_injective⟩
  let F (r : Fin 6→Fin m) := ∑ p : Equiv.Perm (Fin 6),colours (ascents (r ∘ p))
  have sub : ∑ r∈univ.map e,F r ≤ ∑ r,F r :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)
  have equal : ∑ r∈univ.map e,F r = (m.descFactorial 6)*5400 := by
    rw [sum_map]
    change (∑ r : Fin 6↪Fin m, ∑ p : Equiv.Perm (Fin 6),colours (ascents (r ∘ p))) = _
    simp [exact_average,Fintype.card_embedding_eq]
  rw [equal] at sub
  change _ ≤ ∑ r : Fin 6→Fin m,∑ p : Equiv.Perm (Fin 6),colours (ascents (r ∘ p)) at sub
  rw [sum_orders] at sub
  have h := Nat.pow_sub_le_descFactorial m 6
  omega

end MaTangCarousel
