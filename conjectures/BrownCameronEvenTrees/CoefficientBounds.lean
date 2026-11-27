module

public import conjectures.BrownCameronEvenTrees.IndependencePolynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open Finset

namespace BrownCameron

/-- The Eneström–Kakeya estimate for a polynomial with nonnegative integer coefficients. -/
theorem root_bound (a : ℕ → ℕ) (R d : ℕ) (hR : 0 < R) (ha : 0 < a d)
    (hr : ∀ j < d, a j ≤ R * a (j+1)) (z : ℂ)
    (hz : ∑ j ∈ range (d+1), (a j : ℂ) * z^j = 0) : ‖z‖ ≤ (R : ℝ) := by
  by_contra! h
  let P (t : ℕ) := ∑ j ∈ range (t+1), (a j : ℂ) * z^j
  have key (t : ℕ) (ht : t ≤ d) :
      ‖((R : ℂ) - z)*P t + (a t : ℂ)*z^(t+1)‖ ≤ R * (a t : ℝ) * ‖z‖^t := by
    induction t with
    | zero =>
      simp [P, sub_mul, mul_comm z]
    | succ t ih =>
      have iht := ih (by omega)
      have ht' : t < d := by omega
      have hcoeff : 0 ≤ (R : ℝ) * a (t+1) - a t := sub_nonneg.mpr (by exact_mod_cast hr t ht')
      have eqn : ((R : ℂ)-z)*P (t+1) + (a (t+1) : ℂ)*z^(t+1+1) =
          ((R-z)*P t + (a t : ℂ)*z^(t+1)) +
          (((R : ℂ)*a (t+1) - a t)*z^(t+1)) := by
        simp only [P, sum_range_succ, pow_succ]
        ring
      rw [eqn]
      calc
        _ ≤ _ := norm_add_le _ _
        _ ≤ R * (a t : ℝ) * ‖z‖^t +
            ((R : ℝ)*a (t+1) - a t)*‖z‖^(t+1) := by
              refine add_le_add iht ?_
              rw [norm_mul, norm_pow]
              have hm : (R : ℂ)*a (t+1) - a t =
                  ((R : ℝ)*a (t+1) - a t : ℝ) := by norm_cast
              rw [hm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoeff]
        _ ≤ _ := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (a t)) (pow_nonneg (norm_nonneg z) t)) (sub_nonneg.mpr h.le)]
  have hP : P d = 0 := hz
  have last := key d le_rfl
  rw [hP, mul_zero, zero_add, norm_mul, norm_pow, Complex.norm_natCast, pow_succ] at last
  have nz : 0 < ‖z‖ := lt_trans (by exact_mod_cast hR) h
  have hp : 0 < (a d : ℝ) * ‖z‖^d := by positivity
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem mem_layer {j : ℕ} {s : Finset V} :
    s ∈ layer G j ↔ G.IsNIndepSet j s := by
  classical
  simp [layer]

omit [DecidableEq V] in
theorem choose_le_layer (s : Finset V) (hs : G.IsIndepSet s) (j : ℕ) :
    s.card.choose j ≤ (layer G j).card := by
  rw [← card_powersetCard]
  apply card_le_card
  intro t ht
  have hm := mem_powersetCard.mp ht
  exact mem_layer.mpr ⟨hs.mono hm.1, hm.2⟩

/-- Every omitted vertex has a neighbor already in the set. -/
def saturated (G : SimpleGraph V) (t : Finset V) : Prop :=
  ∀ v, v ∉ t → ∃ w ∈ t, G.Adj v w

noncomputable def maximalLayer (G : SimpleGraph V) (j : ℕ) : Finset (Finset V) := by
  classical
  exact (layer G j).filter (saturated G)

omit [DecidableEq V] in
theorem mem_maximal {j : ℕ} {t : Finset V} :
    t ∈ maximalLayer G j ↔ G.IsNIndepSet j t ∧ saturated G t := by
  classical
  simp [maximalLayer, mem_layer]

omit [Fintype V] in
theorem add_indep {t : Finset V} {v : V} (ht : G.IsIndepSet t)
    (h : ∀ w ∈ t, ¬ G.Adj v w) : G.IsIndepSet (insert v t : Finset V) := by
  rw [coe_insert,SimpleGraph.isIndepSet_iff]
  exact Set.Pairwise.insert ht (fun w hw _ => ⟨h w hw,fun a => h w hw a.symm⟩)

/-- Count the independent sets of size `j` by extensions and maximal sets. -/
theorem consecutive (G : SimpleGraph V) (j : ℕ) :
    (layer G j).card ≤ (layer G (j+1)).card * (j+1) + (maximalLayer G j).card := by
  classical
  let E := (layer G (j+1)).biUnion fun t => t.powersetCard j
  have hs : layer G j ⊆ E ∪ maximalLayer G j := by
    intro t ht
    obtain ⟨hi, hc⟩ := mem_layer.mp ht
    by_cases hm : saturated G t
    · exact mem_union_right _ (mem_maximal.mpr ⟨⟨hi,hc⟩,hm⟩)
    rw [saturated] at hm
    push Not at hm
    obtain ⟨v, hv, hn⟩ := hm
    refine mem_union_left _ (mem_biUnion.mpr ⟨insert v t, mem_layer.mpr ⟨?_, ?_⟩, ?_⟩)
    · exact add_indep hi hn
    · simp [hv,hc]
    · exact mem_powersetCard.mpr ⟨subset_insert _ _,hc⟩
  have hE : E.card ≤ (layer G (j+1)).card * (j+1) := by
    apply card_biUnion_le_card_mul
    intro t ht
    simp [card_powersetCard, (mem_layer.mp ht).card_eq, Nat.choose_succ_self_right]
  exact (card_le_card hs).trans (card_union_le _ _ |>.trans (Nat.add_le_add_right hE _))

/-- The part outside a fixed independent set determines each maximal independent set. -/
theorem diff_injective {j : ℕ} (S : Finset V) (hS : G.IsIndepSet S) :
    Set.InjOn (fun t : Finset V => t \ S) (maximalLayer G j) := by
  intro t ht u hu he
  obtain ⟨it,st⟩ := mem_maximal.mp ht
  obtain ⟨iu,su⟩ := mem_maximal.mp hu
  have sub {t u : Finset V} (hI : G.IsIndepSet t) (sat : saturated G u)
      (eqd : t \ S = u \ S) : t ⊆ u := by
    intro v hv
    by_contra hn
    obtain ⟨w, hw, adj⟩ := sat v hn
    have vs : v ∈ S := by
      by_contra hs
      have h : v ∈ u \ S := eqd ▸ mem_sdiff.mpr ⟨hv,hs⟩
      exact hn (mem_sdiff.mp h).1
    have ws : w ∉ S := fun xp => hS vs xp adj.ne adj
    have h : w ∈ t \ S := eqd ▸ mem_sdiff.mpr ⟨hw,ws⟩
    exact hI hv (mem_sdiff.mp h).1 adj.ne adj
  exact Subset.antisymm (sub it.isIndepSet su he) (sub iu.isIndepSet st he.symm)

theorem diff_nonempty {j : ℕ} {S t : Finset V} (hS : G.IsIndepSet S)
    (hj : j < S.card) (ht : t ∈ maximalLayer G j) : (t \ S).Nonempty := by
  obtain ⟨it,st⟩ := mem_maximal.mp ht
  by_contra! he
  have sub : t ⊆ S := sdiff_eq_empty_iff_subset.mp he
  obtain ⟨v, hvS, hvt⟩ := exists_mem_notMem_of_card_lt_card (it.card_eq.trans_lt hj)
  obtain ⟨w, hw, adj⟩ := st v hvt
  exact hS hvS (sub hw) adj.ne adj

end BrownCameron
