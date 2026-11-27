module

public import conjectures.AlabamaParadox.Weights
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open Finset Filter
open scoped Topology
namespace AlabamaParadox

/-- Bound the frequency of an event using disjoint events in its complement.
The events need only be disjoint at the positive indices. -/
private theorem packing {β : Type*} [Fintype β] (E : ℕ → Prop) (B : β → ℕ → Prop)
    (uniq : ∀ n, 0 < n → ∀ b c, B b n → B c n → b = c)
    (disj : ∀ b n, B b n → ¬ E n) {N : ℕ} (hN : 0 < N) :
    frequency E N + ∑ b, frequency (B b) N ≤ 1+(Fintype.card β : ℝ)/N := by
  classical
  let hit (P : ℕ → Prop) (n : ℕ) : ℝ := if P n then 1 else 0
  have eqf (P : ℕ → Prop) : frequency P N = (∑ n ∈ range N, hit P n)/N := by
    simp [frequency,hit,sum_boole]
  have point (n : ℕ) : hit E n + ∑ b, hit (B b) n ≤
      1 + if n=0 then (Fintype.card β : ℝ) else 0 := by
    have cnt : ∑ b, hit (B b) n = (((univ.filter fun b => B b n).card : ℕ) : ℝ) := by
      simp [hit,sum_boole]
    rw [cnt]
    by_cases hn : n=0
    · have hc := card_le_univ (univ.filter fun b => B b n)
      have hr : (((univ.filter fun b => B b n).card : ℕ) : ℝ) ≤ Fintype.card β := by exact_mod_cast hc
      simp only [hn,ite_true] at hr ⊢
      dsimp [hit]
      split <;> linarith
    · simp only [hn,ite_false,add_zero]
      by_cases h : E n
      · have a : (univ.filter fun b => B b n) = ∅ := filter_false_of_mem
          (fun b _ hb => disj b n hb h)
        simp [hit,h,a]
      · have a : (univ.filter fun b => B b n).card ≤ 1 :=
          card_le_one_iff.mpr (fun {b c} hb hc => uniq n (Nat.pos_of_ne_zero hn) b c
            (mem_filter.mp hb).2 (mem_filter.mp hc).2)
        simp only [hit, h, ite_false, zero_add]
        exact_mod_cast a
  have pos : 0 < (N : ℝ) := by exact_mod_cast hN
  simp_rw [eqf]
  rw [← sum_div, ← add_div, div_le_iff₀ pos]
  rw [sum_comm (s:=univ) (t:=range N), ← sum_add_distrib]
  calc
    _ ≤ ∑ n ∈ range N, (1 + if n=0 then (Fintype.card β : ℝ) else 0) :=
      sum_le_sum (fun n _ => point n)
    _ = _ := by
      simp [sum_add_distrib,hN]
      field_simp

public theorem frequency_bound {m : ℕ} [NeZero m] [Nontrivial (Fin m)] (p : Fin m → ℝ)
    (hpos : ∀ i, 0 < p i) (hlt : ∀ i, p i < 1) (hs : ∑ i, p i = 1)
    (hi : IndependentShares p) {q : ℝ} (hq : Tendsto (frequency (Loss p)) atTop (𝓝 q)) :
    q ≤ 1-2/Real.exp 1 := by
  have lim := tendsto_finsetSum univ (fun b _ => box_limit hpos hlt hs hi b)
  have up : Tendsto (fun N : ℕ => 1+(Fintype.card (Label m):ℝ)/N) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (Fintype.card (Label m):ℝ))
  have h := le_of_tendsto_of_tendsto (hq.add lim) up (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact packing (Loss p) (Box p) (fun _ hn _ _ => box_unique hs hi hn)
      (fun _ _ => box_no_loss hpos hlt hs hi) hN)
  linarith [weights_bound hpos hlt hs]

end AlabamaParadox
