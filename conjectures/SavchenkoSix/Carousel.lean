module

public import conjectures.SavchenkoSix.Pfaffians
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

@[expose] public section
namespace SavchenkoSix
open Finset Matrix

theorem carousel_regular (r : ℕ) : Regular r (carousel r) := by
  intro x
  let gap (y : Fin (2*r+1)) :=
    if x.val < y.val then y.val - x.val else 2*r+1+y.val-x.val
  have spec (y : Fin (2*r+1)) :
      (carousel r).arc x y = true ↔ gap y ∈ Icc 1 r := by
    simp only [carousel, decide_eq_true_eq, mem_Icc, gap]
    split <;> omega
  have hx := x.isLt
  calc
    _ = (Icc 1 r).card := by
      apply card_bij (fun y _ ↦ gap y)
      · intro y hy
        exact (spec y).mp (mem_filter.mp hy).2
      · intro y _ z _ eq
        apply Fin.ext
        have hy := y.isLt
        have hz := z.isLt
        simp only [gap] at eq
        split at eq <;> split at eq <;> omega
      · intro t ht
        obtain ⟨ht1, htr⟩ := mem_Icc.mp ht
        let y : Fin (2*r+1) :=
          ⟨if x.val + t < 2*r+1 then x.val+t else x.val+t-(2*r+1), by split <;> omega⟩
        have hyt : gap y = t := by
          dsimp [gap, y]
          split_ifs <;> omega
        exact ⟨y, mem_filter.mpr ⟨mem_univ _, (spec y).mpr (hyt ▸ ht)⟩, hyt⟩
    _ = r := by simp

/-- Doubling the clockwise positions orders the two halves in alternation. -/
private def rankEmb (r : ℕ) : Fin (2*r+1) ↪ ℕ where
  toFun i := if i.val ≤ r then 2*i.val else 2*(i.val-r-1)+1
  inj' := by
    intro i j eq
    apply Fin.ext
    dsimp only at eq
    split at eq <;> split at eq <;> omega

private theorem rank_apply (r : ℕ) (i : Fin (2*r+1)) :
    rankEmb r i = if i.val ≤ r then 2*i.val else 2*(i.val-r-1)+1 := rfl

private def switchSign (r : ℕ) (i : Fin (2*r+1)) : ℤ := if i.val ≤ r then 1 else -1

private def orderedSign (V : Type*) [LinearOrder V] : Matrix V V ℤ :=
  fun i j ↦ if i < j then 1 else if j < i then -1 else 0

private theorem carousel_switch (r : ℕ) : (carousel r).sign =
    switch (switchSign r) ((orderedSign ℕ).submatrix (rankEmb r) (rankEmb r)) := by
  ext i j
  by_cases same : i = j
  · subst j
    simp [Tournament.sign, switch, orderedSign]
  have ne : i.val ≠ j.val := fun e ↦ same (Fin.ext e)
  have hi := i.isLt
  have hj := j.isLt
  simp only [Tournament.sign, same, ite_false, carousel, decide_eq_true_eq, switch,
    switchSign, orderedSign, submatrix_apply, rank_apply]
  split_ifs <;> first | rfl | omega

private theorem carousel_excess_eq (r k : ℕ) (s : Finset (Fin (2*r+1))) (hs : s.card = k) :
    excess (carousel r).sign s = (orderedSign (Fin k)).det - 1 := by
  let e := rankEmb r
  let t := s.map e
  have ht : t.card = k := by simpa [t] using hs
  let g := t.orderIsoOfFin ht
  rw [carousel_switch, excess_switch _ _ (fun i ↦ by simp only [switchSign]; split <;> decide),
    ← excess_map]
  change excess (orderedSign ℕ) t = _
  unfold excess
  rw [← det_submatrix_equiv_self g.toEquiv]
  congr 2
  ext i j
  change (if ((g i : t) : ℕ) < (g j : ℕ) then (1 : ℤ) else
    if ((g j : t) : ℕ) < (g i : ℕ) then -1 else 0) = _
  have lt (i j : Fin k) : ((g i : t) : ℕ) < (g j : ℕ) ↔ i < j := g.lt_iff_lt
  simp only [lt, orderedSign]

private theorem carousel_excessOn_zero (r k : ℕ) (h : (orderedSign (Fin k)).det = 1) :
    excessOn (carousel r).sign univ k = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  rw [carousel_excess_eq r k s (mem_powersetCard.mp hs).2, h, sub_self]

private theorem ordered_anti {V : Type*} [LinearOrder V] (i j : V) :
    orderedSign V j i = -orderedSign V i j := by
  rcases lt_trichotomy i j with h | h | h
  · simp [orderedSign, h, not_lt_of_gt h]
  · simp [orderedSign, h]
  · simp [orderedSign, h, not_lt_of_gt h]

theorem carousel_excess_four (r : ℕ) : excessOn (carousel r).sign univ 4 = 0 := by
  apply carousel_excessOn_zero
  rw [det_skew4 _ ordered_anti]
  decide

theorem carousel_excess_six (r : ℕ) : excessOn (carousel r).sign univ 6 = 0 := by
  apply carousel_excessOn_zero
  rw [det_skew6 _ ordered_anti]
  decide

end SavchenkoSix
