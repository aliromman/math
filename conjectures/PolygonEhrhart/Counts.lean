module

public import conjectures.PolygonEhrhart.Statement
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

@[expose] public section
namespace PolygonEhrhart
open Finset

theorem pointCount_pos (n t : ℕ) : 0 < pointCount n t := by
  classical
  simp only [pointCount,sum_pos_iff,mem_univ,true_and]
  exact ⟨0,0,fun _ ↦ 0,fun _ ↦ 0,by simp [Valid]⟩

theorem pointCount_bound (n t : ℕ) : pointCount n t ≤ (t+1)^(2*n+2) := by
  classical
  unfold pointCount
  calc
    _ ≤ ∑ _lo : Fin (t+1), ∑ _hi : Fin (t+1),
        ∑ _v : Fin n → Fin (t+1), ∑ _e : Fin n → Fin (t+1), (1 : ℕ) := by
      apply sum_le_sum;intro a _
      apply sum_le_sum;intro b _
      apply sum_le_sum;intro v _
      apply sum_le_sum;intro e _
      split <;> omega
    _ = _ := by
      simp only [sum_const, card_univ,Fintype.card_fin,Fintype.card_fun,nsmul_eq_mul,mul_one,Nat.cast_id]
      rw [show 2*n+2=1+(1+(n+n)) by omega]
      simp only [pow_add,pow_one]

/-- At a fixed bottom and top height, only the two incident vertex-edge inequalities remain. -/
def crownValid {n w : ℕ} (v e : Fin n → Fin (w+1)) : Prop :=
  ∀ i, v i≤e i ∧ v (next i)≤e i

noncomputable def crownCount (n w : ℕ) : ℕ := by
  classical
  exact ∑ v : Fin n → Fin (w+1), ∑ e : Fin n → Fin (w+1), if crownValid v e then 1 else 0

open scoped Classical in
private theorem pair_count {A : Type*} [Fintype A] (P : A → A → Prop) :
    (∑ x,∑ y,if P x y then 1 else 0) = Fintype.card {q : A × A // P q.1 q.2} := by
  classical
  rw [Fintype.card_subtype]
  calc
    _ = ∑ q : A × A,if P q.1 q.2 then 1 else 0 := (Fintype.sum_prod_type _).symm
    _ = _ := by simp

open scoped Classical in
private theorem inner {n t : ℕ} (lo hi : Fin (t+1)) (bh : lo≤hi) :
    (∑ v : Fin n → Fin (t+1),∑ e : Fin n → Fin (t+1),if Valid lo hi v e then 1 else 0) =
      crownCount n (hi.val-lo.val) := by
  classical
  let w := hi.val-lo.val
  let down (x : Fin (t+1)) (lb : lo≤x) (ub : x≤hi) : Fin (w+1) :=
    ⟨x.val-lo.val,by dsimp [w];change lo.val≤x.val at lb;change x.val≤hi.val at ub;omega⟩
  let up (x : Fin (w+1)) : Fin (t+1) :=
    ⟨lo.val+x.val,by have := x.isLt;have := hi.isLt;dsimp [w] at *;change lo.val≤hi.val at bh;omega⟩
  let A := Fin n → Fin (t+1)
  let B := Fin n → Fin (w+1)
  let narrow (q : {q : A×A // Valid lo hi q.1 q.2}) : {q : B×B // crownValid q.1 q.2} :=
    ⟨(fun i ↦ down (q.val.1 i) (q.property.2 i).1 (q.property.2 i).2.1,
      fun i ↦ down (q.val.2 i) (q.property.2 i).2.2.1 (q.property.2 i).2.2.2.1), by
      intro i
      exact ⟨Nat.sub_le_sub_right (q.property.2 i).2.2.2.2.1 _,
        Nat.sub_le_sub_right (q.property.2 i).2.2.2.2.2 _⟩⟩
  let widen (q : {q : B×B // crownValid q.1 q.2}) : {q : A×A // Valid lo hi q.1 q.2} :=
    ⟨(fun i ↦ up (q.val.1 i), fun i ↦ up (q.val.2 i)), bh, by
      intro i
      have lehi (x : Fin (w+1)) : up x≤hi := by
        change lo.val+x.val≤hi.val
        have := x.isLt;dsimp [w] at this;change lo.val≤hi.val at bh;omega
      exact ⟨Nat.le_add_right _ _,lehi _,Nat.le_add_right _ _,lehi _,
        Nat.add_le_add_left (q.property i).1 _,Nat.add_le_add_left (q.property i).2 _⟩⟩
  let eqv : {q : A×A // Valid lo hi q.1 q.2} ≃ {q : B×B // crownValid q.1 q.2} :=
    ⟨narrow,widen,by
      intro q
      apply Subtype.ext
      apply Prod.ext <;> funext i <;> apply Fin.ext
      · exact Nat.add_sub_of_le (q.property.2 i).1
      · exact Nat.add_sub_of_le (q.property.2 i).2.2.1,
      by
        intro q
        apply Subtype.ext
        apply Prod.ext <;> funext i <;> apply Fin.ext <;> exact Nat.add_sub_cancel_left _ _⟩
  exact (pair_count (Valid lo hi)).trans ((Fintype.card_congr eqv).trans (pair_count crownValid).symm)

theorem pointCount_layers (n t : ℕ) :
    pointCount n t = ∑ lo : Fin (t+1), ∑ hi : Fin (t+1),
      if lo≤hi then crownCount n (hi.val-lo.val) else 0 := by
  classical
  unfold pointCount
  apply sum_congr rfl;intro lo _
  apply sum_congr rfl;intro hi _
  split_ifs with bh
  · exact inner (n:=n) lo hi bh
  · simp [Valid,bh]

end PolygonEhrhart
