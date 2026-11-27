module

public import conjectures.SavchenkoSix.PathOrder
public import conjectures.SavchenkoSix.Pfaffians
public import conjectures.SavchenkoSix.SevenCube
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

@[expose] public section
namespace SavchenkoSix
open Finset Matrix

private def vertexSet {k : ℕ} (u : Fin k → Fin 7) : Finset (Fin 7) := univ.image u

private theorem excess_tuple {k : ℕ} (M : Matrix (Fin 7) (Fin 7) ℤ)
    (u : Fin k → Fin 7) (h : Function.Injective u) :
    excess M (vertexSet u) = (M.submatrix u u).det-1 := by
  let e : Fin k ↪ Fin 7 := ⟨u,h⟩
  have eq : vertexSet u = (univ : Finset (Fin k)).map e := by
    ext i; simp [vertexSet,e]
  rw [eq, excess_map]
  unfold excess
  let E : Fin k ≃ (univ : Finset (Fin k)) :=
    ⟨fun i ↦ ⟨i,mem_univ _⟩,Subtype.val,fun _ ↦ rfl,fun _ ↦ rfl⟩
  rw [← det_submatrix_equiv_self E
    ((M.submatrix e e).submatrix (Subtype.val : {i : Fin k // i ∈ (univ : Finset (Fin k))} → Fin k) Subtype.val)]
  rfl

private def tuple4 : Fin 35 → Fin 4 → Fin 7 :=
  ![![0,1,2,3], ![0,1,2,4], ![0,1,2,5], ![0,1,2,6],
    ![0,1,3,4], ![0,1,3,5], ![0,1,3,6], ![0,1,4,5],
    ![0,1,4,6], ![0,1,5,6], ![0,2,3,4], ![0,2,3,5],
    ![0,2,3,6], ![0,2,4,5], ![0,2,4,6], ![0,2,5,6],
    ![0,3,4,5], ![0,3,4,6], ![0,3,5,6], ![0,4,5,6],
    ![1,2,3,4], ![1,2,3,5], ![1,2,3,6], ![1,2,4,5],
    ![1,2,4,6], ![1,2,5,6], ![1,3,4,5], ![1,3,4,6],
    ![1,3,5,6], ![1,4,5,6], ![2,3,4,5], ![2,3,4,6],
    ![2,3,5,6], ![2,4,5,6], ![3,4,5,6]]

private def term4 (M : Matrix (Fin 7) (Fin 7) ℤ) (i : Fin 35) : ℤ :=
  (pf4 M (tuple4 i 0) (tuple4 i 1) (tuple4 i 2) (tuple4 i 3))^2-1

private theorem eval4 (M : Matrix (Fin 7) (Fin 7) ℤ) (anti : ∀ i j,M j i= -M i j) :
    excessOn M univ 4 = ∑ i,term4 M i := by
  have inj : ∀ i, Function.Injective (tuple4 i) := by decide
  have distinct : Function.Injective (fun i ↦ vertexSet (tuple4 i)) := by decide
  have cover : (univ.image (fun i ↦ vertexSet (tuple4 i))) = univ.powersetCard 4 := by decide
  rw [excessOn,← cover,sum_image distinct.injOn]
  apply sum_congr rfl
  intro i _
  rw [excess_tuple M _ (inj i),det_skew4 (M.submatrix (tuple4 i) (tuple4 i)) (fun a b ↦ anti _ _)]
  rfl

private def tuple6 : Fin 7 → Fin 6 → Fin 7 :=
  ![![0,1,2,3,4,5], ![0,1,2,3,4,6], ![0,1,2,3,5,6], ![0,1,2,4,5,6],
    ![0,1,3,4,5,6], ![0,2,3,4,5,6], ![1,2,3,4,5,6]]

private def term6 (M : Matrix (Fin 7) (Fin 7) ℤ) (i : Fin 7) : ℤ :=
  (pf6 M (tuple6 i 0) (tuple6 i 1) (tuple6 i 2) (tuple6 i 3) (tuple6 i 4) (tuple6 i 5))^2-1

private theorem eval6 (M : Matrix (Fin 7) (Fin 7) ℤ) (anti : ∀ i j,M j i= -M i j) :
    excessOn M univ 6 = ∑ i,term6 M i := by
  have inj : ∀ i, Function.Injective (tuple6 i) := by decide
  have distinct : Function.Injective (fun i ↦ vertexSet (tuple6 i)) := by decide
  have cover : (univ.image (fun i ↦ vertexSet (tuple6 i))) = univ.powersetCard 6 := by decide
  rw [excessOn,← cover,sum_image distinct.injOn]
  apply sum_congr rfl
  intro i _
  rw [excess_tuple M _ (inj i),det_skew6 (M.submatrix (tuple6 i) (tuple6 i)) (fun a b ↦ anti _ _)]
  rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
private theorem score_eq (bits : Fin 15 → Bool) :
    Seven.score bits=3*(∑ i,term4 (bitsMatrix bits) i)-
      (∑ i,term6 (bitsMatrix bits) i) := by
  simp only [term4,term6,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_ofNat]
  simp only [Seven.score, Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  simp only [add_assoc]
  rfl


/-- On seven vertices, six-vertex principal minors have at most three times the
total excess of four-vertex principal minors. -/
theorem seven_checked (bits : Fin 15 → Bool) :
    excessOn (bitsMatrix bits) univ 6 ≤ 3 * excessOn (bitsMatrix bits) univ 4 := by
  obtain ⟨b,h0,h2,h5,h9,h14,eq⟩ := seven_path bits
  rw [eq 6,eq 4]
  have h := Seven.score_nonneg b h0 h2 h5 h9 h14
  rw [score_eq] at h
  rw [eval6 _ (bitsMatrix_flip b),eval4 _ (bitsMatrix_flip b)]
  exact sub_nonneg.mp h

end SavchenkoSix
