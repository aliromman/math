module

public import conjectures.SavchenkoSix.Statement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.LinearCombination

@[expose] public section
noncomputable section
namespace SavchenkoSix
open Matrix Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Excess of a principal determinant over that of a transitive tournament of even order. -/
def excess (M : Matrix V V ℤ) (s : Finset V) : ℤ :=
  (M.submatrix (Subtype.val : s→V) Subtype.val).det-1

def excessOn (M : Matrix V V ℤ) (U : Finset V) (k : ℕ) : ℤ :=
  ∑ s∈U.powersetCard k, excess M s

theorem excess_map (M : Matrix V V ℤ) (e : W ↪ V) (s : Finset W) :
    excess M (s.map e)=excess (M.submatrix e e) s := by
  unfold excess
  rw [←Matrix.det_submatrix_equiv_self (s.equivMap e)
    (M.submatrix (Subtype.val : s.map e→V) Subtype.val)]
  rfl

theorem excessOn_map (M : Matrix V V ℤ) (e : W ↪ V) (s : Finset W) (k : ℕ) :
    excessOn M (s.map e) k=excessOn (M.submatrix e e) s k := by
  simp only [excessOn,powersetCard_map,sum_map,mapEmbedding_apply,RelEmbedding.coe_toEmbedding,excess_map]

def switch (d : V→ℤ) (M : Matrix V V ℤ) : Matrix V V ℤ := fun i j ↦ d i*M i j*d j

theorem excess_switch (M : Matrix V V ℤ) (d : V→ℤ) (h : ∀ i,d i*d i=1) (s : Finset V) :
    excess (switch d M) s=excess M s := by
  let A : Matrix s s ℤ := M.submatrix (Subtype.val : s→V) Subtype.val
  let D : Matrix s s ℤ := diagonal (fun i ↦ d i)
  have eq : (switch d M).submatrix (Subtype.val : s→V) Subtype.val = D*A*D := by
    ext i j
    simp [D,A,switch,Matrix.mul_diagonal,Matrix.diagonal_mul]
  have square : D*D=1 := by
    simp only [D,diagonal_mul_diagonal,h,diagonal_one]
  have det2 := congrArg Matrix.det square
  rw [det_mul,det_one] at det2
  unfold excess
  rw [eq,det_mul,det_mul]
  change D.det*A.det*D.det-1=A.det-1
  linear_combination A.det*det2

theorem excessOn_switch (M : Matrix V V ℤ) (d : V→ℤ) (h : ∀ i,d i*d i=1) (s : Finset V) (k : ℕ) :
    excessOn (switch d M) s k=excessOn M s k := by
  simp only [excessOn,excess_switch M d h]

theorem sevenfold_sum (X : Finset V) (k : ℕ) (hk : k≤7) (f : Finset V→ℤ) :
    (∑ U∈X.powersetCard 7, ∑ s∈U.powersetCard k,f s) =
      ((X.card-k).choose (7-k) : ℤ)*∑ s∈X.powersetCard k,f s := by
  classical
  have inner (U : Finset V) (hU : U∈X.powersetCard 7) :
      ∑ s∈U.powersetCard k,f s=∑ s∈X.powersetCard k,if s⊆U then f s else 0 := by
    rw [←sum_filter]
    congr 1
    ext s
    simp only [mem_filter,mem_powersetCard]
    have sub := (mem_powersetCard.mp hU).1
    exact ⟨fun ⟨h,c⟩ ↦ ⟨⟨h.trans sub,c⟩,h⟩,fun ⟨⟨_,c⟩,h⟩ ↦ ⟨h,c⟩⟩
  rw [sum_congr rfl inner,sum_comm,mul_sum]
  apply sum_congr rfl
  intro s hs
  obtain ⟨sx,sz⟩ := mem_powersetCard.mp hs
  rw [←sum_filter,sum_const,card_filter_powersetCard_subset s X 7 sx (sz ▸ hk),sz,nsmul_eq_mul]

end SavchenkoSix
end
