module

public import conjectures.SavchenkoSix.Encoding
public import conjectures.SavchenkoSix.Minors
public import conjectures.SavchenkoSix.Moments
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace SavchenkoSix
open Finset Matrix

private def endpoints : Fin 15→Fin 7×Fin 7 :=
  ![(1,2),(1,3),(2,3),(1,4),(2,4),(3,4),(1,5),(2,5),(3,5),(4,5),
    (1,6),(2,6),(3,6),(4,6),(5,6)]

private theorem lookup : ∀ i j : Fin 7, 0 < i → i < j → endpoints (edgeIndex i j)=(i,j) := by
  decide +kernel

theorem recover_bits (M : Matrix (Fin 7) (Fin 7) ℤ)
    (anti : ∀ i j,M j i= -M i j) (unit : ∀ i j,i≠j → M i j=1 ∨ M i j= -1)
    (root : ∀ j : Fin 7,0 < j → M 0 j=1) : ∃ b : Fin 15→Bool, bitsMatrix b=M := by
  let b (k : Fin 15) := decide (M (endpoints k).1 (endpoints k).2 = -1)
  refine ⟨b,?_⟩
  have upper {i j : Fin 7} (h : i < j) : bitsMatrix b i j=M i j := by
    by_cases zero : i=0
    · subst i
      rw [bitsMatrix_first b h,root j h]
    · have iz : 0 < i := by omega
      rw [bitsMatrix_upper b iz h]
      have hb : b (edgeIndex i j) = decide (M i j = -1) := by
        simp only [b,lookup i j iz h]
      rw [hb]
      rcases unit i j h.ne with u|u <;> simp [u]
  ext i j
  rcases lt_trichotomy i j with h|rfl|h
  · exact upper h
  · have a := anti i i
    have b' := bitsMatrix_flip b i i
    omega
  · rw [bitsMatrix_flip b j i,anti j i,upper h]

/-- Switching signs at vertices preserves every principal determinant and can make the first row positive. -/
theorem normalize_seven {V : Type*} [Fintype V] [DecidableEq V]
    (T : Tournament V) (e : Fin 7 ↪ V) :
    ∃ b : Fin 15→Bool, ∀ k, excessOn (T.sign.submatrix e e) univ k=excessOn (bitsMatrix b) univ k := by
  let M := T.sign.submatrix e e
  have anti (i j : Fin 7) : M j i= -M i j := sign_flip T _ _
  have unit (i j : Fin 7) (ne : i≠j) : M i j=1 ∨ M i j= -1 := by
    change T.sign (e i) (e j)=1 ∨ T.sign (e i) (e j)= -1
    simp only [Tournament.sign,e.injective.ne ne,ite_false]
    split <;> simp
  let d (j : Fin 7) : ℤ := if j=0 then 1 else M 0 j
  have du (i : Fin 7) : d i=1 ∨ d i= -1 := by
    by_cases hi : i=0
    · simp [d,hi]
    · simpa [d,hi] using unit 0 i (Ne.symm hi)
  have sq (i : Fin 7) : d i*d i=1 := by rcases du i with h|h <;> rw [h] <;> decide
  have flip (i j : Fin 7) : switch d M j i= -switch d M i j := by
    simp only [switch,anti i j]; ring
  have su (i j : Fin 7) (h : i≠j) : switch d M i j=1 ∨ switch d M i j= -1 := by
    unfold switch
    rcases du i with di|di <;> rcases du j with dj|dj <;> rcases unit i j h with a|a <;> rw [di,dj,a] <;> decide
  have root (j : Fin 7) (h : 0 < j) : switch d M 0 j=1 := by
    simpa [switch,d,h.ne'] using sq j
  obtain ⟨b,h⟩ := recover_bits (switch d M) flip su root
  exact ⟨b,fun k ↦ h ▸ (excessOn_switch M d sq univ k).symm⟩

end SavchenkoSix
end
