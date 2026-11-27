module

public import conjectures.ChipShadow.Statement
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

@[expose] public section
noncomputable section
namespace ChipShadow
open Finset

theorem mem_blocks {n : ℕ} {w : State n} {B : Block n} : B∈blocks w ↔ IsBlock w B := by
  classical simp [blocks]

theorem suite_in {n : ℕ} {w : State n} {B : Block n} (h : IsBlock w B)
    {i : Fin (n+1)} (hi : B.1≤i ∧ i≤B.2) :
    w i+i.val=w B.2+B.2.val := by
  exact ((h.2 i).2 hi).trans (((h.2 B.2).2 ⟨h.1.le,le_rfl⟩).symm)

structure Good {n : ℕ} (w : State n) : Prop where
  sorted : Monotone (suite w)
  width : ∀ i j, i≤j → w j≤w i+1
  bounded : ∀ i,w i≤n
  marked : w=initial n ∨ ∃ i j, i<j ∧ w i<w j

theorem initial_good (n : ℕ) : Good (initial n) where
  sorted := by intro i j _;change n-i.val+i.val≤n-j.val+j.val;have := i.isLt;have := j.isLt;omega
  width := by intro i j h;change n-j.val≤n-i.val+1;change i.val≤j.val at h;omega
  bounded := by intro i;exact Nat.sub_le ..
  marked := Or.inl rfl

private theorem pushed_in {n : ℕ} {w : State n} {B : Block n} (h : IsBlock w B)
    {r : ℕ} (hr : r<span B) {j : Fin (n+1)} (hj : B.1≤j ∧ j≤B.2) :
    w B.2≤push w B r j ∧ push w B r j≤w B.1 := by
  have a := suite_in h hj
  have b := suite_in h (show B.1≤B.1 ∧ B.1≤B.2 from ⟨le_rfl,h.1.le⟩)
  change r<B.2.val-B.1.val at hr
  have l : B.1.val≤j.val := hj.1
  have u : j.val≤B.2.val := hj.2
  simp only [push,ite_eq_left hj]
  split <;> omega

theorem pushed_good {n : ℕ} {w : State n} (g : Good w) {B : Block n}
    (h : IsBlock w B) {r : ℕ} (hr : r<span B) : Good (push w B r) := by
  let inside (i : Fin (n+1)) := B.1≤i ∧ i≤B.2
  have lo (i : Fin (n+1)) : w i≤push w B r i+1 ∧ push w B r i≤w i+1 := by
    simp only [push]
    split_ifs <;> omega
  have outside {i : Fin (n+1)} (q : ¬inside i) : push w B r i=w i := ite_eq_right q
  have lrange : r<B.2.val-B.1.val := hr
  have leftval := suite_in h (show inside B.1 from ⟨le_rfl,h.1.le⟩)
  have ilt : B.1.val<B.2.val := h.1
  refine ⟨?_,?_,?_,?_⟩
  · intro i j ij
    by_cases I : inside i <;> by_cases J : inside j
    · have ai := suite_in h I
      have aj := suite_in h J
      have ij' : i.val≤j.val := ij
      change push w B r i+i.val≤push w B r j+j.val
      simp only [push]
      split_ifs <;> omega
    · have neq : suite w j≠suite w B.1 := fun e ↦ J ((h.2 j).mp e)
      have lt := lt_of_le_of_ne (g.sorted (I.1.trans ij)) (Ne.symm neq)
      have e := (h.2 i).mpr I
      simp only [suite] at e lt ⊢
      rw [outside J]
      exact (by have t := lo i; omega)
    · have neq : suite w i≠suite w B.1 := fun e ↦ I ((h.2 i).mp e)
      have before : i<B.1 := lt_of_not_ge (fun q ↦ I ⟨q,ij.trans J.2⟩)
      have lt := lt_of_le_of_ne (g.sorted before.le) neq
      have e := (h.2 j).mpr J
      simp only [suite] at e lt ⊢
      rw [outside I]
      exact (by have t := lo j; omega)
    · simpa only [suite,outside I,outside J] using g.sorted ij
  · intro i j ij
    by_cases I : inside i <;> by_cases J : inside j
    · rcases eq_or_lt_of_le ij with rfl|lt
      · omega
      have ai := suite_in h I
      have aj := suite_in h J
      have lt' : i.val<j.val := lt
      have t := lo i;have t' := lo j
      omega
    · have after : B.2≤j := le_of_not_ge (fun q ↦ J ⟨I.1.trans ij,q⟩)
      have hw := g.width B.2 j after
      have v := (pushed_in h hr I).1
      rw [outside J]
      exact hw.trans (Nat.add_le_add_right v 1)
    · have before : i≤B.1 := le_of_not_ge (fun q ↦ I ⟨q,ij.trans J.2⟩)
      have hw := g.width i B.1 before
      have v := (pushed_in h hr J).2
      rw [outside I]
      exact v.trans hw
    · rw [outside I,outside J]
      exact g.width i j ij
  · intro i
    by_cases I : inside i
    · exact (pushed_in h hr I).2.trans (g.bounded _)
    · rw [outside I]
      exact g.bounded i
  · right
    let j : Fin (n+1) := ⟨B.2.val-r,by have := B.2.isLt;omega⟩
    let i : Fin (n+1) := ⟨j.val-1,by have := j.isLt;omega⟩
    have jv : j.val=B.2.val-r := rfl
    have iv : i.val=j.val-1 := rfl
    have I : inside i := by change B.1.val≤i.val ∧ i.val≤B.2.val;omega
    have J : inside j := by change B.1.val≤j.val ∧ j.val≤B.2.val;omega
    have ai := suite_in h I;have aj := suite_in h J
    refine ⟨i,j,show i.val<j.val by omega,?_⟩
    simp only [push]
    split_ifs <;> omega

theorem has_block {n : ℕ} {w : State n} (g : Monotone (suite w)) (i : Fin n)
    (tie : suite w i.castSucc=suite w i.succ) : ∃ B∈blocks w,B.1≤i.castSucc ∧ i.succ≤B.2 := by
  classical
  let S := univ.filter fun j ↦ suite w j=suite w i.castSucc
  have mem (j : Fin (n+1)) : j∈S ↔ suite w j=suite w i.castSucc := by simp [S]
  have a := (mem _).mpr rfl
  have b := (mem _).mpr tie.symm
  let ne : S.Nonempty := ⟨_,a⟩
  let l := S.min' ne
  let u := S.max' ne
  have li : l≤i.castSucc := S.min'_le _ a
  have iu : i.succ≤u := S.le_max' _ b
  have ll := (mem _).mp (S.min'_mem ne)
  have uu := (mem _).mp (S.max'_mem ne)
  refine ⟨(l,u),mem_blocks.mpr ⟨lt_of_le_of_lt li (i.castSucc_lt_succ.trans_le iu),?_⟩,li,iu⟩
  intro j
  change suite w j=suite w l ↔ l≤j ∧ j≤u
  constructor
  · intro eq
    have member := (mem _).mpr (eq.trans ll)
    exact ⟨S.min'_le _ member,S.le_max' _ member⟩
  · rintro ⟨a,b⟩
    exact le_antisymm ((g b).trans_eq (uu.trans ll.symm)) (g a)

end ChipShadow
end
