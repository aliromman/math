module

public import conjectures.KarlovskySumAttainment.Arithmetic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace KarlovskySumAttainment
open Finset
open scoped BigOperators

/-- The unique candidate when equality is possible. -/
def extremizer (k F y : ℕ) : Fin (k+2) → ℕ :=
  Fin.snoc (Fin.snoc (fun i : Fin k => i.val+1) y) (F*(tri k+y))

private theorem snoc_strict {k : ℕ} {f : Fin k → ℕ} (h : StrictMono f)
    {a : ℕ} (lt : ∀ i,f i<a) : StrictMono (Fin.snoc f a : Fin (k+1) → ℕ) := by
  intro i j edge
  induction i using Fin.lastCases with
  | last => exact (not_lt_of_ge (Fin.le_last _) edge).elim
  | cast p =>
    induction j using Fin.lastCases with
    | last => simpa only [Fin.snoc_castSucc,Fin.snoc_last] using lt p
    | cast q => simpa only [Fin.snoc_castSucc] using h (Fin.castSucc_lt_castSucc_iff.mp edge)

private theorem tri_pos {k : ℕ} (hk : 0<k) : 0<tri k := by
  apply Nat.pos_of_ne_zero
  intro zero
  have contradiction := tri_twice k
  rw [zero,Nat.mul_zero] at contradiction
  exact (Nat.mul_ne_zero hk.ne' (Nat.succ_ne_zero k)) contradiction.symm

theorem extremizer_attains {k F y : ℕ} (hk : 2≤k) (hF : 0<F) (hy : k<y)
    (fy : F+1=k.factorial*y) :
    Solution F (extremizer k F y) ∧ ((∑ i,extremizer k F y i) : ℕ)=upper k F := by
  let z := F*(tri k+y)
  have t := tri_pos (by omega : 0<k)
  have above : y<z := by
    have := Nat.mul_le_mul_right (tri k+y) (Nat.succ_le_of_lt hF)
    dsimp only [z]; omega
  let b (i : Fin k) := i.val+1
  have mono : StrictMono b := fun i j edge => Nat.succ_lt_succ edge
  have lo : ∀ i,b i<y := fun i => Nat.lt_of_le_of_lt (Nat.succ_le_of_lt i.isLt) hy
  have full : StrictMono (extremizer k F y) := by
    apply snoc_strict (snoc_strict mono lo)
    intro i
    induction i using Fin.lastCases with
    | last => simpa [z] using above
    | cast j => simpa only [Fin.snoc_castSucc] using (lo j).trans above
  have sums : (∑ i,extremizer k F y i) = tri k+y+z := by
    unfold extremizer
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    rw [Fin.sum_univ_castSucc]
    simp [tri,z]
  have prods : (∏ i,extremizer k F y i) = k.factorial*y*z := by
    unfold extremizer
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    rw [Fin.prod_univ_eq_prod_range (fun i => i+1),Finset.prod_range_add_one_eq_factorial]
  constructor
  · refine ⟨?_,full,?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa [extremizer,z] using (Nat.zero_lt_of_lt above)
      | cast j =>
        induction j using Fin.lastCases with
        | last => simpa [extremizer] using (Nat.zero_lt_of_lt hy)
        | cast l => simp [extremizer]
    · rw [prods,sums,←fy]
      dsimp only [z]
      ring
  · have pos : (0:ℚ)<k.factorial := by exact_mod_cast k.factorial_pos
    apply (mul_right_inj' pos.ne').mp
    rw [upper_nat,sums]
    have e : k.factorial*(tri k+y+z)=(F+1)*(F+1+k.factorial*tri k) := by
      dsimp [z]
      nlinarith only [congrArg (fun a : ℕ => (F+1)*a) fy]
    exact_mod_cast e

/-- Up to the increasing ordering of the inputs, the extremizer is unique. -/
theorem equality_iff {k F : ℕ} (hk : 2≤k) (hF : 0<F)
    {x : Fin (k+2) → ℕ} (sol : Solution F x) :
    ((∑ i,x i) : ℕ) = upper k F ↔
      ∃ y : ℕ, k<y ∧ F+1=k.factorial*y ∧ x=extremizer k F y := by
  constructor
  · intro eq
    have p : (k.factorial:ℚ)*((∑ i,x i):ℕ)=k.factorial*upper k F := by rw [eq]
    rw [upper_nat] at p
    have n : k.factorial*(∑ i,x i) = (F+1)*(F+1+k.factorial*tri k) := by exact_mod_cast p
    obtain ⟨fy,hi,hs,z⟩ := (core_bound hk hF sol).2 n
    let y:=x (Fin.last k).castSucc
    refine ⟨y,hi,fy,?_⟩
    have point (i : Fin k) : i.val+1=x i.castSucc.castSucc :=
      (sum_eq_sum_iff_of_le (fun j _ => rank_lower sol.1 sol.2.1
        (j : Fin k).castSucc.castSucc)).mp hs.symm i (mem_univ i)
    funext i
    induction i using Fin.lastCases with
    | last => simpa [extremizer,y] using z
    | cast j =>
      induction j using Fin.lastCases with
      | last => simp [extremizer,y]
      | cast l => simpa only [extremizer,Fin.snoc_castSucc] using (point l).symm
  · rintro ⟨y,hi,fy,rfl⟩
    exact (extremizer_attains hk hF hi fy).2

theorem resolution : Conjecture3 := by
  intro k F hk hF
  constructor
  · rintro ⟨x,sol,eq,_⟩
    obtain ⟨y,hi,fy,_⟩ := (equality_iff hk hF sol).mp eq
    exact ⟨y-k,by omega,by rw [Nat.add_sub_of_le hi.le,mul_comm]; exact fy⟩
  · rintro ⟨b,hb,fy⟩
    let y:=k+b
    obtain ⟨sol,eq⟩ := extremizer_attains hk hF (show k<y by dsimp [y]; omega)
      (by simpa [y,mul_comm] using fy)
    refine ⟨extremizer k F y,sol,eq,?_⟩
    intro w wh
    have bound := sum_le hk hF wh
    rw [←eq] at bound
    exact_mod_cast bound

/-- info: 'KarlovskySumAttainment.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'KarlovskySumAttainment.equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equality_iff

end KarlovskySumAttainment
