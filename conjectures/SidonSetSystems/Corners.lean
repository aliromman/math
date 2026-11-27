module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace SidonSetSystems
open Finset
open scoped Classical

/-- Alternate a function over all subsets of a finite index set. -/
noncomputable def alternate {ι : Type*} [Fintype ι] (f : Finset ι → ℚ) : ℚ :=
  ∑ s ∈ (univ : Finset ι).powerset, (-1:ℚ)^s.card*f s

theorem alternate_congr {ι : Type*} [Fintype ι] {f g : Finset ι → ℚ}
    (h : ∀ s, f s=g s) : alternate f=alternate g := by
  rw [show f=g from funext h]

theorem alternate_add {ι : Type*} [Fintype ι] (f g : Finset ι → ℚ) :
    alternate (fun s => f s+g s)=alternate f+alternate g := by
  simp only [alternate,mul_add,sum_add_distrib]

theorem alternate_sub {ι : Type*} [Fintype ι] (f g : Finset ι → ℚ) :
    alternate (fun s => f s-g s)=alternate f-alternate g := by
  simp only [alternate,mul_sub,sum_sub_distrib]

theorem alternate_swap {ι κ : Type*} [Fintype ι] [Fintype κ] (f : Finset ι → Finset κ → ℚ) :
    alternate (fun s => alternate (f s)) = alternate (fun t => alternate (fun s => f s t)) := by
  simp only [alternate,mul_sum,←mul_assoc]
  rw [sum_comm]
  congr 1
  funext t
  apply sum_congr rfl
  intro s _
  rw [mul_comm ((-1:ℚ)^s.card)]

/-- If one coordinate is irrelevant, the two terms that differ there cancel. -/
theorem alternate_ignore {ι : Type*} [Fintype ι] (i : ι) (f : Finset ι → ℚ)
    (h : ∀ s, i∉s → f (insert i s)=f s) : alternate f=0 := by
  classical
  unfold alternate
  rw [←insert_erase (mem_univ i), sum_powerset_insert (notMem_erase i univ)]
  apply add_eq_zero_iff_eq_neg.mpr
  rw [←sum_neg_distrib]
  apply sum_congr rfl
  intro s hs
  have hi : i∉s := fun hi => (notMem_erase i _) (mem_powerset.mp hs hi)
  rw [card_insert_of_notMem hi,h s hi,pow_succ]
  ring

theorem alternate_point {ι : Type*} [Fintype ι] (c : ℚ) :
    alternate (fun s : Finset ι => if s=∅ then c else 0)=c := by
  unfold alternate
  rw [Finset.sum_eq_single ∅] <;> simp_all

theorem alternate_weighted {ι κ : Type*} [Fintype ι] [Fintype κ] (w : κ→ℚ) (f : κ→Finset ι→ℚ) :
    alternate (fun s => ∑ j, w j*f j s)=∑ j, w j*alternate (f j) := by
  simp only [alternate,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro s _
  ring

/-- The largest reading of the finite family of coordinates. -/
noncomputable def high {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℚ) : ℚ :=
  univ.sup' univ_nonempty f

theorem le_high {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℚ) (i : ι) : f i ≤ high f :=
  Finset.le_sup' f (mem_univ i)

theorem high_le {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → ℚ} {c : ℚ}
    (h : ∀ i, f i≤c) : high f ≤ c := Finset.sup'_le _ _ fun i _ => h i

noncomputable def corner {ι : Type*} [Fintype ι] [Nonempty ι]
    (δ : ℚ) (x : ι → ℚ) (s : Finset ι) : ℚ :=
  high (fun i => x i + if i∈s then δ else 0)

/-- At the common tie, every nonempty set of perturbations raises the maximum. -/
theorem alternate_origin {ι : Type*} [Fintype ι] [Nonempty ι] {δ : ℚ} (hd : 0<δ) :
    alternate (corner δ (fun _ : ι => 0)) = -δ := by
  classical
  let i : ι := Classical.arbitrary ι
  have h (s : Finset ι) : corner δ (fun _ : ι => 0) s = δ-(if s=∅ then δ else 0) := by
    by_cases hs : s=∅
    · subst s
      simp only [corner,notMem_empty,ite_false,add_zero,ite_true,sub_self]
      exact le_antisymm (high_le fun _ => le_rfl) (le_high (fun _ : ι => 0) i)
    · obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      rw [ite_eq_right hs,sub_zero]
      apply le_antisymm (high_le fun a => by dsimp; split <;> linarith)
      simpa [hj] using le_high (fun a : ι => (0:ℚ)+if a∈s then δ else 0) j
  rw [alternate_congr h,alternate_sub,alternate_ignore i (fun _ => δ) (by simp)]
  rw [alternate_point,zero_sub]

/-- A coordinate below the maximum by the perturbation size cannot affect it. -/
theorem alternate_away {ι : Type*} [Fintype ι] [Nonempty ι] {δ : ℚ} (hd : 0≤δ)
    (x : ι → ℚ) {i j : ι} (gap : x i+δ≤x j) : alternate (corner δ x)=0 := by
  classical
  apply alternate_ignore i
  intro s hs
  let f (u : ι) := x u+if u∈s then δ else 0
  let g (u : ι) := x u+if u∈insert i s then δ else 0
  change high g=high f
  have grow (u : ι) : f u≤g u := by
    by_cases hu : u=i
    · subst u
      simp [f,g,hs,hd]
    · simp [f,g,hu]
  have hj : x j≤f j := by dsimp [f]; split <;> linarith
  apply le_antisymm (high_le fun u => ?_) (high_le fun u => (grow u).trans (le_high g u))
  by_cases hu : u=i
  · subst u
    simpa [g] using gap.trans (hj.trans (le_high f j))
  · simpa [f,g,hu] using le_high f u

end SidonSetSystems
