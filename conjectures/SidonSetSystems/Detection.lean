module

public import conjectures.SidonSetSystems.Probes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace SidonSetSystems
open Finset
open scoped Classical

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The support function of a simplex detects its full subspace of directions. -/
theorem detect_directions (A : Figure V) (B : Fin 3 → Figure V) (w : Fin 3 → ℚ)
    (free : A.Free) (equal : ∀ f : Probe V, A.support f=∑ j, w j*(B j).support f) :
    ∃ j, A.directions ≤ (B j).directions := by
  classical
  by_contra! missing
  obtain ⟨v,hv,away⟩ := avoid_three A.directions (fun i => (B i).directions) missing
  choose u hu hu0 using fun i => (B i).probe_of_outside (away i)
  let shift (t : Finset (Fin 3)) : Probe V := ∑ i ∈ t, u i
  have null (p : Probe V) : alternate (fun t => A.support (p+shift t))=0 := by
    rw [alternate_congr (fun t => equal (p+shift t)),alternate_weighted]
    apply sum_eq_zero
    intro j _
    suffices alternate (fun t => (B j).support (p+shift t))=0 by rw [this,mul_zero]
    apply alternate_ignore j
    intro t ht
    apply Figure.support_congr
    intro x hx
    simp only [shift,Probe.read_add,Probe.read_sum]
    congr 1
    calc
      _ = ∑ i ∈ t.cons j ht, (u i).read x := sum_congr (by ext k; simp) (by simp)
      _ = _ := by rw [sum_cons,hu0 j x hx,zero_add]

  let T := {t : Finset (Fin 3) // t.Nonempty}
  let _ : Nonempty T := ⟨⟨{0},singleton_nonempty 0⟩⟩
  have nonconstant (t : T) : ∃ i j : A.sites, (shift t.1).read i < (shift t.1).read j := by
    by_contra! no
    have flat (i j : A.sites) : (shift t.1).read i=(shift t.1).read j := le_antisymm (no j i) (no i j)
    have vanish := A.constant_on flat v hv
    have score : (shift t.1).1 v=∑ j∈t.1, (u j).1 v := by
      dsimp [shift]
      induction t.1 using Finset.induction_on with
      | empty => simp
      | insert j s hj ih => simp [hj,ih]
    have pos := Finset.sum_pos (fun j (_ : j∈t.1) => hu j) t.2
    linarith
  choose lo hi hlt using nonconstant
  let gap (t : T) := (shift t.1).read (hi t)-(shift t.1).read (lo t)
  let δ := (univ : Finset T).inf' univ_nonempty gap
  have hδ : 0<δ := (Finset.lt_inf'_iff _).mpr fun t _ => sub_pos.mpr (hlt t)
  choose test test_eq using fun s : Finset A.sites => free (fun x => if x∈s then δ else 0)
  let H (s : Finset A.sites) (t : Finset (Fin 3)) := A.support (test s+shift t)
  have mass (t : Finset (Fin 3)) :
      alternate (fun s => H s t)=if t=∅ then -δ else 0 := by
    have eq (s : Finset A.sites) : H s t=corner δ (fun x : A.sites => (shift t).read x) s := by
      apply congrArg high
      funext x
      simp only [Probe.read_add,test_eq]
      by_cases hx : x∈s <;> simp [hx,add_comm]
    rw [alternate_congr eq]
    by_cases ht : t=∅
    · subst t
      simpa [shift] using alternate_origin (ι:=A.sites) hδ
    · let t' : T := ⟨t,nonempty_iff_ne_empty.mpr ht⟩
      rw [ite_eq_right ht]
      apply alternate_away hδ.le _ (i:=lo t') (j:=hi t')
      have small : δ≤gap t' := Finset.inf'_le gap (mem_univ t')
      dsimp [gap,t'] at small ⊢
      linarith
  have lhs : alternate (fun s => alternate (H s)) = 0 := by
    rw [alternate_congr (fun s => null (test s))]
    simp [alternate]
  rw [alternate_swap,alternate_congr mass] at lhs
  have point := alternate_point (ι:=Fin 3) (-δ)
  have eq : -δ=0 := by
    rw [←point]
    convert lhs using 1
    apply alternate_congr
    intro t
    by_cases ht : t=∅ <;> simp [ht]
  linarith

end SidonSetSystems
