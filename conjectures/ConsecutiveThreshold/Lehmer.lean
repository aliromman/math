module

public import conjectures.ConsecutiveThreshold.Statement
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Interval.Finset.Fin

@[expose] public section
namespace ConsecutiveThreshold
open Finset Equiv
open scoped Classical BigOperators

/-- The Lehmer digit counts the smaller entries to the right of a position. -/
def digit {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) : ℕ :=
  (univ.filter fun j : Fin n ↦ i<j ∧ σ j<σ i).card

def Code (n : ℕ) := (i : Fin n) → Fin (n-i.val)

instance (n : ℕ) : Fintype (Code n) := by unfold Code; infer_instance

theorem digit_lt {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) : digit σ i < n-i.val := by
  have inc : univ.filter (fun j : Fin n ↦ i<j ∧ σ j<σ i) ⊆ Ioi i :=
    fun j hj ↦ mem_Ioi.mpr (mem_filter.mp hj).2.1
  have bound := card_le_card inc
  rw [Fin.card_Ioi] at bound
  change (univ.filter fun j : Fin n ↦ i<j ∧ σ j<σ i).card < _
  have := i.isLt
  omega

def encode {n : ℕ} (σ : Perm (Fin n)) : Code n := fun i ↦ ⟨digit σ i,digit_lt σ i⟩

theorem digit_zero {n : ℕ} (σ : Perm (Fin (n+1))) : digit σ 0=(σ 0).val := by
  rw [← Fin.card_Iio (σ 0)]
  apply card_bij (fun j _ ↦ σ j)
  · intro j h
    exact mem_Iio.mpr (mem_filter.mp h).2.2
  · intro i _ j _ e
    exact σ.injective e
  · intro x hx
    have lt := mem_Iio.mp hx
    have neq : σ.symm x ≠ 0 := fun h ↦ lt.ne (by simp [←h])
    exact ⟨σ.symm x,mem_filter.mpr ⟨mem_univ _,Fin.pos_iff_ne_zero.mpr neq,by simpa using lt⟩,σ.apply_symm_apply x⟩

private theorem skip_strict {n : ℕ} (p : Fin (n+1)) : StrictMono p.succAbove := by
  intro i j h
  simp only [Fin.succAbove]
  split <;> split <;> simp_all only [Fin.lt_def,Fin.val_castSucc,Fin.val_succ] <;> omega

theorem digit_succ {n : ℕ} (p : Fin (n+2)) (σ : Perm (Fin (n+1))) (i : Fin (n+1)) :
    digit (Perm.decomposeFin'Symm p σ) i.succ=digit σ i := by
  symm
  apply card_bij (fun j _ ↦ j.succ)
  · intro j hj
    obtain ⟨a,b⟩ := (mem_filter.mp hj).2
    apply mem_filter.mpr
    exact ⟨mem_univ _,Fin.succ_lt_succ_iff.mpr a,by simpa only [Perm.decomposeFin'Symm_succ] using (skip_strict p b)⟩
  · intro i _ j _ e
    exact Fin.succ_injective _ e
  · intro j hj
    obtain ⟨a,b⟩ := (mem_filter.mp hj).2
    induction j using Fin.cases with
    | zero => exact (not_lt_of_ge (Fin.zero_le _) a).elim
    | succ z =>
      simp only [Perm.decomposeFin'Symm_succ] at b
      exact ⟨z,mem_filter.mpr ⟨mem_univ _,Fin.succ_lt_succ_iff.mp a,(skip_strict p).lt_iff_lt.mp b⟩,rfl⟩

theorem encode_injective (n : ℕ) : Function.Injective (@encode n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact fun _ _ _ ↦ Subsingleton.elim ..
  | one => exact fun _ _ _ ↦ Subsingleton.elim ..
  | more n _ ih =>
    intro σ τ h
    let E := @Perm.decomposeFin' n
    obtain ⟨⟨p,S⟩,rfl⟩ := E.symm.surjective σ
    obtain ⟨⟨q,T⟩,rfl⟩ := E.symm.surjective τ
    change encode (Perm.decomposeFin'Symm p S) = encode (Perm.decomposeFin'Symm q T) at h
    have digits (i : Fin (n+2)) := congrArg Fin.val (congrFun h i)
    change ∀ i,digit (Perm.decomposeFin'Symm p S) i=digit (Perm.decomposeFin'Symm q T) i at digits
    obtain rfl : p=q := Fin.ext (by simpa [digit_zero] using digits 0)
    have eq : S=T := ih (by
      funext i
      apply Fin.ext
      change digit S i=digit T i
      simpa only [digit_succ] using digits i.succ)
    rw [eq]

private theorem code_card (n : ℕ) : Fintype.card (Code n)=n.factorial := by
  change Fintype.card ((i : Fin n) → Fin (n-i.val))=_
  simp only [Fintype.card_pi,Fintype.card_fin]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ,Nat.factorial_succ]
    simp only [Fin.val_zero,Nat.sub_zero,Fin.val_succ,Nat.succ_sub_succ_eq_sub,ih]

/-- All bounded inversion codes represent exactly one permutation. -/
noncomputable def codeEquiv (n : ℕ) : Perm (Fin n) ≃ Code n :=
  Equiv.ofBijective encode ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨encode_injective n,by rw [Fintype.card_perm,Fintype.card_fin,code_card]⟩)

end ConsecutiveThreshold
