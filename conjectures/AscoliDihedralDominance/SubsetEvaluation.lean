module

public import conjectures.AscoliDihedralDominance.Events
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

@[expose] public section
open Finset
namespace AscoliDihedral

variable {X : Type*} [DecidableEq X]

def permitted (edge : X → X → Bool) (allow : X → Bool) (A : Finset X) : Prop :=
  (∀ x∈A, allow x = true) ∧ ∀ x∈A, ∀ y∈A, edge x y = false

instance (edge : X → X → Bool) (allow : X → Bool) (A : Finset X) :
    Decidable (permitted edge allow A) := by unfold permitted; infer_instance

/-- Add the contributions from subsets that exclude or include the next vertex. -/
def countIndependent (B : ℕ) (edge : X → X → Bool) : List X → (X → Bool) → ℕ
  | [],_ => 1
  | v::vs, allow =>
    countIndependent B edge vs allow + if allow v && !edge v v then
      B * countIndependent B edge vs (fun x => allow x && !edge v x && !edge x v) else 0

private theorem permitted_insert (edge : X → X → Bool) (allow : X → Bool) (v : X) (A : Finset X) :
    permitted edge allow (insert v A) ↔
      (allow v && !edge v v) ∧ permitted edge (fun x => allow x && !edge v x && !edge x v) A := by
  simp only [permitted,forall_mem_insert,Bool.and_eq_true,Bool.not_eq_true']
  constructor
  · rintro ⟨⟨hv,ha⟩,⟨⟨ev,eva⟩, ea⟩⟩
    exact ⟨⟨hv,ev⟩,⟨fun x hx => ⟨⟨ha x hx,eva x hx⟩,(ea x hx).1⟩,
      fun x hx => (ea x hx).2⟩⟩
  · rintro ⟨⟨hv,ev⟩,ha,ea⟩
    exact ⟨⟨hv,fun x hx => (ha x hx).1.1⟩,⟨⟨ev,fun x hx => (ha x hx).1.2⟩,
      fun x hx => ⟨(ha x hx).2,ea x hx⟩⟩⟩

theorem countIndependent_eq (B : ℕ) (edge : X → X → Bool) (xs : List X) (hxs : xs.Nodup)
    (allow : X → Bool) : countIndependent B edge xs allow =
      ∑ A ∈ xs.toFinset.powerset, if permitted edge allow A then B^A.card else 0 := by
  induction xs generalizing allow with
  | nil => simp [countIndependent,permitted]
  | cons v vs ih =>
    have hv : v ∉ vs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    rw [countIndependent,List.toFinset_cons,sum_powerset_insert hv,
      ih (List.nodup_cons.mp hxs).2 allow]
    congr 1
    split_ifs with h
    · rw [ih (List.nodup_cons.mp hxs).2,mul_sum]
      apply sum_congr rfl
      intro A hA
      have hv' : v ∉ A := fun e => hv (mem_powerset.mp hA e)
      rw [card_insert_of_notMem hv']
      simp only [permitted_insert,h,true_and,pow_succ,mul_ite,mul_zero]
      split <;> simp [mul_comm]
    · symm
      apply sum_eq_zero
      intro A _
      simp [permitted_insert,h]

end AscoliDihedral
