module

public import conjectures.LeanderLinusson.Statement
public import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Ring

@[expose] public section
namespace LeanderLinusson
open Finset Function

variable {S T V : Type*} [Fintype S] [Fintype T] [Fintype V]

noncomputable def pinned (a : T ↪ S) (b : T → V) : Finset (S → V) := by
  classical exact univ.filter fun g ↦ ∀ t, g (a t) = b t

@[simp] theorem mem_pinned {a : T ↪ S} {b : T → V} {g : S → V} :
    g ∈ pinned a b ↔ ∀ t, g (a t) = b t := by classical simp [pinned]

theorem pinned_card (a : T ↪ S) (b : T → V) :
    (pinned a b).card = Fintype.card V ^ (Fintype.card S - Fintype.card T) := by
  classical
  let e : (pinned a b : Type _) ≃ (((Set.range a)ᶜ : Set S) → V) := {
    toFun := fun g s ↦ g.val s.val
    invFun := fun f ↦ ⟨fun s ↦ if hs : ∃ t, a t = s then b hs.choose else f ⟨s,hs⟩,
      mem_pinned.mpr fun t ↦ by
        have hex : ∃ j, a j = a t := ⟨t,rfl⟩
        rw [dite_eq_left hex]
        exact congrArg b (a.injective hex.choose_spec)⟩
    left_inv := fun g ↦ by
      apply Subtype.ext
      funext s
      dsimp only
      split
      next hs => exact (mem_pinned.mp g.property hs.choose).symm.trans (congrArg g.val hs.choose_spec)
      rfl
    right_inv := fun f ↦ by
      funext s
      exact dite_eq_right s.property }
  have h := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_compl_set, Fintype.card_range] at h
  exact h

noncomputable def collisions (b : T → V) : Finset (S → V) := by
  classical exact univ.filter fun g ↦ ¬Injective g ∧ ∀ t, ∃ s, g s = b t

@[simp] theorem mem_collisions {b : T → V} {g : S → V} :
    g ∈ collisions b ↔ ¬Injective g ∧ ∀ t, ∃ s, g s = b t := by classical simp [collisions]

private noncomputable def slice (a : T ↪ S) (b : T → V) (u v : S) : Finset (S → V) := by
  classical exact (pinned a b).filter fun g ↦ u ∉ Set.range a ∧ u ≠ v ∧ g u = g v

private theorem slice_card (a : T ↪ S) (b : T → V) (u v : S) :
    (slice a b u v).card ≤ Fintype.card V ^ (Fintype.card S - Fintype.card T - 1) := by
  classical
  by_cases hu : u ∈ Set.range a
  · simp [slice, hu]
  by_cases huv : u = v
  · simp [slice, huv]
  let a' : T ↪ ({u}ᶜ : Set S) := ⟨fun t ↦ ⟨a t, fun h ↦ hu ⟨t,h⟩⟩,
    fun _ _ h ↦ a.injective (congrArg Subtype.val h)⟩
  have h := Finset.card_le_card_of_injOn (s := slice a b u v) (t := pinned a' b)
    (fun g (s : ({u}ᶜ : Set S)) ↦ g s.val)
    (fun g hg ↦ mem_pinned.mpr (fun t ↦ mem_pinned.mp (mem_filter.mp hg).1 t)) (by
      intro f hf g hg he
      apply funext
      intro s
      by_cases hs : s = u
      · subst s
        exact (mem_filter.mp hf).2.2.2.trans ((congrFun he ⟨v,Ne.symm huv⟩).trans
          (mem_filter.mp hg).2.2.2.symm)
      exact congrFun he ⟨s,hs⟩)
  rw [pinned_card] at h
  have hc : Fintype.card ↥(({u} : Set S)ᶜ) = Fintype.card S - 1 := by rw [Fintype.card_compl_set]; simp
  rw [hc, Nat.sub_sub, Nat.add_comm 1, ← Nat.sub_sub] at h
  exact h

/-- A repeated label costs one free choice in addition to the specified distinct labels. -/
theorem collisions_card (b : T ↪ V) :
    (collisions (S := S) b).card ≤ Fintype.card (T ↪ S) * Fintype.card S ^ 2 *
      Fintype.card V ^ (Fintype.card S - Fintype.card T - 1) := by
  classical
  let U (a : T ↪ S) (u v : S) := slice a (fun t ↦ b t) u v
  have sub : collisions (S := S) b ⊆ univ.biUnion
      (fun a ↦ univ.biUnion (fun u ↦ univ.biUnion (fun v ↦ U a u v))) := by
    intro g hg
    obtain ⟨hn,hs⟩ := mem_collisions.mp hg
    choose a ha using hs
    let e : T ↪ S := ⟨a,fun i j h ↦ b.injective ((ha i).symm.trans ((congrArg g h).trans (ha j)))⟩
    have pin : g ∈ pinned e (fun t ↦ b t) := mem_pinned.mpr ha
    obtain ⟨u,v,huv,hne⟩ : ∃ u v, g u = g v ∧ u ≠ v := by
      by_contra! h
      exact hn fun {i j} hij ↦ h i j hij
    have addSlice {u v : S} (hnot : u ∉ Set.range e) (hd : u ≠ v) (eq : g u=g v) :
        g ∈ univ.biUnion (fun u ↦ univ.biUnion (fun v ↦ U e u v)) :=
      mem_biUnion.mpr ⟨u,mem_univ _,mem_biUnion.mpr ⟨v,mem_univ _,mem_filter.mpr ⟨pin,hnot,hd,eq⟩⟩⟩
    refine mem_biUnion.mpr ⟨e,mem_univ _,?_⟩
    by_cases hu : u ∈ Set.range e
    · apply addSlice (v := u) _ hne.symm huv.symm
      rintro ⟨j,rfl⟩
      obtain ⟨i,rfl⟩ := hu
      exact hne (congrArg e (b.injective ((ha i).symm.trans (huv.trans (ha j)))))
    exact addSlice hu hne huv
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ ∑ a : T ↪ S, ∑ u : S, ∑ v : S, (U a u v).card :=
      card_biUnion_le.trans (sum_le_sum fun a _ ↦ card_biUnion_le.trans
        (sum_le_sum fun u _ ↦ card_biUnion_le))
    _ ≤ ∑ _a : T ↪ S, ∑ _u : S, ∑ _v : S,
        Fintype.card V ^ (Fintype.card S-Fintype.card T-1) :=
      sum_le_sum fun a _ ↦ sum_le_sum fun u _ ↦ sum_le_sum fun v _ ↦ slice_card a _ u v
    _ = _ := by simp; ring

theorem collisions_empty (b : T ↪ V) (h : Fintype.card S ≤ Fintype.card T) :
    collisions (S := S) b = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro g hg
  obtain ⟨hn,hs⟩ := mem_collisions.mp hg
  choose a ha using hs
  have hi : Injective a := fun i j h ↦ b.injective ((ha i).symm.trans ((congrArg g h).trans (ha j)))
  have sur := ((Fintype.bijective_iff_injective_and_card a).mpr
    ⟨hi,le_antisymm (Fintype.card_le_of_injective a hi) h⟩).2
  apply hn
  intro s u he
  obtain ⟨i,rfl⟩ := sur s
  obtain ⟨j,rfl⟩ := sur u
  exact congrArg a (b.injective ((ha i).symm.trans (he.trans (ha j))))

theorem collisions_scaled (b : T ↪ V) :
    (collisions (S := S) b).card * Fintype.card V ≤ Fintype.card (T ↪ S) * Fintype.card S ^ 2 *
      Fintype.card V ^ (Fintype.card S - Fintype.card T) := by
  by_cases h : Fintype.card S ≤ Fintype.card T
  · simp [collisions_empty b h]
  have h' := Nat.mul_le_mul_right (Fintype.card V) (collisions_card (S := S) b)
  rwa [Nat.mul_assoc, ← pow_succ,
    show Fintype.card S - Fintype.card T - 1 + 1 = Fintype.card S - Fintype.card T by omega] at h'

end LeanderLinusson
