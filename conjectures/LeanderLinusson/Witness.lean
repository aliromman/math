module

public import conjectures.LeanderLinusson.Statement
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace LeanderLinusson
open Finset

/-- Forget the order of the directed edges. -/
def edges {V : Type*} [DecidableEq V] {m : ℕ} (g : Sample V m) : Finset (V × V) :=
  univ.image fun i ↦ (g (i,false),g (i,true))

private theorem edge_injective {V : Type*} {m : ℕ} {g : Sample V m} (hg : Valid g) :
    Function.Injective (fun i ↦ (g (i,false),g (i,true))) := by
  intro i j eq
  by_contra h
  exact (hg.2 i j h).1 eq

/-- Every graph in the model has exactly the same number of edge orderings. -/
theorem ordering_count {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}
    (g : Sample V m) (hg : Valid g) :
    ((samples V m).filter (fun h ↦ edges h = edges g)).card = m.factorial := by
  classical
  let ordered (π : Equiv.Perm (Fin m)) : Sample V m := fun s ↦ g (π s.1,s.2)
  have hv (π : Equiv.Perm (Fin m)) : Valid (ordered π) :=
    ⟨fun i ↦ hg.1 _,fun i j ne ↦ hg.2 _ _ (fun e ↦ ne (π.injective e))⟩
  have he (π : Equiv.Perm (Fin m)) : edges (ordered π) = edges g := by
    ext y
    simp only [edges,mem_image,mem_univ,true_and]
    exact ⟨fun ⟨i,h⟩ ↦ ⟨π i,h⟩,fun ⟨i,h⟩ ↦ ⟨π.symm i,by simpa [ordered] using h⟩⟩
  have count := Finset.card_bij (s := univ) (t := (samples V m).filter (fun h ↦ edges h=edges g))
    (fun π _ ↦ ordered π)
    (fun π _ ↦ mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hv π⟩,he π⟩) (by
      intro π _ σ _ eq
      apply Equiv.ext
      intro i
      exact edge_injective hg (Prod.ext (congrFun eq (i,false)) (congrFun eq (i,true)))) (by
      intro h hh
      have hvalid : Valid h := (mem_filter.mp (mem_filter.mp hh).1).2
      have e := (mem_filter.mp hh).2
      have pick (i : Fin m) : ∃ j, (g (j,false),g (j,true)) = (h (i,false),h (i,true)) := by
        have z : (h (i,false),h (i,true)) ∈ edges g := e ▸ mem_image_of_mem _ (mem_univ i)
        simpa [edges] using z
      choose f hf using pick
      have hfi : Function.Injective f := fun i j e ↦ edge_injective hvalid
        ((hf i).symm.trans ((congrArg (fun k ↦ (g (k,false),g (k,true))) e).trans (hf j)))
      let π := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,rfl⟩)
      refine ⟨π,mem_univ _,?_⟩
      funext i
      rcases i with ⟨i,b⟩
      cases b
      · exact congrArg Prod.fst (hf i)
      · exact congrArg Prod.snd (hf i))
  simpa [Fintype.card_perm] using count.symm

private theorem joint_card {α : Type*} (S : Finset α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (S.filter (fun x ↦ ¬P x ∧ ¬Q x)).card + (S.filter P).card + (S.filter Q).card =
      S.card + (S.filter (fun x ↦ P x ∧ Q x)).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    by_cases hp : P x <;> by_cases hq : Q x <;> simp [filter_insert,hx,hp,hq] at * <;> omega

theorem failureCovariance_eq {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (s a t b : V) : failureCovariance V m s a t b = covariance V m s a t b := by
  let S := samples V m
  let P (g : Sample V m) := PathEvent g s a
  let Q (g : Sample V m) := PathEvent g t b
  let N : ℝ := S.card
  have comp (R : Sample V m → Prop) [DecidablePred R] :
      ((S.filter (fun x ↦ ¬R x)).card : ℝ) = N - (S.filter R).card := by
    have h : ((S.filter R).card : ℝ) + (S.filter (fun x ↦ ¬R x)).card = N := by
      dsimp [N]; exact_mod_cast S.card_filter_add_card_filter_not R
    linarith
  have joint : ((S.filter (fun x ↦ ¬P x ∧ ¬Q x)).card : ℝ) =
      N - (S.filter P).card - (S.filter Q).card + (S.filter (fun x ↦ P x ∧ Q x)).card := by
    have h : ((S.filter (fun x ↦ ¬P x ∧ ¬Q x)).card : ℝ) + (S.filter P).card +
      (S.filter Q).card = N + (S.filter (fun x ↦ P x ∧ Q x)).card := by dsimp [N]; exact_mod_cast joint_card S P Q
    linarith
  change _ / N - _ / N * (_ / N) = _ / N - _ / N * (_ / N)
  rw [comp P,comp Q,joint]
  by_cases hn : N=0
  · simp [hn]
  field_simp [hn]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem four_counts :
    (samples (Fin 4) 3).card = 960 ∧
    ((samples (Fin 4) 3).filter (fun g ↦ PathEvent g 0 1)).card = 336 ∧
    ((samples (Fin 4) 3).filter (fun g ↦ PathEvent g 2 3)).card = 336 ∧
    ((samples (Fin 4) 3).filter (fun g ↦ PathEvent g 0 1 ∧ PathEvent g 2 3)).card = 96 := by
  decide +kernel

theorem half_density : covariance (Fin 4) 3 0 1 2 3 = -(9/400) := by
  rcases four_counts with ⟨h,h₁,h₂,h₁₂⟩
  norm_num [covariance, probability, h, h₁, h₂, h₁₂]

theorem resolution : ¬Conjecture := by
  intro h
  have hp := h 4 (by decide) 3 (by decide) 0 1 2 3 (by decide)
  rw [failureCovariance_eq,half_density] at hp
  norm_num at hp

end LeanderLinusson
