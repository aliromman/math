module

public import conjectures.ConsecutiveThreshold.EventSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace ConsecutiveThreshold
open Equiv Finset
open scoped BigOperators Classical

/-- Generating polynomial for all bounded inversion codes. -/
noncomputable def full (n : ℕ) (q : ℝ) : Series := ∏ i : Fin n, geom q (n-i.val)

private theorem full_as_event (n : ℕ) (q : ℝ) : full n q = eventSeries q (fun _ : Code n ↦ True) := by
  calc
    _ = ∑ e : Code n, mono q (∑ i,(e i).val) := (weight_all q (fun i : Fin n ↦ n-i.val)).symm
    _ = _ := by simp [eventSeries]

theorem full_coefficient (n : ℕ) (q : ℝ) (z : ℤ) : (full n q).coeff z =
    if 0≤z then q^z.toNat * ((codeLayer n z.toNat).card:ℝ) else 0 := by
  rw [full_as_event]
  by_cases hz : 0≤z
  · have eq : (z.toNat : ℤ) = z := by omega
    simp only [hz, ↓reduceIte]
    conv_lhs => rw [←eq,event_coeff]
    simp [mul_comm]
  · simp only [hz, ↓reduceIte, eventSeries]
    rw [coeff_sum]
    apply Finset.sum_eq_zero
    intro e _
    have ne : ((∑ i,(e i).val : ℕ) : ℤ) ≠ z := by omega
    simp only [mono, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ne, ↓reduceIte]

private theorem choose_step (n : ℕ) : (n+1).choose 2 = n+n.choose 2 := by
  rw [Nat.choose_succ_succ]
  simp

private theorem realize_sum (n m : ℕ) (hm : m ≤ n.choose 2) :
    ∃ e : Code n, (∑ i, (e i).val)=m := by
  induction n generalizing m with
  | zero =>
    have hz : m=0 := by simpa using hm
    exact ⟨fun i ↦ Fin.elim0 i, by simp [hz]⟩
  | succ n ih =>
    rw [choose_step] at hm
    let z := min n m
    have hsum : z+(m-z)=m := Nat.add_sub_of_le (min_le_right n m)
    have hrest : m-z ≤ n.choose 2 := by dsimp [z]; omega
    obtain ⟨e,he⟩ := ih (m-z) hrest
    let g : Code (n+1) := Fin.cases (motive := fun i : Fin (n+1) ↦ Fin (n+1-i.val))
      ⟨z, by change z<n+1; exact Nat.lt_succ_of_le (min_le_left ..)⟩
      (fun i ↦ ⟨(e i).val, by simpa only [Fin.val_succ,Nat.succ_sub_succ_eq_sub] using (e i).isLt⟩)
    refine ⟨g, ?_⟩
    rw [Fin.sum_univ_succ]
    change z + (∑ i, (e i).val)=m
    rw [he, hsum]

theorem layer_positive {n m : ℕ} (h : m ≤ n.choose 2) : 0 < (codeLayer n m).card := by
  obtain ⟨e,he⟩ := realize_sum n m h
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩

private def reflectCode {n : ℕ} (e : Code n) : Code n := fun i ↦ Fin.rev (e i)

private theorem reflect_twice {n : ℕ} (e : Code n) : reflectCode (reflectCode e)=e := by
  funext i
  exact Fin.rev_rev _

private theorem available (n : ℕ) : (∑ i : Fin n, (n-i.val-1))=n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ,choose_step]
    simp [ih]

private theorem reflect_total {n : ℕ} (e : Code n) :
    (∑ i, ((reflectCode e) i).val) + ∑ i,(e i).val = n.choose 2 := by
  rw [←Finset.sum_add_distrib,←available]
  apply Finset.sum_congr rfl
  intro i _
  change (Fin.rev (e i)).val + (e i).val = _
  rw [Fin.val_rev]
  have he := (e i).isLt
  omega

theorem layer_symmetric {n m : ℕ} (h : m ≤ n.choose 2) :
    (codeLayer n (n.choose 2-m)).card = (codeLayer n m).card := by
  apply Finset.card_bij (fun e _ ↦ reflectCode e)
  · intro e he
    have H := reflect_total e
    have H' := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  · intro e _ f _ he
    simpa only [reflect_twice] using congrArg reflectCode he
  · intro e he
    have H := reflect_total e
    have H' := (Finset.mem_filter.mp he).2
    exact ⟨reflectCode e,Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩,reflect_twice _⟩

private theorem codes_equicard {n m : ℕ} (P : Perm (Fin n) → Prop) :
    ((univ.filter fun σ : Perm (Fin n) ↦ inversions σ=m).filter P).card =
      ((codeLayer n m).filter fun e ↦ P ((codeEquiv n).symm e)).card := by
  classical
  let E := codeEquiv n
  apply Finset.card_bij (fun σ _ ↦ E σ)
  · intro σ h
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hm).2⟩,
      by simpa [E] using hp⟩
  · exact fun _ _ _ _ he ↦ E.injective he
  · intro e he
    obtain ⟨hm,hp⟩ := Finset.mem_filter.mp he
    have eq : (∑ i, (E (E.symm e) i).val) = m := by rw [E.apply_symm_apply]; exact (Finset.mem_filter.mp hm).2
    exact ⟨E.symm e,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩,hp⟩,E.apply_symm_apply e⟩

theorem occurrence_eq_avoiding {n m k : ℕ} (π : Perm (Fin k)) (h : m≤n.choose 2) :
    occurrence π n m = 1 - (((codeLayer n m).filter (fun e ↦ ¬contains π ((codeEquiv n).symm e))).card : ℝ) /
      (codeLayer n m).card := by
  classical
  let P (e : Code n) := contains π ((codeEquiv n).symm e)
  have all := codes_equicard (n := n) (m := m) (fun _ ↦ True)
  simp at all
  have some := codes_equicard (n := n) (m := m) (contains π)
  have total := Finset.card_filter_add_card_filter_not (s := codeLayer n m) P
  have hp : 0 < ((codeLayer n m).card:ℝ) := by exact_mod_cast layer_positive h
  have add : (((codeLayer n m).filter P).card:ℝ) + (((codeLayer n m).filter fun e ↦ ¬P e).card:ℝ)
    = ((codeLayer n m).card:ℝ) := by exact_mod_cast total
  unfold occurrence
  dsimp only
  rw [some,all]
  change (((codeLayer n m).filter P).card:ℝ) / (codeLayer n m).card = _
  field_simp [hp.ne']
  linarith

end ConsecutiveThreshold
