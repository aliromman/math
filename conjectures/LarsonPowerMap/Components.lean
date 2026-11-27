module

public import conjectures.LarsonPowerMap.Statement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section
open Finset Function
namespace LarsonPowerMap
noncomputable section
variable {α : Type*} (f : α → α)

private abbrev cl := (mapGraph f).connectedComponentMk

private theorem step (x : α) : cl f (f x) = cl f x := by
  by_cases h : x = f x
  · rw [←h]
  · exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show (mapGraph f).Adj x (f x) from ⟨h,Or.inl rfl⟩)).symm

private theorem iter_step (n : ℕ) (x : α) : cl f (f^[n] x) = cl f x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply',step,ih]

variable [Fintype α]

open Classical in
def moved : Finset α := univ.filter fun x => f x ≠ x

/-- Each pair of moved points costs at least one weak component. -/
theorem moved_bound : (moved f).card + 2 * componentCount f ≤ 2 * Fintype.card α := by
  classical
  let C := (mapGraph f).ConnectedComponent
  let _ : Fintype C := Fintype.ofFinite _
  let s (c : C) := univ.filter (fun x => cl f x = c)
  let t (c : C) := (moved f).filter (fun x => cl f x = c)
  have allc : Fintype.card α = ∑ c, (s c).card := by
    simpa [s] using (card_eq_sum_card_fiberwise (f:=cl f) (s:=univ) (t:=univ)
      (fun _ _ => mem_univ _))
  have allm : (moved f).card = ∑ c, (t c).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  have h (c : C) : (t c).card + 2 ≤ 2 * (s c).card := by
    have sub : t c ⊆ s c := by
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
    have le := card_le_card sub
    obtain ⟨x,hx⟩ : ∃ x, cl f x = c := by
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h x => exact ⟨x,rfl⟩
    have pos : 0 < (s c).card := card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,hx⟩⟩
    by_cases z : (t c).Nonempty
    · obtain ⟨y,hy⟩ := z
      have ne := (mem_filter.mp (mem_filter.mp hy).1).2
      have two : 1 < (s c).card := one_lt_card.mpr
        ⟨y,sub hy,f y,mem_filter.mpr ⟨mem_univ _,(step f y).trans (mem_filter.mp hy).2⟩,Ne.symm ne⟩
      omega
    · rw [not_nonempty_iff_eq_empty.mp z,card_empty]
      omega
  have total := sum_le_sum (s:=univ) (fun c _ => h c)
  simpa [sum_add_distrib,←mul_sum,←allm,←allc,componentCount,Nat.card_eq_fintype_card,
    C,Nat.mul_comm] using total

omit [Fintype α] in
/-- Vertices in a component eventually reach a common vertex. -/
private theorem meet {x y : α} (h : cl f x = cl f y) :
    ∃ m n : ℕ, f^[m] x=f^[n] y := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact h
  clear h
  induction p with
  | nil => exact ⟨0,0,rfl⟩
  | @cons u v w adj _ ih =>
    obtain ⟨i,j,e⟩ := ih
    rcases adj.2 with e'|e'
    · exact ⟨i+1,j,by rw [iterate_succ_apply,e',e]⟩
    · refine ⟨i,j+1,?_⟩
      calc
        f^[i] u = f^[i+1] v := by rw [iterate_succ_apply,e']
        _ = f^[j+1] w := by rw [iterate_succ_apply',iterate_succ_apply',e]

private theorem periodic_in_component (c : (mapGraph f).ConnectedComponent) :
    ∃ x ∈ periodicPts f, cl f x=c := by
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h x =>
    obtain ⟨m,n,eq,ne⟩ : ∃ m n, f^[m] x=f^[n] x ∧ m≠n := by
      simpa [Injective] using not_injective_infinite_finite (f^[·] x)
    wlog h : m<n generalizing m n
    · exact this n m eq.symm ne.symm (by omega)
    refine ⟨f^[m] x,mk_mem_periodicPts (n:=n-m) (by omega) ?_,iter_step f m x⟩
    change f^[n-m] (f^[m] x)=f^[m] x
    rw [←iterate_add_apply,Nat.sub_add_cancel h.le,eq]

omit [Fintype α] in
private theorem orbit_in_component {x y : α} (hx : x ∈ periodicPts f)
    (hy : y ∈ periodicPts f) (h : cl f x=cl f y) : ∃ n, f^[n] x=y := by
  obtain ⟨i,j,e⟩ := meet f h
  apply (mem_periodicOrbit_iff hx).mp
  rw [←periodicOrbit_apply_iterate_eq hx i,e,periodicOrbit_apply_iterate_eq hy j]
  exact self_mem_periodicOrbit hy

/-- Each component contributes one cycle. A point off the cycle has period zero
and contributes zero to the reciprocal-period sum. -/
theorem componentCount_eq_sum_inv_period :
    (componentCount f : ℚ) = ∑ x, (minimalPeriod f x : ℚ)⁻¹ := by
  classical
  let C := (mapGraph f).ConnectedComponent
  let _ : Fintype C := Fintype.ofFinite _
  let p := univ.filter (fun x => x ∈ periodicPts f)
  let s (c : C) := p.filter (fun x => cl f x = c)
  let w (x : α) : ℚ := (minimalPeriod f x : ℚ)⁻¹
  have fiber (c : C) : ∑ x ∈ s c, w x = 1 := by
    obtain ⟨x,hx,hc⟩ := periodic_in_component f c
    have pos := minimalPeriod_pos_of_mem_periodicPts hx
    have repr (y) : y ∈ s c ↔ ∃ i : Fin (minimalPeriod f x), f^[i.val] x=y := by
      constructor
      · intro h
        obtain ⟨hy,hyc⟩ := mem_filter.mp h
        obtain ⟨n,rfl⟩ := orbit_in_component f hx (mem_filter.mp hy).2 (hc.trans hyc.symm)
        exact ⟨⟨n%_,Nat.mod_lt _ pos⟩,iterate_mod_minimalPeriod_eq⟩
      · rintro ⟨i,rfl⟩
        obtain ⟨t,ht,per⟩ := hx
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,mk_mem_periodicPts ht
          (per.apply_iterate i.val)⟩,(iter_step f _ _).trans hc⟩
    have im : s c = univ.image (fun i : Fin (minimalPeriod f x) => f^[i.val] x) := by
      ext y; simp only [repr,mem_image,mem_univ,true_and]
    have inj : Injective (fun i : Fin (minimalPeriod f x) => f^[i.val] x) :=
      fun i j e => Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp e)
    rw [im,sum_image (fun i _ j _ e => inj e)]
    simp only [w,minimalPeriod_apply_iterate hx,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast pos.ne')
  have grouped : ∑ c, ∑ x ∈ s c, w x = ∑ x ∈ p, w x :=
    sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
  have full : ∑ x ∈ p, w x = ∑ x, w x := by
    apply sum_subset (subset_univ p)
    intro x _ h
    have np : x ∉ periodicPts f := fun hx => h (mem_filter.mpr ⟨mem_univ _,hx⟩)
    simp [w,minimalPeriod_eq_zero_of_notMem_periodicPts np]
  calc
    (componentCount f : ℚ) = ∑ _c : C, (1 : ℚ) := by
      simp [componentCount,C,Nat.card_eq_fintype_card]
    _ = _ := ((sum_congr rfl (fun c _ => (fiber c).symm)).trans grouped).trans full

end
end LarsonPowerMap
