module

public import conjectures.MissingSumFringes.Window
public import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith

@[expose] public section
namespace MissingSumFringes
open Finset
open scoped Pointwise Classical

/-- Average over all subsets of the given set of sites. -/
noncomputable def avg (s : Finset ℕ) (f : Finset ℕ → ℝ) : ℝ := s.powerset.expect f

noncomputable def prob (s : Finset ℕ) (p : Finset ℕ → Prop) : ℝ :=
  avg s (fun A ↦ if p A then 1 else 0)

theorem prob_count (s : Finset ℕ) (p : Finset ℕ → Prop) :
    prob s p = ((s.powerset.filter p).card : ℝ) / 2^s.card := by
  simp [prob,avg,expect_eq_sum_div_card,sum_boole]

theorem avg_mono (s : Finset ℕ) {f g : Finset ℕ → ℝ} (h : ∀ A ⊆ s, f A ≤ g A) :
    avg s f ≤ avg s g := expect_le_expect fun A hA ↦ h A (mem_powerset.mp hA)

theorem avg_congr (s : Finset ℕ) {f g : Finset ℕ → ℝ} (h : ∀ A ⊆ s, f A = g A) :
    avg s f = avg s g := expect_congr rfl fun A hA ↦ h A (mem_powerset.mp hA)

@[simp] theorem avg_const (s : Finset ℕ) (x : ℝ) : avg s (fun _ ↦ x)=x :=
  expect_const ⟨∅, by simp⟩ x

theorem avg_union {s t : Finset ℕ} (disj : Disjoint s t) (f : Finset ℕ → ℝ) :
    avg (s ∪ t) f = avg s (fun A ↦ avg t (fun B ↦ f (A ∪ B))) := by
  unfold avg
  rw [←expect_product s.powerset t.powerset (fun p ↦ f (p.1 ∪ p.2))]
  refine expect_nbij' (fun A ↦ (A ∩ s,A ∩ t)) (fun p ↦ p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro A _
    simp
  · rintro ⟨A,B⟩ h
    simp only [mem_product,mem_powerset] at h ⊢
    exact union_subset_union h.1 h.2
  · intro A h
    rw [←inter_union_distrib_left,inter_eq_left.mpr (mem_powerset.mp h)]
  · rintro ⟨A,B⟩ h
    simp only [mem_product,mem_powerset] at h
    have bs : Disjoint B s := disj.symm.mono_left h.2
    have at' : Disjoint A t := disj.mono_left h.1
    simp [union_inter_distrib_right,disjoint_iff_inter_eq_empty.mp bs,
      disjoint_iff_inter_eq_empty.mp at',inter_eq_left.mpr h.1,inter_eq_left.mpr h.2]
  · intro A h
    rw [←inter_union_distrib_left,inter_eq_left.mpr (mem_powerset.mp h)]

theorem avg_restrict {s t : Finset ℕ} (h : s ⊆ t) (f : Finset ℕ → ℝ) :
    avg t (fun A ↦ f (A ∩ s)) = avg s f := by
  have e : s ∪ (t \ s) = t := union_sdiff_of_subset h
  calc
    _ = avg (s ∪ (t \ s)) (fun A ↦ f (A ∩ s)) := by rw [e]
    _ = _ := by
      rw [avg_union disjoint_sdiff_self_right]
      apply avg_congr
      intro A hA
      calc
        _ = avg (t \ s) (fun _ ↦ f A) := by
          apply avg_congr
          intro B hB
          have d : Disjoint B s := disjoint_sdiff_self_left.mono_left hB
          rw [union_inter_distrib_right,inter_eq_left.mpr hA,disjoint_iff_inter_eq_empty.mp d,union_empty]
        _ = _ := avg_const ..

theorem avg_image (s : Finset ℕ) (f g : ℕ → ℕ) (h : ∀ x ∈ s, g (f x)=x)
    (v : Finset ℕ → ℝ) : avg (s.image f) v = avg s (fun A ↦ v (A.image f)) := by
  symm
  refine expect_nbij' (image f) (image g) ?_ ?_ ?_ ?_ (by simp)
  · intro A hA
    exact mem_powerset.mpr (image_subset_image (mem_powerset.mp hA))
  · intro B hB
    apply mem_powerset.mpr
    intro y hy
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp (mem_powerset.mp hB hz)
    rwa [h x hx]
  · intro A hA
    rw [image_image]
    apply image_congr (g := id) (fun x hx ↦ h x (mem_powerset.mp hA hx)) |>.trans
    simp
  · intro B hB
    rw [image_image]
    calc
      _ = B.image id := by
        apply image_congr
        intro y hy
        obtain ⟨x,hx,rfl⟩ := mem_image.mp (mem_powerset.mp hB hy)
        simp [h x hx]
      _ = B := by simp

theorem missing_restrict (t : ℕ) (A : Finset ℕ) : missing t (A ∩ range t)=missing t A := by
  ext x
  simp only [missing,mem_sdiff,mem_range,mem_add,mem_inter]
  constructor
  · rintro ⟨hx,no⟩
    refine ⟨hx,?_⟩
    rintro ⟨a,ha,b,hb,e⟩
    exact no ⟨a,⟨ha,by omega⟩,b,⟨hb,by omega⟩,e⟩
  · rintro ⟨hx,no⟩
    exact ⟨hx,fun ⟨a,ha,b,hb,e⟩ ↦ no ⟨a,ha.1,b,hb.1,e⟩⟩

end MissingSumFringes
