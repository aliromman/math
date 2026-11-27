module

public import conjectures.MissingSumFringes.Endpoints

@[expose] public section
namespace MissingSumFringes
open Finset
open scoped Pointwise Classical

theorem prob_congr (s : Finset ℕ) {p q : Finset ℕ → Prop} (eq : ∀ A ⊆ s, p A ↔ q A) :
    prob s p=prob s q := avg_congr s fun A h ↦ by simp only [eq A h]

theorem prob_mono (s : Finset ℕ) {p q : Finset ℕ → Prop} (h : ∀ A ⊆ s, p A → q A) :
    prob s p≤prob s q := by
  apply avg_mono s
  intro A hA
  by_cases hit : p A <;> simp [hit,show p A → q A from h A hA]
  split <;> norm_num

theorem prob_nonneg (s : Finset ℕ) (p : Finset ℕ → Prop) : 0≤prob s p := by
  rw [prob_count]
  positivity

theorem restrict_prob {s t : Finset ℕ} (h : s⊆t) (p : Finset ℕ → Prop) :
    prob t (fun A ↦ p (A ∩ s)) = prob s p := avg_restrict h (fun A ↦ if p A then 1 else 0)

theorem pair_prob {s t u : Finset ℕ} (disj : Disjoint s t) (sub : s∪t⊆u)
    (p q : Finset ℕ → Prop) :
    prob u (fun A ↦ p (A ∩ s) ∧ q (A ∩ t)) = prob s p * prob t q := by
  have project (A : Finset ℕ) (v : Finset ℕ) (hv : v⊆s∪t) :
      (A∩(s∪t))∩v=A∩v := by rw [inter_assoc,inter_eq_right.mpr hv]
  calc
    _ = prob u (fun A ↦ p ((A∩(s∪t))∩s) ∧ q ((A∩(s∪t))∩t)) := by
      apply prob_congr
      intro A _
      rw [project A s subset_union_left,project A t subset_union_right]
    _ = prob (s∪t) (fun A ↦ p (A∩s) ∧ q (A∩t)) := restrict_prob sub (fun A ↦ p (A∩s) ∧ q (A∩t))
    _ = _ := by
      unfold prob
      rw [avg_union disj]
      rw [show avg s (fun A ↦ if p A then (1:ℝ) else 0) * avg t (fun B ↦ if q B then 1 else 0) =
        avg s (fun A ↦ avg t (fun B ↦ (if p A then 1 else 0) * (if q B then 1 else 0))) from
        expect_mul_expect ..]
      apply avg_congr
      intro A hA
      apply avg_congr
      intro B hB
      have bs := disjoint_iff_inter_eq_empty.mp (disj.symm.mono_left hB)
      have at' := disjoint_iff_inter_eq_empty.mp (disj.mono_left hA)
      simp only [union_inter_distrib_right,bs,at',inter_eq_left.mpr hA,inter_eq_left.mpr hB,
        union_empty,empty_union]
      by_cases hp : p A <;> by_cases hq : q B <;> simp [hp,hq]

theorem reflect_subset {n : ℕ} {A : Finset ℕ} (hA : A⊆range n) : reflect n A⊆range n := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
  have := mem_range.mp (hA hx)
  apply mem_range.mpr
  omega

theorem two_ends {n l r : ℕ} (space : l+r≤n) (p q : Finset ℕ → Prop) :
    prob (range n) (fun A ↦ p (A∩range l) ∧ q (reflect n A ∩ range r)) =
      prob (range l) p * prob (range r) q := by
  let S := reflect n (range r)
  have rn : range r ⊆ range n := range_mono (by omega)
  have sub : range l ∪ S ⊆ range n :=
    union_subset (range_mono (by omega)) (reflect_subset rn)
  have ds : Disjoint (range l) S := by
    apply disjoint_left.mpr
    intro y hl hr
    obtain ⟨x,hx,e⟩ := mem_image.mp hr
    simp only [mem_range] at hx hl
    omega
  have projection (A : Finset ℕ) (hA : A⊆range n) : reflect n (A∩S)=reflect n A ∩ range r := by
    ext x
    simp only [reflect,S,mem_image,mem_inter,mem_range]
    constructor
    · rintro ⟨y,⟨hy,z,hz,ez⟩,ey⟩
      refine ⟨⟨y,hy,ey⟩,?_⟩
      omega
    · rintro ⟨⟨y,hy,ey⟩,hx⟩
      have := mem_range.mp (hA hy)
      exact ⟨y,⟨hy,x,hx,by omega⟩,ey⟩
  calc
    _ = prob (range n) (fun A ↦ p (A∩range l) ∧ q (reflect n (A∩S))) := by
      apply prob_congr
      intro A hA
      rw [projection A hA]
    _ = prob (range l) p * prob S (fun B ↦ q (reflect n B)) := pair_prob ds sub p (fun B ↦ q (reflect n B))
    _ = _ := by
      congr 1
      unfold prob
      have inv (x : ℕ) (h : x∈range r) : n-1-(n-1-x)=x := by
        have := mem_range.mp h
        omega
      rw [show S=(range r).image (fun x ↦ n-1-x) from rfl,avg_image _ _ _ inv]
      apply avg_congr
      intro A hA
      change (if q (reflect n (reflect n A)) then 1 else 0) = _
      rw [reflect_twice (hA.trans rn)]

end MissingSumFringes
