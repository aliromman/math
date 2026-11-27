module

public import conjectures.ErdosSuranyi708.Site
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section
namespace ErdosSuranyi708
open Finset

def requiredLabels (p q : ℕ) (V : Finset ℕ) := insert p (insert q V)

abbrev Assignment (C : ℕ → Finset ℕ) (U : Finset ℕ) :=
  (r : U) → ↥(C r.val)

/-- A term is specified by its two crossing primes, its earlier red primes,
and one valuation bucket for each of these labels. -/
abbrev SeedIndex (P : Finset ℕ) (C : ℕ → Finset ℕ) :=
  Σ p : P, Σ q : earlier P p.val, Σ V : (earlier P q.val).powerset,
    Assignment C (requiredLabels p.val q.val V.val)

namespace SeedIndex
variable {P : Finset ℕ} {C : ℕ → Finset ℕ}

abbrev top (i : SeedIndex P C) := i.1.val
abbrev second (i : SeedIndex P C) := i.2.1.val
abbrev red (i : SeedIndex P C) := i.2.2.1.val
abbrev required (i : SeedIndex P C) := requiredLabels i.top i.second i.red
abbrev tail (i : SeedIndex P C) := earlier P i.second \ i.red

def exponent (i : SeedIndex P C) (p : ℕ) : ℕ :=
  if h : p ∈ i.required then (i.2.2.2 ⟨p,h⟩).val else 0

theorem exponent_mem (i : SeedIndex P C) {p : ℕ} (hp : p ∈ i.required) : i.exponent p ∈ C p := by
  simp only [exponent,dite_eq_left hp]
  exact (i.2.2.2 ⟨p,hp⟩).property

theorem second_lt (i : SeedIndex P C) : i.second < i.top := (mem_filter.mp i.2.1.property).2
theorem red_sub (i : SeedIndex P C) : i.red ⊆ earlier P i.second := mem_powerset.mp i.2.2.1.property

theorem req_sub (i : SeedIndex P C) : i.required ⊆ P := by
  exact insert_subset i.1.property (insert_subset (mem_filter.mp i.2.1.property).1
    (i.red_sub.trans (filter_subset ..)))

theorem top_not_second_red (i : SeedIndex P C) : i.top ∉ insert i.second i.red := by
  intro h
  rcases mem_insert.mp h with h|h
  · exact i.second_lt.ne' h
  · exact ((mem_filter.mp (i.red_sub h)).2.trans i.second_lt).false

theorem second_not_red (i : SeedIndex P C) : i.second ∉ i.red := fun h ↦
  ((mem_filter.mp (i.red_sub h)).2).false

theorem required_card (i : SeedIndex P C) : i.required.card = i.red.card + 2 := by
  simp [required,requiredLabels,card_insert_of_notMem i.top_not_second_red,
    card_insert_of_notMem i.second_not_red, Nat.add_assoc]

theorem tail_disjoint (i : SeedIndex P C) : Disjoint i.required i.tail := by
  apply disjoint_left.mpr
  intro r hr ht
  obtain ⟨he,hn⟩ := mem_sdiff.mp ht
  have hl := (mem_filter.mp he).2
  have hs := i.second_lt
  rcases mem_insert.mp hr with h|h
  · omega
  rcases mem_insert.mp h with h|h
  · omega
  · exact hn h

end SeedIndex

private theorem earlier_active (P : Finset ℕ) (p a : ℕ) :
    earlier (activeLabels P a) p = (earlier P p).filter (· ∣ a) := by
  ext b
  simp [earlier,activeLabels,and_left_comm,and_comm]

private theorem powerset_filter (P : Finset ℕ) (a : ℕ) :
    (P.filter (· ∣ a)).powerset = P.powerset.filter (fun V ↦ ∀ r ∈ V, r ∣ a) := by
  ext V
  simp only [mem_powerset,mem_filter]
  constructor
  · intro h
    exact ⟨h.trans (filter_subset ..),fun r hr ↦ (mem_filter.mp (h hr)).2⟩
  · intro ⟨h,h'⟩ r hr
    exact mem_filter.mpr ⟨h hr,h' r hr⟩

/-- Sum over all site-independent terms. At a site at most one assignment
contributes for each crossing pair and set of earlier labels. -/
theorem project_seed_sum {P : Finset ℕ} {C : ℕ → Finset ℕ} {a : ℕ}
    (hC : ∀ p ∈ P, 1 ∈ C p) (hp : ∀ p ∈ P, p.Prime) (ha : 0 < a)
    (F : SeedIndex P C → ℝ) (f : ℕ → ℕ → Finset ℕ → ℝ)
    (hyes : ∀ i, (∀ r ∈ i.required, r ∣ a ∧ lastCut (C r) (a.factorization r) = i.exponent r) →
      F i = f i.top i.second i.red)
    (hno : ∀ i, ¬(∀ r ∈ i.required, r ∣ a ∧ lastCut (C r) (a.factorization r) = i.exponent r) → F i = 0) :
    (∑ i, F i) = ∑ p ∈ activeLabels P a, ∑ q ∈ earlier (activeLabels P a) p,
      ∑ V ∈ (earlier (activeLabels P a) q).powerset, f p q V := by
  classical
  let g (p q : ℕ) (V : Finset ℕ) := if ∀ r ∈ requiredLabels p q V, r ∣ a then f p q V else 0
  have group (p : P) (q : earlier P p.val) (V : (earlier P q.val).powerset) :
      (∑ j : Assignment C (requiredLabels p.val q.val V.val), F ⟨p,q,V,j⟩) = g p q V := by
    let U := requiredLabels p.val q.val V.val
    by_cases hd : ∀ r ∈ requiredLabels p.val q.val V.val, r ∣ a
    · have sub : U ⊆ P := insert_subset p.property (insert_subset (mem_filter.mp q.property).1
        ((mem_powerset.mp V.property).trans (filter_subset ..)))
      let J : Assignment C U := fun r ↦ ⟨lastCut (C r) (a.factorization r), lastCut_mem
        (hC r (sub r.property)) ((hp r (sub r.property)).factorization_pos_of_dvd ha.ne' (hd r r.property))⟩
      suffices (∑ j : Assignment C U, F ⟨p,q,V,j⟩) = f p q V by simpa only [g,ite_eq_left hd] using this
      rw [sum_eq_single J]
      · apply hyes
        intro r hr
        exact ⟨hd r hr,by simp [SeedIndex.exponent, hr, J]⟩
      · intro b _ hb
        apply hno
        intro hmatch
        apply hb
        funext r
        apply Subtype.ext
        have hrr : r.val ∈ SeedIndex.required (P := P) (C := C) ⟨p,q,V,b⟩ := r.property
        have he := (hmatch r.val hrr).2
        simpa [SeedIndex.exponent, hrr, J] using he.symm
      · simp
    · simp only [g,ite_eq_right hd]
      apply sum_eq_zero
      intro j _
      exact hno _ fun hh ↦ hd fun r hr ↦ (hh r hr).1
  simp only [Fintype.sum_sigma,group]
  rw [sum_coe_sort P (fun p : ℕ ↦ ∑ q : earlier P p, ∑ V : (earlier P q.val).powerset, g p q V)]
  have curr (p : ℕ) : (∑ q : earlier P p, ∑ V : (earlier P q.val).powerset, g p q V) =
      ∑ q ∈ earlier P p, ∑ V ∈ (earlier P q).powerset, g p q V := by
    rw [← sum_coe_sort (earlier P p) (fun q : ℕ ↦ ∑ V ∈ (earlier P q).powerset, g p q V)]
    exact sum_congr rfl fun q _ ↦ sum_coe_sort _ (g p q.val)
  simp only [curr]
  rw [activeLabels,sum_filter]
  apply sum_congr rfl
  intro p hp'
  by_cases hp0 : p ∣ a
  · rw [ite_eq_left hp0, ← activeLabels, earlier_active, sum_filter]
    apply sum_congr rfl
    intro q hq
    by_cases hq0 : q ∣ a
    · rw [ite_eq_left hq0,earlier_active,powerset_filter,sum_filter]
      apply sum_congr rfl
      intro V _
      simp only [g,requiredLabels,forall_mem_insert,hp0,hq0,true_and]
    · rw [ite_eq_right hq0]
      exact sum_eq_zero fun V _ ↦ by simp [g,requiredLabels,hq0]
  · rw [ite_eq_right hp0]
    exact sum_eq_zero fun q _ ↦ sum_eq_zero fun V _ ↦ by simp [g,requiredLabels,hp0]

end ErdosSuranyi708
