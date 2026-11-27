module

public import Mathlib.GroupTheory.Perm.Centralizer

@[expose] public section

open Equiv Equiv.Perm Finset

namespace LarsonPowerMap

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A fixed point has cycle length one. -/
noncomputable def cycleLength (σ : Perm α) (x : α) : ℕ :=
  orderOf (σ.cycleOf x)

abbrev HasCycle (σ : Perm α) (k : ℕ) : Prop := ∃ x, cycleLength σ x = k

theorem cycleLength_dvd_orderOf (σ : Perm α) (x : α) : cycleLength σ x ∣ orderOf σ :=
  orderOf_cycleOf_dvd_orderOf σ x

theorem cycleLength_pos (σ : Perm α) (x : α) : 0 < cycleLength σ x := orderOf_pos _

theorem cycleLength_le_card (σ : Perm α) (x : α) : cycleLength σ x ≤ Fintype.card α := by
  by_cases hx : σ x = x
  · rw [cycleLength, (cycleOf_eq_one_iff σ).mpr hx, orderOf_one]
    exact Fintype.card_pos_iff.mpr ⟨x⟩
  · rw [cycleLength, (isCycle_cycleOf σ hx).orderOf]
    exact card_le_univ _

theorem hasCycle_dvd_orderOf {σ : Perm α} {k : ℕ} (h : HasCycle σ k) : k ∣ orderOf σ := by
  obtain ⟨x,rfl⟩ := h
  exact cycleLength_dvd_orderOf σ x

theorem hasCycle_iff_mem_cycleType {σ : Perm α} {k : ℕ} (hk : 2 ≤ k) :
    HasCycle σ k ↔ k ∈ σ.cycleType := by
  rw [cycleType, Multiset.mem_map]
  constructor
  · rintro ⟨x,hx⟩
    have hn : σ x ≠ x := by
      intro h
      rw [cycleLength, (cycleOf_eq_one_iff σ).mpr h, orderOf_one] at hx
      omega
    exact ⟨σ.cycleOf x,cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hn),
      (isCycle_cycleOf σ hn).orderOf.symm.trans hx⟩
  · rintro ⟨c,hc,hs⟩
    have hcy := (mem_cycleFactorsFinset_iff.mp (show c ∈ σ.cycleFactorsFinset from hc)).1
    obtain ⟨x,hx⟩ := hcy.nonempty_support
    exact ⟨x,by rw [cycleLength, ← cycle_is_cycleOf hx hc, hcy.orderOf]; exact hs⟩

private noncomputable def pure (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Finset (Perm α) := univ.filter fun c => c.cycleType = {k}

private noncomputable def marked (k : ℕ) (x : α) : Finset (Perm α) :=
  (pure α k).filter fun c => x ∈ c.support

private def carriers (c : Perm α) : Finset (Perm α) :=
  univ.filter fun σ => c ∈ σ.cycleFactorsFinset

private theorem pure_facts {k : ℕ} {c : Perm α} (hc : c ∈ pure α k) :
    c.IsCycle ∧ c.support.card = k := by
  have h : c.cycleType = {k} := (mem_filter.mp hc).2
  exact ⟨card_cycleType_eq_one.mp (by simp [h]), by rw [← sum_cycleType, h]; simp⟩

private theorem disjoint_iff_outside (r c : Perm α) :
    r.Disjoint c ↔ r ∈ permsOfFinset c.supportᶜ := by
  rw [disjoint_iff_eq_or_eq, mem_perms_of_finset_iff]
  constructor
  · intro h x hx
    exact mem_compl.mpr (notMem_support.mpr ((h x).resolve_left hx))
  · intro h x
    by_cases hx : r x = x
    · exact Or.inl hx
    · exact Or.inr (notMem_support.mp (mem_compl.mp (h hx)))

private theorem card_carriers {c : Perm α} (hc : c.IsCycle) :
    (carriers c).card = (Fintype.card α - c.support.card).factorial := by
  have he : (permsOfFinset c.supportᶜ).card = (carriers c).card := by
    refine card_bij (fun r _ => r * c) ?_ (fun _ _ _ _ he => mul_right_cancel he) ?_
    · intro r hr
      have hd := (disjoint_iff_outside r c).mpr hr
      simp [carriers, hd.cycleFactorsFinset_mul_eq_union, hc.cycleFactorsFinset_eq_singleton]
    · intro σ hσ
      have hmem := (mem_filter.mp hσ).2
      exact ⟨σ * c⁻¹, (disjoint_iff_outside _ _).mp
        (disjoint_mul_inv_of_mem_cycleFactorsFinset hmem), by simp⟩
  rw [← he, card_perms_of_finset, card_compl]

private theorem marked_card_eq (x y : α) (k : ℕ) : (marked k x).card = (marked k y).card := by
  let p := Equiv.swap x y
  have hxy : p x = y := Equiv.swap_apply_left _ _
  have hconj (r c : Perm α) (a : α) (h : c ∈ marked k a) :
      r*c*r⁻¹ ∈ marked k (r a) := by
    obtain ⟨hC,hx⟩ := mem_filter.mp h
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩,?_⟩
    · rw [cycleType_conj]; exact (mem_filter.mp hC).2
    · rw [support_conj]; exact mem_map.mpr ⟨a,hx,rfl⟩
  refine card_bij (fun c _ => p*c*p⁻¹) ?_ ?_ ?_
  · intro c hc
    simpa [hxy] using hconj p c x hc
  · intro c _ d _ h
    exact mul_left_cancel (mul_right_cancel h)
  · intro c hc
    have hp : p⁻¹ y = x := by rw [← hxy]; simp
    exact ⟨p⁻¹*c*(p⁻¹)⁻¹,by simpa [hp] using hconj p⁻¹ c y hc,by simp [mul_assoc]⟩

private theorem marked_incidence (k : ℕ) (x : α) :
    Fintype.card α * (marked k x).card = (pure α k).card * k := by
  calc
    Fintype.card α * (marked k x).card = ∑ y : α, (marked k y).card := by
      simp_rw [marked_card_eq _ x k]
      simp
    _ = ∑ c ∈ pure α k, c.support.card := by
      simp only [marked, card_filter]
      rw [sum_comm]
      refine sum_congr rfl fun c _ => ?_
      simp [Equiv.Perm.support, card_filter]
    _ = (pure α k).card * k := by
      have eq : ∀ c ∈ pure α k, c.support.card = k := fun _ h => (pure_facts h).2
      simp [sum_congr rfl eq]

private theorem marked_union {k : ℕ} (hk : 2 ≤ k) (x : α) :
    (univ.filter fun σ : Perm α => cycleLength σ x = k) =
      (marked k x).biUnion carriers := by
  classical
  ext σ
  simp only [mem_filter, mem_univ, true_and, mem_biUnion, marked, carriers, pure]
  constructor
  · intro h
    have hx : σ x ≠ x := by
      intro he
      rw [cycleLength, (cycleOf_eq_one_iff σ).mpr he, orderOf_one] at h
      omega
    have hc := isCycle_cycleOf σ hx
    refine ⟨σ.cycleOf x,⟨?_,?_⟩,?_⟩
    · rw [hc.cycleType, ← hc.orderOf]; exact congrArg _ h
    · simpa [mem_support] using hx
    · exact cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)
  · rintro ⟨c,⟨h1,h2⟩,h3⟩
    obtain ⟨hc,hs⟩ := pure_facts (mem_filter.mpr ⟨mem_univ c,h1⟩ : c ∈ pure α k)
    rw [cycleLength, ← cycle_is_cycleOf h2 h3, hc.orderOf, hs]

private theorem fixed_factor (x : α) :
    (univ.filter fun σ : Perm α => cycleLength σ x = 1) = permsOfFinset ({x} : Finset α)ᶜ := by
  ext σ
  simp only [mem_filter, mem_univ, true_and, cycleLength, orderOf_eq_one_iff, cycleOf_eq_one_iff,
    mem_perms_of_finset_iff, mem_compl, mem_singleton]
  constructor
  · intro he y hy hxy
    subst y; exact hy he
  · intro h
    by_contra hn
    exact h hn rfl

private theorem pure_mass {k : ℕ} (hk : 2 ≤ k) (hn : k ≤ Fintype.card α) :
    (pure α k).card * (Fintype.card α - k).factorial * k = (Fintype.card α).factorial := by
  rw [show (pure α k).card = (k-1).factorial * (Fintype.card α).choose k from
    card_of_cycleType_singleton hk hn]
  have hk' : k ≠ 0 := by omega
  have hfac := Nat.mul_factorial_pred hk'
  calc
    _ = (Fintype.card α).choose k * (k * (k-1).factorial) * (Fintype.card α-k).factorial := by ac_rfl
    _ = _ := by rw [hfac, Nat.choose_mul_factorial_mul_factorial hn]

private theorem count_marked (x : α) {k : ℕ} (hk : 2 ≤ k) :
    (univ.filter fun σ : Perm α => cycleLength σ x = k).card =
      (marked k x).card * (Fintype.card α-k).factorial := by
  rw [marked_union hk x, card_biUnion]
  · have eq : ∀ c ∈ marked k x, (carriers c).card = (Fintype.card α-k).factorial := by
      intro c hc
      obtain ⟨hc',hs⟩ := pure_facts (mem_filter.mp hc).1
      rw [card_carriers hc',hs]
    simp [sum_congr rfl eq]
  · intro c hc d hd he
    apply Finset.disjoint_left.mpr
    intro σ h₁ h₂
    exact he ((cycle_is_cycleOf (mem_filter.mp hc).2 (mem_filter.mp h₁).2).trans
      (cycle_is_cycleOf (mem_filter.mp hd).2 (mem_filter.mp h₂).2).symm)

/-- Each possible cycle length of a named point occurs equally often. -/
theorem card_cycleLength (x : α) {k : ℕ} (hk : 0 < k) (hn : k ≤ Fintype.card α) :
    (univ.filter fun σ : Perm α => cycleLength σ x = k).card =
      (Fintype.card α - 1).factorial := by
  by_cases he : k = 1
  · subst k
    rw [fixed_factor, card_perms_of_finset, card_compl, card_singleton]
  have hk₂ : 2 ≤ k := by omega
  rw [count_marked x hk₂]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Fintype.card α by omega)
  rw [← Nat.mul_assoc, marked_incidence,
    Nat.mul_factorial_pred (show Fintype.card α ≠ 0 by omega)]
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using pure_mass hk₂ hn

private theorem has_union {k : ℕ} (hk : 2 ≤ k) :
    (univ.filter fun σ : Perm α => HasCycle σ k) = (pure α k).biUnion carriers := by
  classical
  ext σ
  simp only [mem_filter, mem_univ, true_and, mem_biUnion]
  constructor
  · rintro ⟨x,hx⟩
    have hm : σ ∈ (marked k x).biUnion carriers := by rw [← marked_union hk]; simp [hx]
    obtain ⟨c,hc,hσ⟩ := mem_biUnion.mp hm
    exact ⟨c,(mem_filter.mp hc).1,hσ⟩
  · rintro ⟨c,hc,hσ⟩
    obtain ⟨x,hx⟩ := (pure_facts hc).1.nonempty_support
    refine ⟨x, ?_⟩
    have hm : σ ∈ (marked k x).biUnion carriers :=
      mem_biUnion.mpr ⟨c,mem_filter.mpr ⟨hc,hx⟩,hσ⟩
    rw [← marked_union hk] at hm
    exact (mem_filter.mp hm).2

/-- A cycle longer than half the degree is unique. -/
theorem card_hasCycle_mul {k : ℕ} (hk : Fintype.card α / 2 < k) (hn : k ≤ Fintype.card α) :
    (univ.filter fun σ : Perm α => HasCycle σ k).card * k = (Fintype.card α).factorial := by
  classical
  by_cases he : k = 1
  · subst k
    have hn' : Fintype.card α = 1 := by omega
    obtain ⟨x,hx⟩ := Fintype.card_eq_one_iff.mp hn'
    have H : (univ.filter fun σ : Perm α => HasCycle σ 1) =
        (univ.filter fun σ : Perm α => cycleLength σ x = 1) := by
      ext σ
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun ⟨y,h⟩ => (hx y) ▸ h,fun h => ⟨x,h⟩⟩
    rw [H,card_cycleLength x (by decide) (by omega),hn']
    decide
  have hk₂ : 2 ≤ k := by omega
  rw [has_union hk₂, card_biUnion]
  · have eq : ∀ c ∈ pure α k, (carriers c).card = (Fintype.card α-k).factorial := by
      intro c hc
      obtain ⟨hc',hs⟩ := pure_facts hc
      rw [card_carriers hc',hs]
    simpa [sum_congr rfl eq] using pure_mass hk₂ hn
  · intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro σ h₁ h₂
    have dis := (σ.cycleFactorsFinset_pairwise_disjoint (mem_filter.mp h₁).2
      (mem_filter.mp h₂).2 hcd).disjoint_support
    have bounds := Finset.card_le_univ (c.support ∪ d.support)
    rw [Finset.card_union_of_disjoint dis, (pure_facts hc).2, (pure_facts hd).2] at bounds
    omega

/-- info: 'LarsonPowerMap.card_cycleLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_cycleLength

/-- info: 'LarsonPowerMap.card_hasCycle_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_hasCycle_mul

end LarsonPowerMap
