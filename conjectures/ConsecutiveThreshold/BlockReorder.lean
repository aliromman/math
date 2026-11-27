module

public import conjectures.ConsecutiveThreshold.BlockPositions
public import Mathlib.GroupTheory.Perm.ViaEmbedding

@[expose] public section
namespace ConsecutiveThreshold
open Equiv Finset
open scoped Classical BigOperators

variable {k n : ℕ}

def inBlock (r k : ℕ) (i : Fin n) : Prop := r ≤ i.val ∧ i.val < r+k

theorem pos_inBlock (r : ℕ) (room : r+k≤n) (i : Fin k) :
    inBlock r k (blockPos r room i) := by
  simp [inBlock,blockPos]

private theorem inBlock_pos (r : ℕ) (room : r+k≤n) {x : Fin n} (hx : inBlock r k x) :
    ∃ i : Fin k, blockPos r room i=x := by
  obtain ⟨lo,hi⟩ := hx
  exact ⟨⟨x.val-r,by omega⟩, Fin.ext (by change r+(x.val-r)=x.val; omega)⟩

noncomputable def blockReorder (r : ℕ) (room : r+k≤n) (ρ : Perm (Fin k)) : Perm (Fin n) :=
  Perm.viaEmbedding ρ ⟨blockPos r room, (blockPos_strict r room).injective⟩

@[simp] theorem reorder_pos (r : ℕ) (room : r+k≤n) (ρ : Perm (Fin k)) (i : Fin k) :
    blockReorder r room ρ (blockPos r room i) = blockPos r room (ρ i) := by
  exact Perm.viaEmbedding_apply _ _ i

theorem reorder_outside (r : ℕ) (room : r+k≤n) (ρ : Perm (Fin k)) (x : Fin n)
    (hx : ¬inBlock r k x) : blockReorder r room ρ x = x := by
  apply Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i,rfl⟩
  exact hx (pos_inBlock r room i)

private theorem outside_lt (r : ℕ) (room : r+k≤n) (ρ : Perm (Fin k)) (x y : Fin n)
    (hxy : x<y) (h : ¬(inBlock r k x ∧ inBlock r k y)) :
    blockReorder r room ρ x < blockReorder r room ρ y := by
  by_cases hx : inBlock r k x
  · have hy : ¬inBlock r k y := fun z ↦ h ⟨hx,z⟩
    obtain ⟨i,rfl⟩ := inBlock_pos r room hx
    rw [reorder_pos, reorder_outside r room ρ y hy]
    simp only [inBlock,blockPos,Fin.lt_def] at *
    have := (ρ i).isLt
    omega
  · rw [reorder_outside r room ρ x hx]
    by_cases hy : inBlock r k y
    · obtain ⟨j,rfl⟩ := inBlock_pos r room hy
      rw [reorder_pos]
      simp only [inBlock,blockPos,Fin.lt_def] at *
      have := j.isLt
      omega
    · simpa [reorder_outside r room ρ y hy] using hxy

theorem can_force_pattern (π : Perm (Fin k)) (σ : Perm (Fin n)) (r : ℕ) (room : r+k≤n) :
    ∃ ρ : Perm (Fin k), blockHit π r room (σ * blockReorder r room ρ) := by
  classical
  let f : Fin k ↪ Fin n := ⟨fun i ↦ σ (blockPos r room i), σ.injective.comp (blockPos_strict r room).injective⟩
  let S := Finset.univ.map f
  let lift (i : Fin k) : S := ⟨f i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have bij : Function.Bijective lift := by
    refine ⟨fun _ _ h ↦ f.injective (congrArg Subtype.val h), ?_⟩
    intro z
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp z.property
    exact ⟨i, Subtype.ext hi⟩
  let E := Equiv.ofBijective lift bij
  let sorted := S.orderIsoOfFin (k := k) (by simp [S])
  let ρ := (π.trans sorted.toEquiv).trans E.symm
  have he (i : Fin k) : σ (blockPos r room (ρ i)) = (sorted (π i) : Fin n) :=
    congrArg Subtype.val (E.apply_symm_apply (sorted (π i)))
  refine ⟨ρ, fun i j ↦ ?_⟩
  simp only [Perm.mul_apply, reorder_pos, he]
  exact sorted.lt_iff_lt.symm

private def invPairs (σ : Perm (Fin n)) : Finset (Fin n × Fin n) :=
  univ.filter fun p ↦ p.1<p.2 ∧ σ p.2<σ p.1

private theorem invPairs_card (σ : Perm (Fin n)) : (invPairs σ).card = inversions σ := by
  rw [invPairs,Finset.card_filter,Fintype.sum_prod_type]
  unfold inversions
  simp only [Finset.card_filter]

/-- Reordering a consecutive block to pattern π adds at most the inversions of π. -/
theorem force_cost (π : Perm (Fin k)) (σ : Perm (Fin n)) (r : ℕ) (room : r+k≤n)
    (ρ : Perm (Fin k)) (hit : blockHit π r room (σ * blockReorder r room ρ)) :
    inversions (σ * blockReorder r room ρ) ≤ inversions σ + inversions π := by
  classical
  let E := blockReorder r room ρ
  let S := invPairs (σ * E)
  let both (p : Fin n × Fin n) := inBlock r k p.1 ∧ inBlock r k p.2
  have outside : (S.filter fun p ↦ ¬both p).card ≤ (invPairs σ).card := by
    apply Finset.card_le_card_of_injOn (fun p : Fin n × Fin n ↦ (E p.1,E p.2))
    · intro p hp
      obtain ⟨hs,he⟩ := Finset.mem_filter.mp hp
      obtain ⟨hlt,hinv⟩ := (Finset.mem_filter.mp hs).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,outside_lt r room ρ _ _ hlt he,hinv⟩
    · intro x _ y _ he
      exact Prod.ext (E.injective (congrArg Prod.fst he)) (E.injective (congrArg Prod.snd he))
  have inside : (S.filter both).card ≤ (invPairs π).card := by
    let f (p : Fin k × Fin k) := (blockPos r room p.1,blockPos r room p.2)
    apply le_trans (Finset.card_le_card (t := (invPairs π).image f) ?_) Finset.card_image_le
    rintro ⟨x,y⟩ hxy
    obtain ⟨hs,hboth⟩ := Finset.mem_filter.mp hxy
    obtain ⟨i,rfl⟩ := inBlock_pos r room hboth.1
    obtain ⟨j,rfl⟩ := inBlock_pos r room hboth.2
    obtain ⟨hij,hji⟩ := (Finset.mem_filter.mp hs).2
    exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (blockPos_strict r room).lt_iff_lt.mp hij,(hit j i).mpr hji⟩,rfl⟩
  have tot := Finset.card_filter_add_card_filter_not (s := S) both
  change _ ≤ _ + _
  rw [← invPairs_card,← invPairs_card,← invPairs_card]
  change S.card ≤ _ + _
  omega

end ConsecutiveThreshold
