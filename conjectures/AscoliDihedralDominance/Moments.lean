module

public import conjectures.AscoliDihedralDominance.Events
public import conjectures.AscoliDihedralDominance.Counting

@[expose] public section
open Finset
namespace AscoliDihedral

variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- Count memberships in a family of finite sets. -/
theorem incidence_sum (T : Finset Y) (R : Y → Finset X) :
    (∑ x, (T.filter fun y => x ∈ R y).card) = ∑ y ∈ T, (R y).card := by
  simp only [card_filter]
  rw [sum_comm]
  simp

/-- The square counts ordered pairs of memberships in the same object. -/
theorem incidence_square_sum (T : Finset Y) (R : Y → Finset X) :
    (∑ x, (T.filter fun y => x ∈ R y).card^2) =
      ∑ y ∈ T, ∑ z ∈ T, (R y ∩ R z).card := by
  have h (x : X) :
      (T.filter fun y => x ∈ R y).card^2 =
      ∑ y ∈ T, ∑ z ∈ T, if x ∈ R y ∩ R z then 1 else 0 := by
    rw [card_filter, sq, sum_mul]
    apply sum_congr rfl
    intro y _
    rw [mul_sum]
    apply sum_congr rfl
    intro z _
    by_cases hy : x ∈ R y <;> by_cases hz : x ∈ R z <;> simp [hy,hz]
  simp_rw [h]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  rw [sum_boole]
  simp only [Nat.cast_id,filter_mem_eq_inter,univ_inter]

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

def involutions (G : Type*) [Group G] [Fintype G] [DecidableEq G] : Finset G :=
  univ.filter fun g => g ≠ 1 ∧ g*g=1

def productMiss (A : Finset G) := Fintype.card G - (products A).card

def quotientMiss (A : Finset G) := Fintype.card G - (quotients A).card

def witnesses (A : Finset G) := ((involutions G).filter fun g => A ∈ missingQuotients g).card

theorem witnesses_le (A : Finset G) : witnesses A ≤ quotientMiss A := by
  have h : (involutions G).filter (fun g => A ∈ missingQuotients g) ⊆ (quotients A)ᶜ := by
    intro g hg
    exact mem_compl.mpr (mem_filter.mp (mem_filter.mp hg).2).2
  simpa only [witnesses,quotientMiss,Finset.card_compl] using card_le_card h

theorem sum_productMiss :
    ∑ A : Finset G, productMiss A = ∑ g : G, (missingProducts g).card := by
  rw [←incidence_sum]
  apply sum_congr rfl
  intro A _
  rw [productMiss,←Finset.card_compl]
  congr 1
  ext g
  simp [missingProducts]

theorem sum_witnesses :
    (∑ A : Finset G, witnesses A) = ∑ g ∈ involutions G, (missingQuotients g).card :=
  incidence_sum _ _

theorem square_witnesses :
    (∑ A : Finset G, witnesses A ^ 2) = ∑ g ∈ involutions G, ∑ h ∈ involutions G,
      (missingQuotients g ∩ missingQuotients h).card :=
  incidence_square_sum _ _

theorem dominance_from_witnesses
    (hm : (∑ A : Finset G, productMiss A) * (∑ A : Finset G, witnesses A^2) <
      (∑ A : Finset G, witnesses A)^2) : ProductDominant G := by
  have h := dominance_of_moments (univ : Finset (Finset G)) quotientMiss productMiss witnesses
    (fun _ _ => witnesses_le _) hm
  have a (A : Finset G) := card_le_univ (products A)
  have b (A : Finset G) := card_le_univ (quotients A)
  have i (A : Finset G) : productMiss A < quotientMiss A ↔ (quotients A).card < (products A).card := by
    unfold productMiss quotientMiss
    specialize a A
    specialize b A
    omega
  have j (A : Finset G) : quotientMiss A < productMiss A ↔ (products A).card < (quotients A).card := by
    unfold productMiss quotientMiss
    specialize a A
    specialize b A
    omega
  simpa only [i,j,ProductDominant] using h

end AscoliDihedral
