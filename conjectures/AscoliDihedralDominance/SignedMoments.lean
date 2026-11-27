module

public import conjectures.AscoliDihedralDominance.Digits

@[expose] public section
open Finset
namespace AscoliDihedral

variable {X Y : Type*} [DecidableEq X]

theorem incidence_on (S : Finset X) (T : Finset Y) (R : Y → Finset X) :
    (∑ x ∈ S, (T.filter fun y => x∈R y).card) = ∑ y ∈ T, (R y ∩ S).card := by
  simp_rw [card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  rw [sum_boole]
  simp [filter_mem_eq_inter,inter_comm]

theorem pair_incidence_on (S : Finset X) (T : Finset Y) (R : Y → Finset X) :
    (∑ x ∈ S, (T.filter fun y => x∈R y).card^2) =
      ∑ y ∈ T, ∑ z ∈ T, ((R y∩R z)∩S).card := by
  have hx (x : X) : (T.filter fun y => x∈R y).card^2 =
      ∑ y ∈ T, ∑ z ∈ T, if x∈R y∩R z then 1 else 0 := by
    rw [card_filter,sq,sum_mul]
    apply sum_congr rfl
    intro y _
    rw [mul_sum]
    apply sum_congr rfl
    intro z _
    by_cases hy : x∈R y <;> by_cases hz : x∈R z <;> simp [hy,hz]
  simp_rw [hx]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  rw [sum_boole]
  simp only [Nat.cast_id,filter_mem_eq_inter,inter_comm (R y ∩ R z)]

def momentLower (size F D P : ℕ) : ℤ :=
  max (-(size:ℤ)) ((((F^2 + D-1)/D : ℕ):ℤ)-(P:ℤ))

private theorem support_lower (F D C : ℕ) (h : F^2≤C*D) :
    (F^2+D-1)/D≤C := by
  by_cases hz : D=0
  · simp [hz]
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hz)).mpr
    rw [Nat.succ_mul]
    omega

omit [DecidableEq X] in
theorem signed_lower (S : Finset X) (p q w : X→ℕ) (hw : ∀ x∈S, w x≤q x) (D : ℕ)
    (hD : (∑ x ∈ S,w x^2)≤D) :
    momentLower S.card (∑ x∈S,w x) D (∑ x∈S,p x) ≤
      (((S.filter fun x => p x<q x).card:ℤ)-(S.filter fun x => q x<p x).card) := by
  let W := (S.filter fun x => 0<w x).card
  have hC := (cauchy_card S w).trans (Nat.mul_le_mul_left W hD)
  have hW := support_lower _ _ _ hC
  have hb (x : X) (hx : x∈S) :
      (if 0<w x then 1 else 0)+(if q x<p x then 1 else 0) ≤
        p x+(if p x<q x then 1 else 0) := by
    have := hw x hx
    have := indicator_bound (q x) (p x)
    split_ifs at * <;> omega
  have h := sum_le_sum hb
  simp only [sum_add_distrib,sum_boole,Nat.cast_id] at h
  have hsize := (S.card_filter_le (fun x => q x < p x))
  dsimp [W] at hW
  unfold momentLower
  apply max_le <;> omega

end AscoliDihedral
