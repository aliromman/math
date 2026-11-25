module

public import conjectures.AscoliDihedralDominance.CycleEvaluation
public import conjectures.AscoliDihedralDominance.Digits

@[expose] public section
open Finset Equiv
namespace AscoliDihedral
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bits_weight (B : ℕ) (A : Finset X) : colorWeight B (bitsEquiv X A) = B^A.card := by
  simp [colorWeight,bitsEquiv]

theorem weight_by_equiv (B : ℕ) (S : Finset (Finset X)) (U : (X → Bool) → Prop) [DecidablePred U]
    (he : ∀ A, A∈S ↔ U (bitsEquiv X A)) :
    familyWeight B S = ∑ f : X → Bool, if U f then colorWeight B f else 0 := by
  classical
  rw [←(bitsEquiv X).sum_comp (fun f => if U f then colorWeight B f else 0)]
  simp only [←he,bits_weight]
  simp [familyWeight]

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem eval_missing_products (B : ℕ) (g : G) :
    familyWeight B (missingProducts g) = evaluatePerm B (productStep g) := by
  rw [evaluatePerm_eq]
  exact weight_by_equiv B _ _ (fun A => by simp [missingProducts,missing_product,avoids_bits])

theorem eval_missing_quotients (B : ℕ) (g : G) :
    familyWeight B (missingQuotients g) = evaluatePerm B (quotientStep g) := by
  rw [evaluatePerm_eq]
  exact weight_by_equiv B _ _ (fun A => by simp [missingQuotients,missing_quotient,avoids_bits])

def alternating {G : Type*} [Group G] (g h : G) (c : G → Bool) (x : G) :=
  if c x then g*x else h*x

structure TwoMatchings {G : Type*} [Group G] (g h : G) where
  side : G → Bool
  leftInvol : g*g=1
  rightInvol : h*h=1
  leftFlip : ∀ x, side (g*x) = !(side x)
  rightFlip : ∀ x, side (h*x) = !(side x)

namespace TwoMatchings
variable {g h : G}

def perm (M : TwoMatchings g h) : Perm G where
  toFun := alternating g h M.side
  invFun := alternating h g M.side
  left_inv x := by cases hM : M.side x <;> simp [alternating,hM,M.leftFlip,M.rightFlip,←mul_assoc,
    M.leftInvol,M.rightInvol]
  right_inv x := by cases hM : M.side x <;> simp [alternating,hM,M.leftFlip,M.rightFlip,←mul_assoc,
    M.leftInvol,M.rightInvol]

omit [Fintype G] [DecidableEq G] in
theorem coloring (M : TwoMatchings g h) (f : G→Bool) :
    coloringOK M.perm f ↔ coloringOK (quotientStep g) f ∧ coloringOK (quotientStep h) f := by
  constructor
  · intro hf
    constructor <;> intro x
    · change (!(f x && f (g*x)))=true
      cases hc : M.side x
      · have he := hf (g*x)
        simpa [perm,alternating,M.leftFlip,hc,←mul_assoc,M.leftInvol,Bool.and_comm] using he
      · simpa [perm,alternating,hc] using hf x
    · change (!(f x && f (h*x)))=true
      cases hc : M.side x
      · simpa [perm,alternating,hc] using hf x
      · have he := hf (h*x)
        simpa [perm,alternating,M.rightFlip,hc,←mul_assoc,M.rightInvol,Bool.and_comm] using he
  · rintro ⟨hf,hh⟩ x
    cases hc : M.side x
    · simpa [perm,alternating,hc,quotientStep] using hh x
    · simpa [perm,alternating,hc,quotientStep] using hf x

theorem weight (M : TwoMatchings g h) (B : ℕ) :
    familyWeight B (missingQuotients g ∩ missingQuotients h) = evaluatePerm B M.perm := by
  rw [evaluatePerm_eq]
  apply weight_by_equiv
  intro A
  rw [M.coloring]
  simp [missingQuotients,missing_quotient,avoids_bits]

end TwoMatchings
end AscoliDihedral
