module

public import conjectures.AscoliDihedralDominance.Discounts
public import conjectures.AscoliDihedralDominance.PairSides
public import conjectures.AscoliDihedralDominance.SliceCriterion
import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
namespace AscoliDihedral
open Equiv Function Finset
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

def orderValue (g : G) := periodValue (quotientStep g) 1

omit [Fintype G] [DecidableEq G] in
private theorem left_iter (g : G) (k : ℕ) (x : G) : (⇑(quotientStep g))^[k] x = g^k*x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply',ih,pow_succ']
    exact (mul_assoc _ _ _).symm

theorem orderValue_eq (g : G) : orderValue g = orderOf g := by
  rw [orderValue,periodValue_eq]
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    change (⇑(quotientStep g))^[orderOf g] 1=1
    rw [left_iter,pow_orderOf_eq_one,one_mul]
  · apply orderOf_dvd_of_pow_eq_one
    have hh : (⇑(quotientStep g))^[period (quotientStep g) 1] 1=1 := isPeriodicPt_minimalPeriod _ _
    simpa [left_iter] using hh

omit [DecidableEq G] in
private theorem matching_period (g : G) (h₀ : g≠1) (h₂ : g*g=1) (x : G) :
    period (quotientStep g) x =2 := by
  have h : (quotientStep g) ((quotientStep g) x) = x := by
    change g*(g*x)=x
    rw [←mul_assoc,h₂,one_mul]
  have hd := (twice_fixed_iff (quotientStep g) x).mp h
  have hn := period_pos (quotientStep g) x
  have he : period (quotientStep g) x≠1 := by
    intro y
    have eq := minimalPeriod_eq_one_iff_isFixedPt.mp y
    change g*x=x at eq
    exact h₀ (mul_right_cancel (eq.trans (one_mul x).symm))
  have := Nat.le_of_dvd (by decide : 0<2) hd
  omega

omit [Group G] [Fintype G] in
theorem weight_sdiff (B : ℕ) (C S : Finset (Finset G)) (h : C⊆S) :
    familyWeight B (S \ C) = familyWeight B S-familyWeight B C := by
  have hh := Finset.sum_sdiff (f := fun A : Finset G => B^A.card) h
  unfold familyWeight
  omega

namespace Dih
variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def discount (trim : Bool) (g : Dih H) := if trim then common g else ∅

def discountValue (B : ℕ) (xs : List H) (trim : Bool) (g : Dih H) :=
  if trim then evaluateCommon B xs g else 0

def singleValue (B N : ℕ) := (weightedPair B 2).1 ^ (N/2)

def pairValue (B : ℕ) (g h : Dih H) :=
  let k := 2*orderValue (g*h)
  (weightedPair B k).1 ^ (Fintype.card (Dih H)/k)

def data (B : ℕ) (xs : List H) (trim : Bool) : ℕ×ℕ×ℕ :=
  let T := involutions (Dih H)
  let W := singleValue B (Fintype.card (Dih H))
  let v := discountValue B xs trim
  ((∑ g ∈ T, (W - v g)),
   (∑ gh ∈ T×ˢT, if gh.1=gh.2 then W - v gh.1 else pairValue B gh.1 gh.2),
   (∑ g : Dih H, (evaluatePerm B (productStep g) - v g)))

private theorem discount_in (trim : Bool) (g : Dih H) :
    discount trim g ⊆ missingQuotients g ∩ missingProducts g := by
  cases trim <;> simp [discount,common,inter_comm]

private theorem discount_correct (B : ℕ) (xs : List H) (hn : xs.Nodup) (hu : xs.toFinset=univ)
    (trim : Bool) (g : Dih H) : discountValue B xs trim g=familyWeight B (discount trim g) := by
  cases trim <;> simp [discountValue,discount,evaluateCommon_eq B xs hn hu,familyWeight]

private theorem goodValue (B : ℕ) (xs : List H) (hn : xs.Nodup) (hu : xs.toFinset=univ)
    (trim : Bool) (g : Dih H) (hg : g∈involutions (Dih H)) :
    singleValue B (Fintype.card (Dih H)) - discountValue B xs trim g =
      familyWeight B (good (discount trim) g) := by
  rw [good,weight_sdiff B _ _ ((discount_in trim g).trans inter_subset_left),
    discount_correct B xs hn hu,eval_missing_quotients,evaluatePerm_eq]
  congr 1
  exact (uniform_weight B 2 _ (matching_period g (mem_filter.mp hg).2.1 (mem_filter.mp hg).2.2) (by decide)).symm

private theorem badValue (B : ℕ) (xs : List H) (hn : xs.Nodup) (hu : xs.toFinset=univ)
    (trim : Bool) (g : Dih H) :
    evaluatePerm B (productStep g)-discountValue B xs trim g = familyWeight B (bad (discount trim) g) := by
  rw [bad,weight_sdiff B _ _ ((discount_in trim g).trans inter_subset_right),
    discount_correct B xs hn hu,eval_missing_products]

private theorem pairValue_eq (B : ℕ) (g h : Dih H) (hg : g∈involutions (Dih H))
    (hh : h∈involutions (Dih H)) :
    pairValue B g h = familyWeight B (missingQuotients g∩missingQuotients h) := by
  have M := Dih.pairSides (mem_filter.mp hg).2.1 (mem_filter.mp hh).2.1
    (mem_filter.mp hg).2.2 (mem_filter.mp hh).2.2
  rw [M.pair_formula,pairValue,orderValue_eq]

theorem data_eq (B : ℕ) (xs : List H) (hn : xs.Nodup) (hu : xs.toFinset=univ) (trim : Bool) :
    data B xs trim =
      ((∑ g ∈ involutions (Dih H), familyWeight B (good (discount trim) g)),
       (∑ gh ∈ involutions (Dih H)×ˢinvolutions (Dih H), familyWeight B (pairFamily (discount trim) gh)),
       (∑ g : Dih H, familyWeight B (bad (discount trim) g))) := by
  unfold data
  apply Prod.ext
  · exact sum_congr rfl (fun g hg => goodValue B xs hn hu trim g hg)
  apply Prod.ext
  · apply sum_congr rfl
    intro gh hgh
    by_cases he : gh.1=gh.2
    · simpa [pairFamily,he] using goodValue B xs hn hu trim gh.1 (mem_product.mp hgh).1
    · simpa [pairFamily,he] using pairValue_eq B gh.1 gh.2 (mem_product.mp hgh).1 (mem_product.mp hgh).2
  · exact sum_congr rfl (fun g _ => badValue B xs hn hu trim g)

def lowerTotal (N k : ℕ) (d : ℕ×ℕ×ℕ) : ℤ :=
  let B := packBase N
  ∑ m ∈ Ico k (N+1), momentLower (N.choose m) (digit B m d.1) (digit B m d.2.1) (digit B m d.2.2)

theorem finite_case (xs : List H) (hn : xs.Nodup) (hu : xs.toFinset=univ) (trim : Bool) (k : ℕ)
    (hk : k≤Fintype.card (Dih H)+1) (base : ℤ)
    (hbase : base≤∑ m∈range k, gainAt (Dih H) m)
    (h : 0<base+lowerTotal (Fintype.card (Dih H)) k (data (packBase (Fintype.card (Dih H))) xs trim)) :
    ProductDominant (Dih H) := by
  let n := Fintype.card (Dih H)
  apply dominance_from_gains
  rw [←sum_range_add_sum_Ico _ hk]
  apply h.trans_le
  apply add_le_add hbase
  rw [lowerTotal,data_eq _ xs hn hu]
  apply sum_le_sum
  intro m hm
  exact slice_bound _ (discount_in trim) m (by have := (mem_Ico.mp hm).2; omega)

end Dih
end AscoliDihedral
