module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.Init
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Definitions and lemmas from Alex Chengyu Li’s proof of coefficient concavity.
Adapted from the MIT-licensed archive, DOI 10.5281/zenodo.22661864. -/

@[expose] public section
namespace PermutationPeaks

namespace PeakPolynomials
open Finset

abbrev Position (n : ℕ) := {i : ℕ // i ∈ Icc 1 n}

abbrev Permutation (n : ℕ) := Equiv.Perm (Position n)

def valueAt {n : ℕ} (π : Permutation n) (i : ℕ) : ℕ :=
  if hi : i ∈ Icc 1 n then (π ⟨i,hi⟩).val else n+1

@[simp] theorem valueAt_position {n : ℕ} (π : Permutation n) (i : Position n) :
    valueAt π i.val=(π i).val := by simp [valueAt,i.property]

def IsPeak {n : ℕ} (π : Permutation n) (i : ℕ) : Prop :=
  2 ≤ i ∧ i < n ∧ valueAt π (i-1) < valueAt π i ∧ valueAt π (i+1) < valueAt π i

instance {n : ℕ} (π : Permutation n) (i : ℕ) : Decidable (IsPeak π i) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def peaks {n : ℕ} (π : Permutation n) : Finset ℕ :=
  (Icc 2 (n-1)).filter (IsPeak π)

@[simp] theorem mem_peaks {n : ℕ} (π : Permutation n) (i : ℕ) : i ∈ peaks π ↔ IsPeak π i := by
  simp only [peaks,mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨mem_Icc.mpr ⟨h.1,by have := h.2.1; omega⟩,h⟩

def Admissible (S : Finset ℕ) : Prop :=
  (∀ i ∈ S, 2 ≤ i) ∧ (∀ i ∈ S, i+1 ∉ S)

theorem peaks_admissible {n : ℕ} (π : Permutation n) : Admissible (peaks π) := by
  constructor
  · intro i hi
    exact ((mem_peaks π i).mp hi).1
  · intro i hi hnext
    have h1 := (mem_peaks π i).mp hi
    have h2 := (mem_peaks π (i+1)).mp hnext
    have hleft := h2.2.2.1
    have hright := h1.2.2.2
    simp only [Nat.add_sub_cancel] at hleft
    exact lt_asymm hleft hright

def peakCount (n : ℕ) (S : Finset ℕ) : ℕ :=
  ((univ : Finset (Permutation n)).filter (fun π => peaks π=S)).card

theorem inadmissible_peakCount (n : ℕ) (S : Finset ℕ) (hS : ¬ Admissible S) : peakCount n S=0 := by
  unfold peakCount
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro π hπ
  have heq := (mem_filter.mp hπ).2
  have ha := peaks_admissible π
  rw [heq] at ha
  exact hS ha

theorem peakCount_zero_of_large_member (n : ℕ) (S : Finset ℕ) {i : ℕ}
    (hi : i ∈ S) (hlarge : n ≤ i) : peakCount n S=0 := by
  unfold peakCount
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro π hπ
  have heq := (mem_filter.mp hπ).2
  have hmem : i ∈ peaks π := by rw [heq]; exact hi
  have hbound := ((mem_peaks π i).mp hmem).2.1
  omega

end PeakPolynomials
namespace PeakPolynomials
open Finset

def positionFin (n : ℕ) : Position n ≃o Fin n where
  toFun i := ⟨i.val-1,by have := mem_Icc.mp i.property; omega⟩
  invFun i := ⟨i.val+1,mem_Icc.mpr ⟨by omega,by have := i.isLt; omega⟩⟩
  left_inv i := by apply Subtype.ext; have := mem_Icc.mp i.property; simp; omega
  right_inv i := by apply Fin.ext; simp
  map_rel_iff' := by
    intro i j
    change (i.val-1 ≤ j.val-1) ↔ i.val ≤ j.val
    have hi := mem_Icc.mp i.property
    have hj := mem_Icc.mp j.property
    omega

def finPermutation {n : ℕ} (π : Permutation n) : Equiv.Perm (Fin n) :=
  (positionFin n).symm.toEquiv.trans (π.trans (positionFin n).toEquiv)

def fromFinPermutation {n : ℕ} (π : Equiv.Perm (Fin n)) : Permutation n :=
  (positionFin n).toEquiv.trans (π.trans (positionFin n).symm.toEquiv)

theorem finPermutation_roundtrip {n : ℕ} (π : Permutation n) :
    fromFinPermutation (finPermutation π)=π := by
  ext i
  simp [finPermutation,fromFinPermutation]

def firstValues {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) : Finset (Fin (a+b)) :=
  univ.image (fun i : Fin a => π (Fin.castAdd b i))

theorem firstValues_card {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) : (firstValues π).card=a := by
  rw [firstValues,card_image_of_injective]
  · exact card_fin a
  · intro i j hij
    have h := π.injective hij
    apply Fin.ext
    exact congrArg (fun z : Fin (a+b) => z.val) h

theorem second_not_first {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) (j : Fin b) :
    π (Fin.natAdd a j) ∉ firstValues π := by
  intro h
  obtain ⟨i,hi,heq⟩ := mem_image.mp h
  have hv := congrArg Fin.val (π.injective heq)
  have hi' := i.isLt
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

noncomputable def firstBlockEquiv {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) : Fin a ≃ firstValues π :=
  Equiv.ofBijective (fun i => ⟨π (Fin.castAdd b i),mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j heq
      have h := π.injective (congrArg Subtype.val heq)
      apply Fin.ext
      exact congrArg (fun z : Fin (a+b) => z.val) h
    · intro x
      obtain ⟨i,hi,heq⟩ := mem_image.mp x.property
      exact ⟨i,Subtype.ext heq⟩)

noncomputable def secondBlockEquiv {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) : Fin b ≃ ↥((firstValues π)ᶜ : Finset (Fin (a+b))) :=
  Equiv.ofBijective (fun j => ⟨π (Fin.natAdd a j),mem_compl.mpr (second_not_first π j)⟩) (by
    constructor
    · intro i j heq
      have h := congrArg Fin.val (π.injective (congrArg Subtype.val heq))
      apply Fin.ext
      simpa only [Fin.val_natAdd,Nat.add_left_cancel_iff] using h
    · intro x
      obtain ⟨z,hz⟩ := (@finSumFinEquiv a b).surjective (π.symm x.val)
      cases z with
      | inl i =>
        have heq : π (Fin.castAdd b i)=x.val := by
          simpa only [finSumFinEquiv_apply_left,π.apply_symm_apply] using congrArg π hz
        have hmem : x.val ∈ firstValues π := mem_image.mpr ⟨i,mem_univ _,heq⟩
        exact False.elim ((mem_compl.mp x.property) hmem)
      | inr j =>
        refine ⟨j,Subtype.ext ?_⟩
        simpa only [finSumFinEquiv_apply_right,π.apply_symm_apply] using congrArg π hz)

theorem secondValues_card {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) : ((firstValues π)ᶜ).card=b := by
  rw [card_compl,firstValues_card,Fintype.card_fin]
  omega

noncomputable def standardizedFirst {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) : Equiv.Perm (Fin a) :=
  (firstBlockEquiv π).trans ((firstValues π).orderIsoOfFin (firstValues_card π)).symm.toEquiv

noncomputable def standardizedSecond {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) : Equiv.Perm (Fin b) :=
  (secondBlockEquiv π).trans (((firstValues π)ᶜ).orderIsoOfFin (secondValues_card π)).symm.toEquiv

theorem standardization_first_values {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) (i : Fin a) :
    ((firstValues π).orderIsoOfFin (firstValues_card π) (standardizedFirst π i)).val=π (Fin.castAdd b i) := by
  simp only [standardizedFirst,Equiv.trans_apply,OrderIso.coe_toEquiv,OrderIso.apply_symm_apply]
  rfl

theorem standardization_second_values {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) (j : Fin b) :
    (((firstValues π)ᶜ).orderIsoOfFin (secondValues_card π) (standardizedSecond π j)).val=π (Fin.natAdd a j) := by
  simp only [standardizedSecond,Equiv.trans_apply,OrderIso.coe_toEquiv,OrderIso.apply_symm_apply]
  rfl

theorem first_comparison_preserved {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) (i j : Fin a) :
    standardizedFirst π i < standardizedFirst π j ↔ π (Fin.castAdd b i) < π (Fin.castAdd b j) := by
  have h := ((firstValues π).orderIsoOfFin (firstValues_card π)).lt_iff_lt (x := standardizedFirst π i) (y := standardizedFirst π j)
  change (_ < _) ↔ _ at h
  rw [← standardization_first_values π i,← standardization_first_values π j]
  exact h.symm

theorem second_comparison_preserved {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) (i j : Fin b) :
    standardizedSecond π i < standardizedSecond π j ↔ π (Fin.natAdd a i) < π (Fin.natAdd a j) := by
  rw [← standardization_second_values π i,← standardization_second_values π j]
  exact (((firstValues π)ᶜ).orderIsoOfFin (secondValues_card π)).lt_iff_lt.symm

end PeakPolynomials
namespace PeakPolynomials
open Finset

abbrev ValueChoice (a b : ℕ) := {S : Finset (Fin (a+b)) // S.card=a}

abbrev BlockData (a b : ℕ) := ValueChoice a b × Equiv.Perm (Fin a) × Equiv.Perm (Fin b)

def subsetGlue {n : ℕ} (S : Finset (Fin n)) : ↥S ⊕ ↥(Sᶜ : Finset (Fin n)) ≃ Fin n where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun x := if hx : x ∈ S then Sum.inl ⟨x,hx⟩ else Sum.inr ⟨x,mem_compl.mpr hx⟩
  left_inv x := by
    cases x with
    | inl x => simp [x.property]
    | inr x => simp [mem_compl.mp x.property]
  right_inv x := by dsimp; split_ifs <;> rfl

theorem choice_compl_card {a b : ℕ} (S : ValueChoice a b) : (S.valᶜ).card=b := by
  rw [card_compl,S.property,Fintype.card_fin]
  omega

noncomputable def assembleBlocks {a b : ℕ} (d : BlockData a b) : Equiv.Perm (Fin (a+b)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr
      (d.2.1.trans (d.1.val.orderIsoOfFin d.1.property).toEquiv)
      (d.2.2.trans ((d.1.valᶜ).orderIsoOfFin (choice_compl_card d.1)).toEquiv)).trans
      (subsetGlue d.1.val))

theorem assembleBlocks_first {a b : ℕ} (d : BlockData a b) (i : Fin a) :
    assembleBlocks d (Fin.castAdd b i)=(d.1.val.orderIsoOfFin d.1.property (d.2.1 i)).val := by
  simp [assembleBlocks,subsetGlue]

theorem assembleBlocks_second {a b : ℕ} (d : BlockData a b) (i : Fin b) :
    assembleBlocks d (Fin.natAdd a i)=((d.1.valᶜ).orderIsoOfFin (choice_compl_card d.1) (d.2.2 i)).val := by
  simp [assembleBlocks,subsetGlue]

theorem firstValues_assembled {a b : ℕ} (d : BlockData a b) : firstValues (assembleBlocks d)=d.1.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    rw [assembleBlocks_first]
    exact (d.1.val.orderIsoOfFin d.1.property (d.2.1 i)).property
  · intro hx
    obtain ⟨j,hj⟩ := (d.1.val.orderIsoOfFin d.1.property).surjective ⟨x,hx⟩
    obtain ⟨i,hi⟩ := d.2.1.surjective j
    apply mem_image.mpr
    refine ⟨i,mem_univ _,?_⟩
    rw [assembleBlocks_first,hi]
    exact congrArg Subtype.val hj

noncomputable def splitBlocks {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) : BlockData a b :=
  ⟨⟨firstValues π,firstValues_card π⟩,standardizedFirst π,standardizedSecond π⟩

theorem assemble_split {a b : ℕ} (π : Equiv.Perm (Fin (a+b))) : assembleBlocks (splitBlocks π)=π := by
  apply Equiv.ext
  intro i
  obtain ⟨z,hz⟩ := (@finSumFinEquiv a b).surjective i
  cases z with
  | inl j =>
    subst i
    rw [finSumFinEquiv_apply_left,assembleBlocks_first]
    exact standardization_first_values π j
  | inr j =>
    subst i
    rw [finSumFinEquiv_apply_right,assembleBlocks_second]
    exact standardization_second_values π j

theorem assembleBlocks_injective (a b : ℕ) : Function.Injective (@assembleBlocks a b) := by
  rintro ⟨S,A,B⟩ ⟨T,C,D⟩ h
  have hs := congrArg firstValues h
  rw [firstValues_assembled,firstValues_assembled] at hs
  have hST : S=T := Subtype.ext hs
  subst T
  have hA : A=C := by
    apply Equiv.ext
    intro i
    have hx := congrArg (fun π : Equiv.Perm (Fin (a+b)) => π (Fin.castAdd b i)) h
    rw [assembleBlocks_first,assembleBlocks_first] at hx
    apply (S.val.orderIsoOfFin S.property).injective
    exact Subtype.ext hx
  have hB : B=D := by
    apply Equiv.ext
    intro i
    have hx := congrArg (fun π : Equiv.Perm (Fin (a+b)) => π (Fin.natAdd a i)) h
    rw [assembleBlocks_second,assembleBlocks_second] at hx
    apply ((S.valᶜ).orderIsoOfFin (choice_compl_card S)).injective
    exact Subtype.ext hx
  simp only [hA,hB]

theorem split_assemble {a b : ℕ} (d : BlockData a b) : splitBlocks (assembleBlocks d)=d := by
  apply assembleBlocks_injective a b
  exact assemble_split _

theorem valueChoice_card (a b : ℕ) : Fintype.card (ValueChoice a b)=(a+b).choose a := by
  let e : ValueChoice a b ≃ ↥((univ : Finset (Fin (a+b))).powersetCard a) :=
    Equiv.subtypeEquivRight (fun S => by simp)
  rw [Fintype.card_congr e,Fintype.card_coe,card_powersetCard,card_univ,Fintype.card_fin]

end PeakPolynomials

end PermutationPeaks
