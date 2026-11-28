module

public import conjectures.PermutationPeaks.PeakCoefficients

/-! Definitions and lemmas from Alex Chengyu Li’s proof of coefficient concavity.
Adapted from the MIT-licensed archive, DOI 10.5281/zenodo.22661864. -/

@[expose] public section
namespace PermutationPeaks

namespace PeakPolynomials
open Finset

def blockIndex (S : Finset ℕ) (i : ℕ) : ℕ := (S.filter (fun p => p ≤ i)).card

theorem blockIndex_next (S : Finset ℕ) (i : ℕ) :
    blockIndex S (i+1)=blockIndex S i + if i+1 ∈ S then 1 else 0 := by
  have he : S.filter (fun p => p ≤ i+1) =
      if i+1 ∈ S then insert (i+1) (S.filter (fun p => p ≤ i)) else S.filter (fun p => p ≤ i) := by
    split_ifs with hi
    · ext p
      simp only [mem_filter,mem_insert]
      constructor
      · rintro ⟨hp,hpi⟩
        by_cases he : p=i+1
        · exact Or.inl he
        · exact Or.inr ⟨hp,by omega⟩
      · rintro (rfl | ⟨hp,hpi⟩)
        · exact ⟨hi,le_rfl⟩
        · exact ⟨hp,by omega⟩
    · ext p
      simp only [mem_filter]
      constructor
      · rintro ⟨hp,hpi⟩
        have hne : p≠i+1 := by intro h; exact hi (h ▸ hp)
        exact ⟨hp,by omega⟩
      · rintro ⟨hp,hpi⟩
        exact ⟨hp,by omega⟩
  unfold blockIndex
  rw [he]
  split_ifs with hi
  · rw [card_insert_of_notMem (by simp)]
  · simp

def blockKey {n : ℕ} (S : Finset ℕ) (i : Fin n) : ℕᵒᵈ ×ₗ Fin n :=
  toLex (OrderDual.toDual (blockIndex S i.val),i)

theorem blockKey_injective {n : ℕ} (S : Finset ℕ) : Function.Injective (@blockKey n S) := by
  intro i j h
  exact congrArg (fun x : ℕᵒᵈ ×ₗ Fin n => (ofLex x).2) h

def blockKeys (S : Finset ℕ) (n : ℕ) : Finset (ℕᵒᵈ ×ₗ Fin n) := univ.image (blockKey S)

theorem blockKeys_card (S : Finset ℕ) (n : ℕ) : (blockKeys S n).card=n := by
  rw [blockKeys,card_image_of_injective _ (blockKey_injective S),card_univ,Fintype.card_fin]

noncomputable def blockKeyEquiv (S : Finset ℕ) (n : ℕ) : Fin n ≃ ↥(blockKeys S n) :=
  Equiv.ofBijective (fun i => ⟨blockKey S i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j h
      exact blockKey_injective S (congrArg Subtype.val h)
    · intro x
      obtain ⟨i,hi,he⟩ := mem_image.mp x.property
      exact ⟨i,Subtype.ext he⟩)

noncomputable def increasingBlocksPermutation (S : Finset ℕ) (n : ℕ) : Equiv.Perm (Fin n) :=
  (blockKeyEquiv S n).trans ((blockKeys S n).orderIsoOfFin (blockKeys_card S n)).symm.toEquiv

theorem increasingBlocks_comparison (S : Finset ℕ) (n : ℕ) (i j : Fin n) :
    increasingBlocksPermutation S n i < increasingBlocksPermutation S n j ↔
      blockKey S i < blockKey S j := by
  have h := ((blockKeys S n).orderIsoOfFin (blockKeys_card S n)).lt_iff_lt
    (x:=increasingBlocksPermutation S n i) (y:=increasingBlocksPermutation S n j)
  simp only [increasingBlocksPermutation,Equiv.trans_apply,OrderIso.coe_toEquiv,
    OrderIso.apply_symm_apply] at h
  exact h.symm

end PeakPolynomials
namespace PeakPolynomials

theorem increasingBlocks_descent (S : Finset ℕ) (n i : ℕ) (hi : i+1<n) :
    increasingBlocksPermutation S n ⟨i+1,hi⟩ <
      increasingBlocksPermutation S n ⟨i,by omega⟩ ↔ i+1 ∈ S := by
  rw [increasingBlocks_comparison]
  simp only [blockKey,Prod.Lex.toLex_lt_toLex]
  change (blockIndex S i<blockIndex S (i+1) ∨
    blockIndex S (i+1)=blockIndex S i ∧ i+1 < i) ↔ i+1 ∈ S
  rw [blockIndex_next]
  by_cases h : i+1 ∈ S <;> simp [h]

theorem increasingBlocks_ascent (S : Finset ℕ) (n i : ℕ) (hi : i+1<n) :
    increasingBlocksPermutation S n ⟨i,by omega⟩ <
      increasingBlocksPermutation S n ⟨i+1,hi⟩ ↔ i+1 ∉ S := by
  rw [increasingBlocks_comparison]
  simp only [blockKey,Prod.Lex.toLex_lt_toLex]
  change (blockIndex S (i+1)<blockIndex S i ∨
    blockIndex S i=blockIndex S (i+1) ∧ i < i+1) ↔ i+1 ∉ S
  rw [blockIndex_next]
  by_cases h : i+1 ∈ S <;> simp [h]

theorem increasingBlocks_peak_iff (S : Finset ℕ) (n p : ℕ) (hp : 2 ≤ p) (hn : p<n) :
    IsPeak (fromFinPermutation (increasingBlocksPermutation S n)) p ↔
      p-1 ∉ S ∧ p ∈ S := by
  have he : p-2+2=p := by omega
  have he1 : p-2+1=p-1 := by omega
  have he2 : p-1+1=p := by omega
  have h := triplePeak_literal (increasingBlocksPermutation S n) (p-2) (by omega)
  conv_lhs at h => rw [he]
  rw [h]
  unfold TriplePeak
  rw [increasingBlocks_ascent S n (p-2) (by omega)]
  simp only [he1,he] at *
  have hd := increasingBlocks_descent S n (p-1) (by omega)
  simp only [he2] at hd
  rw [hd]

end PeakPolynomials
namespace PeakPolynomials
open Finset

theorem increasingBlocks_peak_set (S : Finset ℕ) (hS : Admissible S)
    (n : ℕ) (hn : maxPeak S<n) :
    peaks (fromFinPermutation (increasingBlocksPermutation S n))=S := by
  ext p
  rw [mem_peaks]
  constructor
  · intro hp
    exact ((increasingBlocks_peak_iff S n p hp.1 hp.2.1).mp hp).2
  · intro hp
    have hp2 := hS.1 p hp
    have hpn : p<n := lt_of_le_of_lt (le_maxPeak hp) hn
    apply (increasingBlocks_peak_iff S n p hp2 hpn).mpr
    refine ⟨?_,hp⟩
    intro hprev
    have hno := hS.2 (p-1) hprev
    have he : p-1+1=p := by omega
    rw [he] at hno
    exact hno hp

theorem admissible_peakCount_positive (S : Finset ℕ) (hS : Admissible S)
    (n : ℕ) (hn : maxPeak S<n) : 0<peakCount n S := by
  unfold peakCount
  apply card_pos.mpr
  refine ⟨fromFinPermutation (increasingBlocksPermutation S n),?_⟩
  exact mem_filter.mpr ⟨mem_univ _,increasingBlocks_peak_set S hS n hn⟩

theorem peakPolynomial_positive (S : Finset ℕ) (hS : Admissible S)
    (n : ℕ) (hn : maxPeak S<n) : 0<(peakPolynomial S).eval (n : ℝ) := by
  rw [peakPolynomial_normalized_count S n hn]
  unfold normalizedPeakCount
  apply div_pos
  · exact_mod_cast admissible_peakCount_positive S hS n hn
  · exact zpow_pos (by norm_num) _

end PeakPolynomials
namespace ReflectedNewton

theorem symmetric_concave_endpoint_lower_bound {a : ℤ → ℝ} {N i : ℤ}
    (ha : SymmetricConcave a N) (hi : 0 ≤ i) (hiN : i ≤ N) : a 0 ≤ a i := by
  by_cases hmid : 2*i ≤ N+1
  · exact sequence_monotone_left ha (by omega) hi hmid
  · have h := sequence_monotone_left ha (i:=0) (j:=N-i) (by omega) (by omega) (by omega)
    rw [ha.reflected i (by omega) (by omega)] at h
    exact h

end ReflectedNewton
namespace PeakPolynomials
open Polynomial Finset ReflectedNewton

theorem peakCoefficient_endpoint (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    peakCoefficient S 0=(peakPolynomial (S.erase (maxPeak S))).eval ((maxPeak S-1 : ℕ) : ℝ) := by
  have hm := (last_peak_reduction hS hne).1
  have hd := (deleted_peak_input S hS hne).1
  rw [peakCoefficient_formula S hS hne 0 (by omega)]
  unfold reflectedCoefficient
  simp only [Nat.sub_zero]
  rw [backward_polynomial_vanish _ (n:=maxPeak S-1) (by omega)]
  have he : ((maxPeak S-1 : ℕ) : ℝ)=(maxPeak S : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ maxPeak S)]
    norm_num
  simp only [backward,sub_zero,he]
  ring

theorem peakCoefficient_first_positive (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    0<peakCoefficient S 0 := by
  rw [peakCoefficient_endpoint S hS hne]
  have hd := last_peak_reduction hS hne
  apply peakPolynomial_positive _ hd.2.1
  have hmax : maxPeak (S.erase (maxPeak S)) ≤ maxPeak S-2 := by
    apply Finset.sup_le
    intro i hi
    have := (hd.2.2.1 i hi).2
    change i ≤ maxPeak S-2
    omega
  omega

theorem peakCoefficient_lower_bound (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    (k : ℕ) (hk : k ≤ maxPeak S-2) :
    (peakPolynomial (S.erase (maxPeak S))).eval ((maxPeak S-1 : ℕ) : ℝ) ≤ peakCoefficient S k := by
  have hm := (last_peak_reduction hS hne).1
  have h := symmetric_concave_endpoint_lower_bound (peakCoefficient_symmetric_concave S hS hne)
    (i:=(k : ℤ)) (by omega) (by omega)
  have hk' : 0 ≤ (k : ℤ) ∧ (k : ℤ) ≤ (maxPeak S : ℤ)-2 := by omega
  have hz : 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (maxPeak S : ℤ)-2 := by omega
  simp only [peakPaddedCoefficient,ite_eq_left hk',ite_eq_left hz,Int.toNat_natCast,Int.toNat_zero] at h
  rw [peakCoefficient_endpoint S hS hne] at h
  exact h

end PeakPolynomials

end PermutationPeaks
