module

public import conjectures.PermutationPeaks.PeakPolynomials

/-! Definitions and lemmas from Alex Chengyu Li’s proof of coefficient concavity.
Adapted from the MIT-licensed archive, DOI 10.5281/zenodo.22661864. -/

@[expose] public section
namespace PermutationPeaks

namespace PeakPolynomials
open Polynomial Finset ReflectedNewton

noncomputable def peakCoefficient (S : Finset ℕ) (k : ℕ) : ℝ :=
  backward (peakPolynomial S).eval (k+1) (maxPeak S : ℝ)

theorem peakCoefficient_formula (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    (k : ℕ) (hk : k<maxPeak S-1) :
    peakCoefficient S k=reflectedCoefficient (peakPolynomial (S.erase (maxPeak S))) (maxPeak S) k := by
  unfold peakCoefficient
  rw [peakPolynomial_reflected S hS hne]
  exact reflectedLift_coefficient _ _ k hk

theorem peakCoefficient_expansion (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) (x : ℝ) :
    (peakPolynomial S).eval x = ∑ k ∈ range (maxPeak S-1),
      peakCoefficient S k * rising (k+1) (x-maxPeak S) := by
  calc
    _ = (reflectedLift (peakPolynomial (S.erase (maxPeak S))) (maxPeak S)).eval x := by
      rw [peakPolynomial_reflected S hS hne]
    _ = _ := by
      have hv := congrFun (reflectedLift_eval (peakPolynomial (S.erase (maxPeak S))) (maxPeak S)) x
      rw [hv]
      apply sum_congr rfl
      intro k hk
      rw [peakCoefficient_formula S hS hne k (mem_range.mp hk)]

theorem peakCoefficient_nonnegative (S : Finset ℕ) (hS : Admissible S) (k : ℕ) :
    0 ≤ peakCoefficient S k := peak_backward_nonnegative S hS (maxPeak S) le_rfl (k+1)

theorem peakCoefficient_symmetric (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty)
    (k : ℕ) (hk : k ≤ maxPeak S-2) :
    peakCoefficient S k=peakCoefficient S (maxPeak S-2-k) := by
  have hm := (last_peak_reduction hS hne).1
  rw [peakCoefficient_formula S hS hne k (by omega),
    peakCoefficient_formula S hS hne (maxPeak S-2-k) (by omega)]
  exact reflectedCoefficient_symmetry _ _ _ hm hk

noncomputable def peakPaddedCoefficient (S : Finset ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k ∧ k ≤ (maxPeak S : ℤ)-2 then peakCoefficient S k.toNat else 0

theorem peakPaddedCoefficient_eq (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) (k : ℤ) :
    peakPaddedCoefficient S k=paddedCoefficient (peakPolynomial (S.erase (maxPeak S))) (maxPeak S) k := by
  unfold peakPaddedCoefficient paddedCoefficient
  split_ifs with hk
  · exact peakCoefficient_formula S hS hne k.toNat (by omega)
  · rfl

end PeakPolynomials
namespace ReflectedNewton
open Finset

theorem nonnegative_data_symmetric_concave (P : Polynomial ℝ) (m : ℕ)
    (hm : 2 ≤ m) (hP : P.natDegree ≤ m-2)
    (hdata : ∀ j, 0 ≤ backward P.eval j ((m : ℝ)-2)) :
    SymmetricConcave (paddedCoefficient P m) ((m : ℤ)-2) := by
  constructor
  · omega
  · simp [paddedCoefficient]
  · rw [paddedCoefficient,ite_eq_right (by omega)]
  · intro k hk hk'
    rw [paddedCoefficient_kernel P m hm hP,paddedCoefficient_kernel P m hm hP]
    apply sum_congr rfl
    intro j hj
    rw [kernel_reflection]
  · intro k hk hk'
    exact paddedCoefficient_concave P m hm hP hdata k ⟨hk,hk'⟩

end ReflectedNewton
namespace PeakPolynomials
open Polynomial Finset ReflectedNewton

theorem deleted_peak_input (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    (peakPolynomial (S.erase (maxPeak S))).natDegree ≤ maxPeak S-2 ∧
      ∀ j, 0 ≤ backward (peakPolynomial (S.erase (maxPeak S))).eval j ((maxPeak S : ℝ)-2) := by
  have hd := last_peak_reduction hS hne
  have hmax : maxPeak (S.erase (maxPeak S)) ≤ maxPeak S-2 := by
    apply Finset.sup_le
    intro i hi
    have := (hd.2.2.1 i hi).2
    change i ≤ maxPeak S-2
    omega
  constructor
  · have := peakPolynomial_degree (S.erase (maxPeak S)); omega
  · intro j
    have h := peak_backward_nonnegative (S.erase (maxPeak S)) hd.2.1 (maxPeak S-2) hmax j
    have he : ((maxPeak S-2 : ℕ) : ℝ)=(maxPeak S : ℝ)-2 := by
      rw [Nat.cast_sub hd.1]
      norm_num
    simpa only [he] using h

theorem peakCoefficient_symmetric_concave (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    SymmetricConcave (peakPaddedCoefficient S) ((maxPeak S : ℤ)-2) := by
  have hd := deleted_peak_input S hS hne
  have he : peakPaddedCoefficient S=paddedCoefficient (peakPolynomial (S.erase (maxPeak S))) (maxPeak S) :=
    funext (peakPaddedCoefficient_eq S hS hne)
  rw [he]
  exact nonnegative_data_symmetric_concave _ _ (last_peak_reduction hS hne).1 hd.1 hd.2

end PeakPolynomials

end PermutationPeaks
