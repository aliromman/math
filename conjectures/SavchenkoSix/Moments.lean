module

public import conjectures.SavchenkoSix.Statement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section
namespace SavchenkoSix
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sum of the order-`k` principal minors of the skew sign matrix. -/
def minorSum (T : Tournament V) (k : ℕ) : ℤ :=
  ∑ s ∈ (univ : Finset V).powersetCard k, (T.sign.submatrix (Subtype.val : s → V) Subtype.val).det

omit [Fintype V] in
theorem sign_flip (T : Tournament V) (i j : V) : T.sign j i = -T.sign i j := by
  by_cases h : i = j
  · simp [Tournament.sign, h]
  · simp only [Tournament.sign, h, Ne.symm h, ite_false, T.orientation (Ne.symm h)]
    cases T.arc i j <;> decide

theorem minorSum_two (T : Tournament V) : minorSum T 2 = (Nat.choose (Fintype.card V) 2 : ℤ) := by
  classical
  unfold minorSum
  have one (s : Finset V) (hs : s ∈ univ.powersetCard 2) :
      (T.sign.submatrix (Subtype.val : s → V) Subtype.val).det = 1 := by
    let e := (Fintype.equivFinOfCardEq (show Fintype.card s = 2 by
      simpa using (mem_powersetCard.mp hs).2)).symm
    have ne : (e 0 : V) ≠ (e 1 : V) := fun h ↦ Fin.zero_ne_one (e.injective (Subtype.ext h))
    rw [← det_submatrix_equiv_self e, det_fin_two]
    simp only [submatrix_apply, sign_flip T (e 0) (e 1)]
    simp [Tournament.sign, ne]
    split <;> norm_num
  rw [Finset.sum_congr rfl one]
  simp

theorem trace_odd (T : Tournament V) (k : ℕ) (h : Odd k) :
    (T.sign ^ k).trace = 0 := by
  have hs : T.signᵀ = -T.sign := by ext i j; exact sign_flip T i j
  have ht := Matrix.trace_transpose (T.sign ^ k)
  rw [transpose_pow, hs, h.neg_pow, trace_neg] at ht
  omega

private theorem cast_minorSum (T : Tournament V) (k : ℕ) :
    (minorSum T k : ℂ) = ∑ s ∈ (univ : Finset V).powersetCard k,
      (((Int.castRingHom ℂ).mapMatrix T.sign).submatrix (Subtype.val : s → V) Subtype.val).det := by
  unfold minorSum
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  rfl

/-- Diagonalize the skew matrix by applying the Hermitian spectral theorem to its multiple by i. -/
private theorem eigenvalues (T : Tournament V) :
    ∃ f : V → ℂ, (∀ k : ℕ, MvPolynomial.aeval f (MvPolynomial.psum V ℂ k) =
      ((T.sign ^ k).trace : ℂ)) ∧ (∀ k ≤ Fintype.card V,
      MvPolynomial.aeval f (MvPolynomial.esymm V ℂ k) = (minorSum T k : ℂ)) := by
  classical
  let ρ := Int.castRingHom ℂ
  let A := ρ.mapMatrix T.sign
  have herm : (Complex.I • A).IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
      Complex.conj_I]
    change -(Complex.I) * (starRingEnd ℂ) (T.sign j i : ℂ) = Complex.I * (T.sign i j : ℂ)
    rw [sign_flip T i j]
    simp
  let U := herm.eigenvectorUnitary
  let d : V → ℂ := RCLike.ofReal ∘ herm.eigenvalues
  let f : V → ℂ := (-Complex.I) • d
  have diagA : A = Unitary.conjStarAlgAut ℂ _ U (diagonal f) := by
    have eq := congrArg ((-Complex.I) • ·) herm.spectral_theorem
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] at eq
    simpa only [f, diagonal_smul, map_smul] using eq
  refine ⟨f, ?_, ?_⟩
  · intro k
    have eq := congrArg (fun B : Matrix V V ℂ ↦ (B ^ k).trace) diagA
    change (A ^ k).trace = ((Unitary.conjStarAlgAut ℂ _ U (diagonal f)) ^ k).trace at eq
    rw [← map_pow (Unitary.conjStarAlgAut ℂ _ U), Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self,
      one_mul, diagonal_pow, trace_diagonal] at eq
    calc
      _ = ∑ i, f i ^ k := by simp [MvPolynomial.psum]
      _ = (A ^ k).trace := eq.symm
      _ = _ := by
        have hh := AddMonoidHom.map_trace ρ (T.sign ^ k)
        rw [← map_pow ρ.mapMatrix]
        exact hh.symm
  · intro k hk
    have eq : A.charpoly = (diagonal f).charpoly := by
      rw [diagA, Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← Matrix.mul_assoc,
        Unitary.coe_star_mul_self, one_mul]
    have aux := congrArg (fun P : Polynomial ℂ ↦ P.coeff (Fintype.card V - k)) eq
    simp only [charpoly_coeff_eq_sum_minors _ _ hk] at aux
    have h := mul_left_cancel₀ (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero)) aux
    rw [cast_minorSum]
    change _ = ∑ s ∈ (univ : Finset V).powersetCard k,
      (A.submatrix (Subtype.val : s → V) Subtype.val).det
    rw [h]
    simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X,
      submatrix_diagonal _ _ Subtype.val_injective, det_diagonal, Finset.prod_coe_sort,
      Function.comp_def]

private theorem trace_moments (T : Tournament V) (hn : 7 ≤ Fintype.card V) :
    (T.sign ^ 4).trace = 2 * (minorSum T 2 ^ 2 - 2 * minorSum T 4) ∧
    (T.sign ^ 6).trace =
      -2 * (minorSum T 2 ^ 3 - 3 * minorSum T 2 * minorSum T 4 + 3 * minorSum T 6) := by
  obtain ⟨f, hp, he⟩ := eigenvalues T
  let E (k : ℕ) := MvPolynomial.aeval f (MvPolynomial.esymm V ℂ k)
  let P (k : ℕ) := MvPolynomial.aeval f (MvPolynomial.psum V ℂ k)
  have step (k : ℕ) (hk : 0 < k) :
      P k = (-1 : ℂ) ^ (k + 1) * k * E k -
        ∑ a ∈ (antidiagonal k).filter (fun a ↦ a.1 ∈ Set.Ioo 0 k),
          (-1 : ℂ) ^ a.1 * E a.1 * P a.2 := by
    simpa only [P, E, map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum]
      using congrArg (MvPolynomial.aeval f : MvPolynomial V ℂ → ℂ)
        (MvPolynomial.psum_eq_mul_esymm_sub_sum V ℂ k hk)
  have odd_zero (k : ℕ) (hk : Odd k) : P k = 0 := by
    simp only [P, hp, trace_odd T k hk, Int.cast_zero]
  have p1 := odd_zero 1 (by decide)
  have p3 := odd_zero 3 (by decide)
  have p5 := odd_zero 5 (by decide)
  have s2 := step 2 (by decide)
  have s4 := step 4 (by decide)
  have s6 := step 6 (by decide)
  have a2 : (antidiagonal 2).filter (fun a : ℕ × ℕ ↦ a.1 ∈ Set.Ioo 0 2) = {(1,1)} := by decide
  have a4 : (antidiagonal 4).filter (fun a : ℕ × ℕ ↦ a.1 ∈ Set.Ioo 0 4) =
      {(1,3),(2,2),(3,1)} := by decide
  have a6 : (antidiagonal 6).filter (fun a : ℕ × ℕ ↦ a.1 ∈ Set.Ioo 0 6) =
      {(1,5),(2,4),(3,3),(4,2),(5,1)} := by decide
  rw [a2] at s2
  rw [a4] at s4
  rw [a6] at s6
  norm_num [p1] at s2
  norm_num [p1, p3, s2] at s4
  norm_num [p1, p3, p5, s2, s4] at s6
  have e2 := he 2 (by omega)
  have e4 := he 4 (by omega)
  have e6 := he 6 (by omega)
  change E 2 = _ at e2
  change E 4 = _ at e4
  change E 6 = _ at e6
  change P 4 = _ at s4
  change P 6 = _ at s6
  rw [show P 4 = _ from hp 4, e2, e4] at s4
  rw [show P 6 = _ from hp 6, e2, e4, e6] at s6
  constructor <;> apply (Int.cast_inj (α := ℂ)).mp <;> push_cast
  · linear_combination s4
  · linear_combination s6

theorem trace_four (T : Tournament V) (hn : 7 ≤ Fintype.card V) :
    (T.sign ^ 4).trace = 2 * (minorSum T 2 ^ 2 - 2 * minorSum T 4) :=
  (trace_moments T hn).1

theorem trace_six (T : Tournament V) (hn : 7 ≤ Fintype.card V) :
    (T.sign ^ 6).trace =
      -2 * (minorSum T 2 ^ 3 - 3 * minorSum T 2 * minorSum T 4 + 3 * minorSum T 6) :=
  (trace_moments T hn).2

end SavchenkoSix
