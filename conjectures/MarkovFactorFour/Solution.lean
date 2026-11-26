module

public import conjectures.MarkovFactorFour.Characters
public import conjectures.MarkovFactorFour.Statement
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Data.ZMod.Basic

@[expose] public section
namespace MarkovFactorFour
open MvPolynomial

private theorem vanishes {R : Type*} [CommRing R] (φ : Poly →+* R) (four : (4 : R)=0)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (hc : a.Coprime b)
    (hu : (φ u)^a=0) (hv : (φ v)^b=0) : φ (numerator a b) = 0 := by
  have hL : IsUnit (1+φ u+φ v) := by
    rw [add_assoc]
    exact ((Commute.all _ _).isNilpotent_add ⟨a,hu⟩ ⟨b,hv⟩).isUnit_one_add
  obtain ⟨s,hsnil,⟨c,hc'⟩,hs⟩ := small_root (show IsNilpotent (φ u) from ⟨a,hu⟩) hL
  obtain ⟨t,htnil,⟨d,hd⟩,ht⟩ := small_root (show IsNilpotent (φ v) from ⟨b,hv⟩) hL
  have hsa : s^a=0 := by rw [hc',mul_pow,hu,zero_mul]
  have htb : t^b=0 := by rw [hd,mul_pow,hv,zero_mul]
  have H := trace_identity φ four s t hs ht hsnil htnil a b ha hb hc
  dsimp only at H
  rw [hsa,htb,zero_mul,mul_zero,add_zero] at H
  exact hL.mul_right_eq_zero.mp H

private abbrev P4 := MvPolynomial (Fin 2) (ZMod 4)

/-- Every coefficient in the open rectangle is a multiple of four. -/
theorem rectangle {a b : ℕ} (ha : 0<a) (hb : 0<b) (hc : a.Coprime b)
    {i j : ℕ} (hi : i<a) (hj : j<b) : (4 : ℤ) ∣ (numerator a b).coeff (exponent i j) := by
  classical
  let gens : Set (Fin 2 →₀ ℕ) := {Finsupp.single 0 a, Finsupp.single 1 b}
  let I : Ideal P4 := Ideal.span ((fun d => monomial d (1 : ZMod 4)) '' gens)
  let reduce : Poly →+* P4 := MvPolynomial.map (Int.castRingHom (ZMod 4))
  let π := Ideal.Quotient.mk I
  let φ := π.comp reduce
  have four : (4 : P4 ⧸ I)=0 := by
    have h := congrArg (π.comp (MvPolynomial.C (σ := Fin 2))) (show (4 : ZMod 4)=0 by decide)
    simpa only [map_ofNat,map_zero] using h
  have zero_power (x : Fin 2) (n : ℕ) (hx : Finsupp.single x n ∈ gens) : (φ (X x))^n=0 := by
    change (π (map (Int.castRingHom (ZMod 4)) (X x)))^n=0
    rw [map_X, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, X_pow_eq_monomial]
    exact Ideal.subset_span ⟨_,hx,rfl⟩
  have hu := zero_power 0 a (by simp [gens])
  have hv := zero_power 1 b (by simp [gens])
  have hz := vanishes φ four ha hb hc hu hv
  have hm : reduce (numerator a b) ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp hz
  have hz' : (reduce (numerator a b)).coeff (exponent i j)=0 := by
    by_contra h
    obtain ⟨s,hs,hle⟩ := mem_ideal_span_monomial_image.mp hm _ (mem_support_iff.mpr h)
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl|rfl
    · have hle' := hle 0
      simp [exponent] at hle'
      omega
    · have hle' := hle 1
      simp [exponent] at hle'
      omega
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
  simpa only [reduce, coeff_map, Int.coe_castRingHom] using hz'

theorem resolution : Conjecture := fun _ _ ha hab hc _ _ hi hj _ =>
  rectangle ha (lt_of_lt_of_le ha hab) hc hi hj

/-- info: 'MarkovFactorFour.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end MarkovFactorFour
