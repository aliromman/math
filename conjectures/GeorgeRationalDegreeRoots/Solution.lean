module

public import conjectures.GeorgeRationalDegreeRoots.Statement
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace GeorgeRationalDegreeRoots

open Polynomial

private theorem linear_dvd {p q : ℕ} (hq : 0 < q) (hc : p.Coprime q)
    {P : ℤ[X]} (hr : P.eval₂ (Int.castRingHom ℚ) (-(p : ℚ) / q) = 0) :
    C (q : ℤ) * X + C (p : ℤ) ∣ P := by
  let L : ℤ[X] := C (q : ℤ) * X + C (p : ℤ)
  have prim : L.IsPrimitive := by
    apply isPrimitive_iff_isUnit_of_C_dvd.mpr
    intro r h
    have hcoeff := (C_dvd_iff_dvd_coeff _ _).mp h
    apply hc.isCoprime.isUnit_of_dvd'
    · simpa [L] using hcoeff 0
    · simpa [L] using hcoeff 1
  apply (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast L P prim).mpr
  have hfactor := dvd_iff_isRoot.mpr (show (P.map (Int.castRingHom ℚ)).IsRoot (-(p : ℚ) / q)
    by simpa [IsRoot, eval_map] using hr)
  obtain ⟨H, hH⟩ := hfactor
  have hQ : (q : ℚ) ≠ 0 := by positivity
  refine ⟨C (q : ℚ)⁻¹ * H, ?_⟩
  have hm : L.map (Int.castRingHom ℚ) = C (q : ℚ) * X + C (p : ℚ) := by simp [L]
  have hcancel : C (q : ℚ)⁻¹ * C (q : ℚ) = (1 : ℚ[X]) := by
    rw [← map_mul, inv_mul_cancel₀ hQ, map_one]
  have hs : C (q : ℚ)⁻¹ * (C (q : ℚ) * X + C (p : ℚ)) = X - C (-(p : ℚ) / q) := by
    calc
      _ = (C (q : ℚ)⁻¹ * C (q : ℚ)) * X + C ((q : ℚ)⁻¹ * p) := by rw [map_mul]; ring
      _ = _ := by rw [hcancel]; simp [div_eq_mul_inv, mul_comm]
  rw [hH, hm, ← hs]
  ring

private theorem graph_constraints {n p q : ℕ} (hq : 0 < q) (hc : p.Coprime q)
    (h : Occurs n (-(p : ℚ) / q)) :
    ∃ k : ℕ, n = (p + q) * k ∧ (Even n → Even k) := by
  classical
  obtain ⟨V, f, G, hV, hroot⟩ := h
  obtain ⟨H, hH⟩ := linear_dvd hq hc hroot
  have heval : (n : ℤ) = (p + q : ℤ) * H.eval 1 := by
    have h1 := congrArg (Polynomial.eval 1) hH
    simpa [degreePolynomial, eval_finsetSum, hV, add_comm] using h1
  have hpos : 0 < (p + q : ℤ) := by positivity
  have hnonneg : 0 ≤ H.eval 1 := by
    by_contra! hneg
    linarith [mul_neg_of_pos_of_neg hpos hneg]
  let k := (H.eval 1).toNat
  have hK : (k : ℤ) = H.eval 1 := Int.toNat_of_nonneg hnonneg
  rw [← hK] at heval
  have hn : n = (p + q) * k := by exact_mod_cast heval
  refine ⟨k, hn, ?_⟩
  intro en
  by_contra hk
  have es : Even (p + q) := by simpa [hn, Nat.even_mul, hk] using en
  have hd : 2 * (G.edgeFinset.card : ℤ) =
      (q : ℤ) * k + (p + q : ℤ) * H.derivative.eval 1 := by
    have d := congrArg (Polynomial.eval 1) (congrArg derivative hH)
    have dg : ∑ v, (G.degree v : ℤ) = 2 * (G.edgeFinset.card : ℤ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    simpa [degreePolynomial, derivative_sum, derivative_X_pow, eval_finsetSum,
      derivative_mul, ← hK, dg, add_comm, mul_comm] using d
  have ds : (2 : ℤ) ∣ (p + q : ℤ) := by exact_mod_cast es.two_dvd
  have dqk : (2 : ℤ) ∣ (q : ℤ) * k :=
    (dvd_add_left (ds.mul_right _)).mp (hd ▸ dvd_mul_right _ _)
  have nat_qk : 2 ∣ q * k := by exact_mod_cast dqk
  have eq : Even q := by simpa [← even_iff_two_dvd, Nat.even_mul, hk] using nat_qk
  have ep : Even p := by simpa [Nat.even_add, eq] using es
  have hcommon := Nat.dvd_gcd ep.two_dvd eq.two_dvd
  rw [hc.gcd_eq_one] at hcommon
  omega

/-- A matching with `a` isolated vertices and `t` edges. -/
private def matching (a t : ℕ) : SimpleGraph (Fin a ⊕ (Fin t × Bool)) where
  Adj
    | .inr (i, b), .inr (j, c) => i = j ∧ b ≠ c
    | _, _ => False
  symm.symm := by
    rintro (u | ⟨i,b⟩) (v | ⟨j,c⟩) h <;> try exact h.elim
    exact ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl := by rintro (u | ⟨i,b⟩) <;> simp

private theorem occurs_matching {a b : ℕ} (hb : Even b) {x : ℚ}
    (hroot : (a : ℚ) + b * x = 0) : Occurs (a + b) x := by
  classical
  obtain ⟨t, rfl⟩ := hb
  let G := matching a t
  have h0 (u : Fin a) : G.degree (.inl u) = 0 := by
    apply (G.degree_eq_zero _).mpr
    rintro (v | ⟨i,b⟩) <;> exact id
  have h1 (u : Fin t × Bool) : G.degree (.inr u) = 1 := by
    apply (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mpr
    obtain ⟨i,b⟩ := u
    refine ⟨.inr (i, !b), ?_, ?_⟩
    · change i = i ∧ b ≠ !b
      cases b <;> simp
    · rintro (v | ⟨j,c⟩) h
      · exact h.elim
      · obtain ⟨rfl, hc⟩ := h
        cases b <;> cases c <;> simp_all
  refine ⟨_, inferInstance, G, ?_, ?_⟩
  · simp [mul_two]
  · simpa [degreePolynomial, eval₂_finsetSum, Fintype.sum_sum_type, h0, h1,
      mul_two, add_mul] using hroot

private theorem occurs_inv {n : ℕ} {x : ℚ} (hx : x ≠ 0) (h : Occurs n x) :
    Occurs n x⁻¹ := by
  classical
  obtain ⟨V, f, G, hn, hz⟩ := h
  let _ : DecidableRel Gᶜ.Adj := fun _ _ => Classical.propDecidable _
  refine ⟨V, f, Gᶜ, hn, ?_⟩
  simp only [degreePolynomial, eval₂_finsetSum, eval₂_pow, eval₂_X] at hz ⊢
  have hpow (v : V) : x⁻¹ ^ Gᶜ.degree v =
      x⁻¹ ^ (Fintype.card V - 1) * x ^ G.degree v := by
    rw [G.degree_compl, pow_sub₀ _ (inv_ne_zero hx) (Nat.le_sub_one_of_lt (G.degree_lt_card_verts _))]
    simp
  calc
    _ = ∑ v, x⁻¹ ^ (Fintype.card V - 1) * x ^ G.degree v :=
      Finset.sum_congr rfl fun v _ => hpow v
    _ = _ := by rw [← Finset.mul_sum, hz, mul_zero]

/-- A reduced negative fraction occurs precisely at these graph orders. -/
public theorem classification {n p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hc : p.Coprime q) :
    Occurs n (-(p : ℚ) / q) ↔ ∃ k : ℕ, n = (p + q) * k ∧ (Even n → Even k) := by
  refine ⟨graph_constraints hq hc, ?_⟩
  rintro ⟨k, rfl, hk⟩
  have epq : Even (q * k) ∨ Even (p * k) := by
    by_cases eq : Even (q * k)
    · exact Or.inl eq
    · right
      by_contra ep
      simp only [Nat.even_mul, not_or] at eq ep
      have e : Even (p + q) := by simp [Nat.even_add, ep.1, eq.1]
      exact eq.2 (hk (e.mul_right _))
  rw [add_mul]
  obtain e | e := epq
  · apply occurs_matching e
    push_cast
    field_simp
    ring
  · have h : Occurs (q * k + p * k) (-(q : ℚ) / p) := by
      apply occurs_matching e
      push_cast
      field_simp
      ring
    have hinv := occurs_inv (div_ne_zero (neg_ne_zero.mpr (by positivity)) (by positivity)) h
    simpa [add_comm, div_neg, neg_div] using hinv

public theorem result : Conjecture := by
  intro n p q hq hc h
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have hq1 : q = 1 := by simpa using hc
    simp [hq1]
  · obtain ⟨k, hk, _⟩ := (classification hp hq hc).mp h
    exact ⟨k, hk⟩

/-- info: 'GeorgeRationalDegreeRoots.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

end GeorgeRationalDegreeRoots
