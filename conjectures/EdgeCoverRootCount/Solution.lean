module

public import conjectures.EdgeCoverRootCount.Statement
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Abel

open scoped Classical Polynomial
open Polynomial

namespace EdgeCoverRootCount

/-- A repeated root of `p` contributes all but one of its copies to the auxiliary polynomial. -/
private theorem repeated_roots (p q : ℂ[X]) (m : ℕ) (hq : q ≠ 0)
    (h : q = (X + 1) * p.derivative - C (m : ℂ) * p) :
    p.natDegree ≤ q.natDegree + p.roots.toFinset.card := by
  classical
  have hroots : p.roots ≤ q.roots + p.roots.dedup := by
    apply Multiset.le_iff_count.mpr
    intro a
    by_cases ha : a ∈ p.roots
    · have hdiv := p.pow_rootMultiplicity_dvd a
      have hqdiv : (X - C a) ^ (p.rootMultiplicity a - 1) ∣ q := by
        rw [h]
        apply dvd_sub
        · exact dvd_mul_of_dvd_right (pow_sub_one_dvd_derivative_of_pow_dvd hdiv) _
        · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (Nat.sub_le _ _)).trans hdiv) _
      have hr := (le_rootMultiplicity_iff hq).2 hqdiv
      simp only [Multiset.count_add, count_roots]
      have hone : p.roots.dedup.count a = 1 := by simp [ha]
      omega
    · simp [Multiset.count_eq_zero.mpr ha]
  have hcard := Multiset.card_le_card hroots
  simpa only [Multiset.card_add, IsAlgClosed.card_roots_eq_natDegree, Multiset.card_toFinset] using hcard

private theorem differential_bound (p b : ℂ[X]) (m : ℕ)
    (hid : p + b = (X + 1) ^ m) (hb : b.natDegree < m) (hr : p.IsRoot 0) :
    m ≤ b.natDegree + p.roots.toFinset.card := by
  classical
  have hp : p = (X + 1) ^ m - b := eq_sub_of_add_eq hid
  have hmon : ((X + 1 : ℂ[X]) ^ m).natDegree = m := by simp
  have hdeg : p.natDegree = m := by
    have hlt : b.natDegree < ((X + 1 : ℂ[X]) ^ m).natDegree := by rwa [hmon]
    rw [hp, natDegree_sub_eq_left_of_natDegree_lt hlt, hmon]
  have hp0 : p ≠ 0 := by intro hpz; simp [hpz] at hdeg; omega
  let q : ℂ[X] := (X + 1) * p.derivative - C (m : ℂ) * p
  have hq : q ≠ 0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    have hdiv : p ∣ p.derivative * (X + 1) := by
      rw [mul_comm, he]
      exact dvd_mul_left _ _
    have hbad := isRoot_of_isRoot_of_dvd_derivative_mul hp0 hdiv hr
    simp at hbad
  have hbase : (X + 1 : ℂ[X]) * derivative ((X + 1) ^ m) = C (m : ℂ) * (X + 1) ^ m := by
    cases m with
    | zero => simp
    | succ n =>
      rw [derivative_pow_succ, pow_succ]
      simp [mul_comm, mul_left_comm]
  have hqb : q = C (m : ℂ) * b - (X + 1) * b.derivative := by
    dsimp [q]
    rw [hp, derivative_sub, mul_sub, mul_sub, hbase]
    abel
  have hbd : ((X + 1 : ℂ[X]) * b.derivative).natDegree ≤ b.natDegree := by
    by_cases hzero : b.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hzero, derivative_C, mul_zero, natDegree_zero]
      exact Nat.zero_le _
    · apply (natDegree_mul_le).trans
      have hd := natDegree_derivative_lt hzero
      simpa using (show 1 + b.derivative.natDegree ≤ b.natDegree by omega)
  have hqdeg : q.natDegree ≤ b.natDegree := by
    rw [hqb]
    exact (natDegree_sub_le ..).trans (max_le (natDegree_C_mul_le _ _) hbd)
  have hfinal := repeated_roots p q m hq rfl
  omega

public theorem resolution : Conjecture := by
  classical
  intro n G
  by_cases hδ : G.minDegree = 0
  · simp [hδ]
  have hpos : 0 < G.minDegree := Nat.pos_of_ne_zero hδ
  have : Nonempty (Fin n) := by
    by_contra! h
    exact hδ (by simp)
  let E := G.edgeFinset
  let T := E.powerset.filter (fun s => ¬ Covers s)
  let b : ℂ[X] := ∑ s ∈ T, X ^ s.card
  have hid : edgeCoverPolynomial G + b = (X + 1) ^ E.card := by
    dsimp [edgeCoverPolynomial, b, T, E]
    rw [Finset.sum_filter_add_sum_filter_not]
    simpa using (Finset.prod_add_one (f := fun _ : Sym2 (Fin n) => (X : ℂ[X])) G.edgeFinset).symm
  have hb : b.natDegree ≤ E.card - G.minDegree := by
    apply natDegree_sum_le_of_forall_le
    intro s hs
    obtain ⟨hsE, hmiss⟩ := Finset.mem_filter.mp hs
    obtain ⟨v, hv⟩ := Classical.not_forall.mp hmiss
    have hsub : s ⊆ E \ G.incidenceFinset v := by
      intro e he
      have heE := Finset.mem_powerset.mp hsE he
      exact Finset.mem_sdiff.mpr ⟨heE, fun h => hv ⟨e, he, (SimpleGraph.mem_incidenceFinset.mp h).2⟩⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (G.incidenceFinset_subset v), G.card_incidenceFinset_eq_degree] at hc
    simp only [natDegree_X_pow]
    exact hc.trans (Nat.sub_le_sub_left (G.minDegree_le_degree v) _)
  obtain ⟨v⟩ := ‹Nonempty (Fin n)›
  have hδm : G.minDegree ≤ E.card := (G.minDegree_le_degree v).trans (G.degree_le_card_edgeFinset v)
  have hr : (edgeCoverPolynomial G).IsRoot 0 := by
    simp only [IsRoot.def, edgeCoverPolynomial, eval_finsetSum, eval_pow, eval_X]
    apply Finset.sum_eq_zero
    intro s hs
    obtain ⟨e, he, _⟩ := (Finset.mem_filter.mp hs).2 v
    exact zero_pow ((Finset.card_pos.mpr ⟨e, he⟩).ne')
  have h := differential_bound _ b E.card hid (by omega) hr
  omega

/-- info: 'EdgeCoverRootCount.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end EdgeCoverRootCount
