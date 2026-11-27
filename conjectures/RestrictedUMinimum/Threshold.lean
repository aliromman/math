module

public import conjectures.RestrictedUMinimum.Growth
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace RestrictedUMinimum

private abbrev Pair := Tree × Tree

private def attached (p q : Pair) : Pair :=
  ((p.1.merge q.1).plant.merge (p.2.merge q.2).plant,
    (p.1.merge q.2).plant.merge (p.2.merge q.1).plant)

/-- A cut at one of the attachments is needed to see how the four branches were paired. -/
private theorem attached_match {i j : ℕ} {p q : Pair} (hp : RootMatch i p)
    (hq : RootMatch j q) : RootMatch (i + j + 1) (attached p q) := by
  obtain ⟨e, he⟩ := hp
  obtain ⟨f, hf⟩ := hq
  obtain ⟨w, hw⟩ := planted_exchange closeRoot z t (t ^ i) (t ^ j)
    p.1.rootedU p.2.rootedU q.1.rootedU q.2.rootedU e f he hf
  refine ⟨w, ?_⟩
  simpa only [attached, Tree.rootedU.eq_3, rooted_plant, pow_succ, pow_add] using hw

private def Below (m : ℕ) : Prop :=
  ∃ u v : Tree, u.order = v.order ∧ ¬ u.iso v ∧ SameRestrictedU m u v ∧
    u.order < predictedOrder m

private def total (u : Tree) : ℤ := 17 * u.spin.1 + u.spin.2

private theorem below_joined {i j : ℕ} {p q : Pair} (hp : RootMatch i p) (hq : RootMatch j q)
    (ho : (joined p q).1.order = (joined p q).2.order)
    (hn : (joined p q).1.order < predictedOrder (i + j))
    (hz : total (joined p q).1 ≠ total (joined p q).2) : Below (i + j) :=
  ⟨_, _, ho, fun h => hz (Tree.spin_iso h), joined_equal hp hq, hn⟩

private theorem small_indices (m : ℕ) (hm : 5 ≤ m) (hn : m ≤ 9) : Below m := by
  have h₁ : RootMatch 1 (fork, path) := by
    obtain ⟨e, he, _⟩ := path_difference
    exact ⟨e, by simpa only [pow_one] using he⟩
  have h₂ : RootMatch 2 (a, b) := branch_differences.1
  have h₃ : RootMatch 3 (c, d) := branch_differences.2
  have h₄ := attached_match h₁ h₂
  have h₅ := attached_match h₂ h₂
  interval_cases m
  · exact ⟨_, _, witness_order.1.trans witness_order.2.symm, witness_noniso, witness_equal,
      by decide⟩
  · exact below_joined h₃ h₃ (by decide) (by decide) (by decide +kernel)
  · exact below_joined h₃ h₄ (by decide) (by decide) (by decide +kernel)
  · exact below_joined h₄ h₄ (by decide) (by decide) (by decide +kernel)
  · exact below_joined h₄ h₅ (by decide) (by decide) (by decide +kernel)

private theorem predicted_step (m : ℕ) (hm : 2 ≤ m) :
    predictedOrder (m + 2) = 2 * predictedOrder m + 2 := by
  have hpar : Even (m + 2) ↔ Even m := by simp only [Nat.even_iff]; omega
  have hd : (m + 2) / 2 = m / 2 + 1 := by omega
  by_cases h : Even m
  · simp only [predictedOrder, hpar, h, ite_true, hd, pow_succ]
    have : 0 < 2 ^ (m / 2) := Nat.pow_pos (by decide)
    omega
  · have he : m / 2 + 1 - 1 = (m / 2 - 1) + 1 := by omega
    simp only [predictedOrder, hpar, h, ite_false, hd, he, pow_succ]
    have : 0 < 2 ^ (m / 2 - 1) := Nat.pow_pos (by decide)
    omega

private theorem quadratic_lt_predicted (m : ℕ) (hm : 14 ≤ m) :
    3 * (m + 1) ^ 2 < predictedOrder m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hb : m ≤ 15
    · interval_cases m <;> decide
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hi := ih k (by omega) (by omega)
    rw [predicted_step k (by omega)]
    have hk := Nat.mul_le_mul_right k (show 4 ≤ k by omega)
    nlinarith

/-- The proposed minimum exceeds the order of a counterexample at every index from five on. -/
theorem pointwise_counterexample (m : ℕ) (hm : 5 ≤ m) :
    ∃ u v : Tree, u.order = v.order ∧ ¬ u.iso v ∧ SameRestrictedU m u v ∧
      u.order < predictedOrder m := by
  by_cases hsmall : m ≤ 9
  · exact small_indices m hm hsmall
  by_cases hmid : m ≤ 13
  · refine ⟨(family 3).1, (family 3).2, (family_order 3).1, family_noniso 2,
      fun j hj => family_equal 3 j (by omega), ?_⟩
    have hlow : 10 ≤ m := by omega
    interval_cases m <;> decide
  obtain ⟨u, v, ho, hi, he, hn⟩ := quadratic_bound m (by omega)
  exact ⟨u, v, ho, hi, he, hn.trans_lt (quadratic_lt_predicted m (by omega))⟩

/-- info: 'RestrictedUMinimum.pointwise_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pointwise_counterexample

end RestrictedUMinimum
