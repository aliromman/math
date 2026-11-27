module

public import conjectures.RestrictedUMinimum.Solution
public import conjectures.RestrictedUMinimum.Ising
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace RestrictedUMinimum

/-- Put two pairs of branches on the two sides of a new root. -/
def nextPair (u v : Tree) : Tree × Tree :=
  ((u.merge u).plant.merge (v.merge v).plant, (u.merge v).plant.merge (u.merge v).plant)

def family : ℕ → Tree × Tree
  | 0 => (fork, path)
  | k + 1 => nextPair (family k).1 (family k).2

private def firstDegree : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * firstDegree k + 1

private theorem firstDegree_spec (k : ℕ) : firstDegree k + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [firstDegree, pow_succ _ (k + 1)]
    omega

/-- The two trees have order `(8 · 4^k + 1)/3`. -/
theorem family_order (k : ℕ) :
    (family k).1.order = (family k).2.order ∧ 3 * (family k).1.order = 8 * 4 ^ k + 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [family, nextPair, Tree.order, Tree.branchesSize, pow_succ] at ih ⊢
    omega

noncomputable section

private theorem family_difference (k : ℕ) :
    ∃ e : RootRing, (family k).1.rootedU - (family k).2.rootedU =
      (Polynomial.X : CutRing) ^ firstDegree k • e := by
  induction k with
  | zero =>
    obtain ⟨e, he, _⟩ := path_difference
    exact ⟨e, by simpa only [family, firstDegree, pow_one] using he⟩
  | succ k ih =>
    obtain ⟨e, he⟩ := ih
    let t : CutRing := Polynomial.X
    have hs : t * (t ^ firstDegree k) ^ 2 = t ^ firstDegree (k + 1) := by
      rw [firstDegree, pow_succ t (2 * firstDegree k), Nat.mul_comm 2, pow_mul, mul_comm]
    obtain ⟨f, hf⟩ := planted_determinant closeRoot Polynomial.X t (t ^ firstDegree k)
      (family k).1.rootedU (family k).2.rootedU e he
    refine ⟨f, ?_⟩
    simpa only [family, nextPair, Tree.rootedU.eq_3, rooted_plant, ← pow_two, Algebra.smul_def,
      hs, t] using hf

/-- The cut polynomials agree through `2^(k+1)−2` cuts. -/
theorem family_equal (k : ℕ) :
    SameRestrictedU (2 ^ (k + 1) - 2) (family k).1 (family k).2 := by
  obtain ⟨e, he⟩ := family_difference k
  have hd : (Polynomial.X : CutRing) ^ firstDegree k ∣
      (family k).1.cutPolynomial - (family k).2.cutPolynomial := by
    refine ⟨closeRoot e, ?_⟩
    change closeRoot _ - closeRoot _ = _
    rw [← map_sub, he, map_smul, smul_eq_mul]
  have hs := firstDegree_spec k
  have hp : 1 ≤ firstDegree k := by cases k <;> simp [firstDegree]
  intro j hj
  exact sub_eq_zero.mp <| by
    simpa only [Polynomial.coeff_sub] using Polynomial.X_pow_dvd_iff.mp hd j (by omega)

end

private def boundedSpin (x : ℤ × ℤ) : Prop := 0 < x.1 ∧ 0 < x.2 ∧ x.2 < 4 * x.1

private def detSpin (x y : ℤ × ℤ) : ℤ := x.1 * y.2 - y.1 * x.2

private def spinTotal (x : ℤ × ℤ) : ℤ := 17 * x.1 + x.2

private def productSpin (a b c d : ℤ) : ℤ × ℤ :=
  ((17 * a + 2 * b) * (17 * c + 2 * d), (34 * a + b) * (34 * c + d))

private theorem productSpin_bounded {a b c d : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : boundedSpin (productSpin a b c d) := by
  refine ⟨by dsimp [productSpin]; positivity, by dsimp [productSpin]; positivity, ?_⟩
  change (34 * a + b) * (34 * c + d) < 4 * ((17 * a + 2 * b) * (17 * c + 2 * d))
  calc
    _ < (2 * (17 * a + 2 * b)) * (34 * c + d) :=
      mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ < (2 * (17 * a + 2 * b)) * (2 * (17 * c + 2 * d)) :=
      mul_lt_mul_of_pos_left (by omega) (by positivity)
    _ = _ := by ring

private def separated (u v : Tree) : Prop :=
  boundedSpin u.spin ∧ boundedSpin v.spin ∧ detSpin u.spin v.spin ≠ 0

private theorem separated_next {u v : Tree} (h : separated u v) :
    separated (nextPair u v).1 (nextPair u v).2 ∧
    spinTotal (nextPair u v).1.spin ≠ spinTotal (nextPair u v).2.spin := by
  let a := u.spin.1
  let b := u.spin.2
  let c := v.spin.1
  let d := v.spin.2
  let f := productSpin (a * a) (b * b) (c * c) (d * d)
  let g := productSpin (a * c) (b * d) (a * c) (b * d)
  rcases h with ⟨⟨ha, hb, hab⟩, ⟨hc, hd, hcd⟩, hdet⟩
  change 0 < a at ha
  change 0 < b at hb
  change 0 < c at hc
  change 0 < d at hd
  change b < 4 * a at hab
  change d < 4 * c at hcd
  change a * d - c * b ≠ 0 at hdet
  have shift_pos : 0 < 34 * (a * d - c * b) ^ 2 := by
    exact mul_pos (by decide) (sq_pos_of_ne_zero hdet)
  have h₁ : f.1 - g.1 = 34 * (a * d - c * b) ^ 2 := by dsimp [f, g, productSpin]; ring
  have h₂ : f.2 - g.2 = 34 * (a * d - c * b) ^ 2 := by dsimp [f, g, productSpin]; ring
  have hbnd : b * d < (4 * a) * (4 * c) :=
    (mul_lt_mul_of_pos_right hab hd).trans (mul_lt_mul_of_pos_left hcd (by positivity))
  have hgap : 0 < g.2 - g.1 := by
    have hfactor : g.2 - g.1 = (17 * (a * c) - b * d) * (51 * (a * c) + 3 * (b * d)) := by
      dsimp [g, productSpin]
      ring
    rw [hfactor]
    exact mul_pos (by nlinarith only [hbnd, mul_pos ha hc]) (by positivity)
  have hf_det : detSpin f g = 34 * (a * d - c * b) ^ 2 * (g.2 - g.1) := by
    unfold detSpin
    linear_combination g.2 * h₁ - g.1 * h₂
  change (boundedSpin f ∧ boundedSpin g ∧ detSpin f g ≠ 0) ∧ spinTotal f ≠ spinTotal g
  refine ⟨⟨productSpin_bounded (mul_pos ha ha) (mul_pos hb hb) (mul_pos hc hc) (mul_pos hd hd),
    productSpin_bounded (mul_pos ha hc) (mul_pos hb hd) (mul_pos ha hc) (mul_pos hb hd), ?_⟩, ?_⟩
  · rw [hf_det]
    exact (mul_pos shift_pos hgap).ne'
  · unfold spinTotal
    omega

private theorem family_separated (k : ℕ) : separated (family k).1 (family k).2 := by
  induction k with
  | zero =>
    norm_num [family, fork, path, Tree.spin, boundedSpin, detSpin, separated]
  | succ k ih => exact (separated_next ih).1

/-- From the first iteration on, the unrooted Ising partition functions differ. -/
theorem family_spin_totals_ne (k : ℕ) :
    17 * (family (k + 1)).1.spin.1 + (family (k + 1)).1.spin.2 ≠
      17 * (family (k + 1)).2.spin.1 + (family (k + 1)).2.spin.2 :=
  (separated_next (family_separated k)).2

theorem family_noniso (k : ℕ) : ¬ (family (k + 1)).1.iso (family (k + 1)).2 :=
  fun h => family_spin_totals_ne k (Tree.spin_iso h)

/-- Every cut index from one onward has a pair of order at most `3(m+1)²`. -/
theorem quadratic_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ u v : Tree, u.order = v.order ∧ ¬ u.iso v ∧ SameRestrictedU m u v ∧
      u.order ≤ 3 * (m + 1) ^ 2 := by
  let k := (m + 1).log2
  have hk : 1 ≤ k := (Nat.le_log2 (by omega)).mpr (by omega)
  have hlo : 2 ^ k ≤ m + 1 := Nat.log2_self_le (by omega)
  have hhi : m + 1 < 2 ^ (k + 1) := Nat.lt_log2_self
  obtain ⟨hord, hsize⟩ := family_order k
  refine ⟨(family k).1, (family k).2, hord, ?_, ?_, ?_⟩
  · rw [show k = (k - 1) + 1 by omega]
    exact family_noniso _
  · exact fun j hj => family_equal k j (by omega)
  · have hs : 4 ^ k ≤ (m + 1) ^ 2 := calc
      _ = (2 ^ k) ^ 2 := by
        rw [← pow_mul, mul_comm k 2, pow_mul]
        rfl
      _ ≤ (m + 1) ^ 2 := pow_le_pow_left' hlo 2
    have hpos : 0 < (m + 1) ^ 2 := by positivity
    omega

/-- info: 'RestrictedUMinimum.quadratic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadratic_bound

end RestrictedUMinimum
