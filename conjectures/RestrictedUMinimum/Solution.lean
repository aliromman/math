module

public import conjectures.RestrictedUMinimum.Statement
public import Mathlib.Algebra.Algebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RestrictedUMinimum

/-- The three-vertex path rooted at its middle vertex. -/
def fork : Tree := Tree.point.plant.merge Tree.point.plant

/-- The three-vertex path rooted at an end. -/
def path : Tree := Tree.point.plant.plant

def a : Tree := fork.link path
def b : Tree := path.link fork
def c : Tree := (fork.merge fork).plant.merge (path.merge path).plant
def d : Tree := (fork.merge path).plant.merge (fork.merge path).plant

/-- The left end of the central edge carries branches from `a` and `c`. -/
def leftTree : Tree := (a.merge c).link (b.merge d)

/-- Exchange the two eleven-vertex pieces at the ends of the central edge. -/
def rightTree : Tree := (a.merge d).link (b.merge c)

theorem witness_order : leftTree.order = 32 ∧ rightTree.order = 32 := by decide

private def adjacentSixFour {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ x, G.degree x = 6 ∧ ∃ y, G.Adj x y ∧ G.degree y = 4

private instance {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Decidable (adjacentSixFour G) := by unfold adjacentSixFour; infer_instance

private theorem adjacentSixFour_map {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ≃g H) : adjacentSixFour G → adjacentSixFour H := by
  rintro ⟨x, hx, y, hxy, hy⟩
  exact ⟨f x, (f.degree_eq x).trans hx, f y, f.map_adj_iff.mpr hxy, (f.degree_eq y).trans hy⟩

/-- Only the right tree has an edge whose endpoints have degrees six and four. -/
theorem witness_noniso : ¬ leftTree.iso rightTree := by
  rintro ⟨f⟩
  have hleft : ¬ adjacentSixFour leftTree.graph := by decide +kernel
  have hright : adjacentSixFour rightTree.graph := by decide +kernel
  exact hleft (adjacentSixFour_map f.symm hright)

section

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- Keep a rooted branch or cut its attachment and forget the root. -/
def plant (L : A →ₗ[K] K) (z : A) (t : K) : A →ₗ[K] A :=
  LinearMap.mulLeft K z + t • (Algebra.linearMap K A).comp L

theorem plant_apply (L : A →ₗ[K] K) (z : A) (t : K) (v : A) :
    plant L z t v = z * v + algebraMap K A (t * L v) := by
  simp [plant, Algebra.smul_def]

/-- Linearity supplies one factor from each exchanged pair of branches. -/
private theorem determinant_shift {B : Type*} [CommRing B] [Algebra K B] (L : A →ₗ[K] B)
    (a b c e E F : A) (d f : K) (ha : a - b = d • E) (hc : c - e = f • F) :
    L (a * c) * L (b * e) - L (a * e) * L (b * c) =
      (d * f) • (L (E * F) * L (b * e) - L (E * e) * L (b * F)) := by
  have h₁ : a = b + d • E := by rw [← ha]; ring
  have h₂ : c = e + f • F := by rw [← hc]; ring
  rw [h₁, h₂]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul]
  simp only [Algebra.smul_def, map_mul]
  ring

/-- Keeping both attachments cancels, so their exchange supplies an extra cut factor. -/
theorem planted_exchange (L : A →ₗ[K] K) (z : A) (t d f : K) (a b c e E F : A)
    (ha : a - b = d • E) (hc : c - e = f • F) :
    ∃ w, plant L z t (a*c) * plant L z t (b*e) - plant L z t (a*e) * plant L z t (b*c) =
      (d * f * t) • w := by
  let C (x : A) := algebraMap K A (L x)
  refine ⟨z * (E * F * C (b * e) + b * e * C (E * F) -
    E * e * C (b * F) - b * F * C (E * e)) +
    algebraMap K A t * (C (E * F) * C (b * e) - C (E * e) * C (b * F)), ?_⟩
  rw [determinant_shift _ a b c e E F d f ha hc]
  simp only [plant_apply, Algebra.smul_def, map_mul, C]
  ring

theorem planted_determinant (L : A →ₗ[K] K) (z : A) (t d : K) (u v D : A)
    (h : u - v = d • D) :
    algebraMap K A (t * d ^ 2) ∣
      plant L z t (u ^ 2) * plant L z t (v ^ 2) - plant L z t (u * v) ^ 2 := by
  obtain ⟨w, hw⟩ := planted_exchange L z t d d u v u v D D h h
  refine ⟨w, ?_⟩
  simpa only [pow_two, mul_comm v u, mul_comm t (d * d), Algebra.smul_def] using hw

end

noncomputable section

abbrev t : CutRing := Polynomial.X
abbrev z : RootRing := Polynomial.X

theorem rooted_plant (u : Tree) :
    u.plant.rootedU = plant closeRoot z t u.rootedU := by
  rw [plant_apply]
  rfl

/-- The common contribution from keeping the joining edge cancels. -/
private theorem link_difference (u v : Tree) :
    (u.link v).rootedU - (v.link u).rootedU =
      t • (v.cutPolynomial • u.rootedU - u.cutPolynomial • v.rootedU) := by
  simp only [Tree.rootedU, Tree.cutPolynomial, Algebra.smul_def,
    Polynomial.algebraMap_eq, map_mul]
  ring

private theorem link_same_closed (u v : Tree) :
    (u.link v).cutPolynomial = (v.link u).cutPolynomial := by
  apply sub_eq_zero.mp
  change closeRoot _ - closeRoot _ = 0
  rw [← map_sub, link_difference, map_smul, map_sub, map_smul, map_smul]
  change t * (v.cutPolynomial * u.cutPolynomial - u.cutPolynomial * v.cutPolynomial) = 0
  ring

theorem path_difference :
    ∃ e : RootRing, fork.rootedU - path.rootedU = t • e ∧
      fork.cutPolynomial = path.cutPolynomial := by
  let edge := Tree.point.plant
  have h₁ : (edge.link Tree.point).rootedU = fork.rootedU := rfl
  have h₂ : (Tree.point.link edge).rootedU = path.rootedU := by
    change 1 * path.rootedU = path.rootedU
    exact one_mul _
  refine ⟨Tree.point.cutPolynomial • edge.rootedU - edge.cutPolynomial • Tree.point.rootedU,
    ?_, ?_⟩
  · rw [← h₁, ← h₂]
    exact link_difference _ _
  · simpa only [Tree.cutPolynomial, h₁, h₂] using link_same_closed edge Tree.point

theorem branch_differences :
    (∃ e : RootRing, a.rootedU - b.rootedU = t ^ 2 • e) ∧
    (∃ f : RootRing, c.rootedU - d.rootedU = t ^ 3 • f) := by
  obtain ⟨e, he, hU⟩ := path_difference
  constructor
  · refine ⟨path.cutPolynomial • e, ?_⟩
    change (fork.link path).rootedU - (path.link fork).rootedU = _
    rw [link_difference, hU, ← smul_sub path.cutPolynomial fork.rootedU path.rootedU,
      he, smul_comm path.cutPolynomial t,
      smul_smul, pow_two]
  · obtain ⟨f, hf⟩ := planted_determinant closeRoot z t t
      fork.rootedU path.rootedU e he
    refine ⟨f, ?_⟩
    simpa only [c, d, Tree.rootedU.eq_3, rooted_plant, ← pow_two, Algebra.smul_def,
      show t * t ^ 2 = t ^ 3 by ring] using hf

theorem cut_link (u v : Tree) :
    (u.link v).cutPolynomial =
      closeRoot (z * (u.rootedU * v.rootedU)) + t * (u.cutPolynomial * v.cutPolynomial) := by
  change closeRoot (u.rootedU * (z * v.rootedU + Polynomial.C (t * v.cutPolynomial))) = _
  have h : u.rootedU * Polynomial.C (t * v.cutPolynomial) =
      (t * v.cutPolynomial) • u.rootedU := by
    simpa only [Algebra.smul_def, Polynomial.algebraMap_eq] using
      (mul_comm u.rootedU (Polynomial.C (t * v.cutPolynomial)))
  rw [mul_add, h, map_add, map_smul, smul_eq_mul,
    show u.rootedU * (z * v.rootedU) = z * (u.rootedU * v.rootedU) by ring]
  change _ + (t * v.cutPolynomial) * u.cutPolynomial = _
  ring

def joined (p q : (Tree × Tree)) : (Tree × Tree) :=
  ((p.1.merge q.1).link (p.2.merge q.2), (p.1.merge q.2).link (p.2.merge q.1))

def RootMatch (i : ℕ) (p : (Tree × Tree)) : Prop :=
  ∃ e : RootRing, p.1.rootedU - p.2.rootedU = t ^ i • e

theorem joined_equal {i j : ℕ} {p q : Tree × Tree} (hp : RootMatch i p)
    (hq : RootMatch j q) : SameRestrictedU (i + j) (joined p q).1 (joined p q).2 := by
  obtain ⟨e, he⟩ := hp
  obtain ⟨f, hf⟩ := hq
  have hw := determinant_shift closeRoot p.1.rootedU p.2.rootedU q.1.rootedU q.2.rootedU
    e f (t ^ i) (t ^ j) he hf
  have hd : t ^ (i + j + 1) ∣ (joined p q).1.cutPolynomial - (joined p q).2.cutPolynomial := by
    refine ⟨closeRoot (e * f) * closeRoot (p.2.rootedU * q.2.rootedU) -
      closeRoot (e * q.2.rootedU) * closeRoot (p.2.rootedU * f), ?_⟩
    change ((p.1.merge q.1).link (p.2.merge q.2)).cutPolynomial -
      ((p.1.merge q.2).link (p.2.merge q.1)).cutPolynomial = _
    rw [cut_link, cut_link]
    simp only [Tree.cutPolynomial, Tree.rootedU.eq_3, pow_succ, pow_add]
    rw [show p.1.rootedU * q.1.rootedU * (p.2.rootedU * q.2.rootedU) =
      p.1.rootedU * q.2.rootedU * (p.2.rootedU * q.1.rootedU) by ring]
    rw [smul_eq_mul] at hw
    linear_combination t * hw
  intro k hk
  exact sub_eq_zero.mp <| by
    simpa only [Polynomial.coeff_sub] using Polynomial.X_pow_dvd_iff.mp hd k (by omega)

theorem witness_equal : SameRestrictedU 5 leftTree rightTree :=
  joined_equal (p := (a,b)) (q := (c,d)) (i := 2) (j := 3) branch_differences.1 branch_differences.2

/-- These two trees on 32 vertices disprove the proposed minimum of 34. -/
theorem counterexample : ¬ Conjecture := by
  intro h
  have hmin := (h 5 (by decide)).2
    ⟨leftTree, rightTree, witness_order.1, witness_order.2, witness_noniso, witness_equal⟩
  have hn : predictedOrder 5 = 34 := by decide
  omega

/-- info: 'RestrictedUMinimum.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample

end
end RestrictedUMinimum
