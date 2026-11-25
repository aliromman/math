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


end RestrictedUMinimum

namespace RestrictedUMinimum

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- Keep a rooted branch or cut its attachment and forget the root. -/
def plant (L : A →ₗ[K] K) (z : A) (t : K) : A →ₗ[K] A :=
  LinearMap.mulLeft K z + t • (Algebra.linearMap K A).comp L

theorem plant_apply (L : A →ₗ[K] K) (z : A) (t : K) (v : A) :
    plant L z t v = z * v + algebraMap K A (t * L v) := by
  simp [plant, Algebra.smul_def]

/-- The determinant is quadratic in the difference between the two branch types. -/
private theorem determinant_shift (f : A →ₗ[K] A) (u v D : A) (d : K) (h : u - v = d • D) :
    f (u ^ 2) * f (v ^ 2) - f (u * v) ^ 2 =
      algebraMap K A (d ^ 2) * (f (D ^ 2) * f (v ^ 2) - f (D * v) ^ 2) := by
  have hu : u = v + d • D := by rw [← h]; ring
  have hs : (v + d • D) ^ 2 = v ^ 2 + (2 * d) • (D * v) + d ^ 2 • D ^ 2 := by
    simp only [Algebra.smul_def, map_mul, map_ofNat, map_pow]
    ring
  have hm : (v + d • D) * v = v ^ 2 + d • (D * v) := by
    simp only [Algebra.smul_def]
    ring
  rw [hu, hs, hm]
  simp only [map_add, map_smul]
  simp only [Algebra.smul_def, map_mul, map_ofNat, map_pow]
  ring

/-- Interchanging the two branch types forces two branch differences and one hub cut. -/
theorem planted_determinant (L : A →ₗ[K] K) (z : A) (t d : K) (u v D : A)
    (h : u - v = d • D) :
    algebraMap K A (t * d ^ 2) ∣
      plant L z t (u ^ 2) * plant L z t (v ^ 2) - plant L z t (u * v) ^ 2 := by
  let e (a : A) := algebraMap K A (L a)
  refine ⟨z * (D ^ 2 * e (v ^ 2) + v ^ 2 * e (D ^ 2) - 2 * (D * v) * e (D * v)) +
    algebraMap K A t * (e (D ^ 2) * e (v ^ 2) - e (D * v) ^ 2), ?_⟩
  rw [determinant_shift _ u v D d h]
  simp only [plant_apply, map_mul, map_pow, e]
  ring

/-- A determinant with different branch pairs has one factor from each pair. -/
theorem mixed_determinant (L : A →ₗ[K] K) (a b c e E F : A) (d f : K)
    (ha : a - b = d • E) (hc : c - e = f • F) :
    d * f ∣ L (a * c) * L (b * e) - L (a * e) * L (b * c) := by
  have h₁ : a = b + d • E := by rw [← ha]; ring
  have h₂ : c = e + f • F := by rw [← hc]; ring
  refine ⟨L (E * F) * L (b * e) - L (E * e) * L (b * F), ?_⟩
  rw [h₁, h₂]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul,
    smul_eq_mul]
  ring

end RestrictedUMinimum

namespace RestrictedUMinimum

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

theorem witness_equal : SameRestrictedU 5 leftTree rightTree := by
  obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := branch_differences
  obtain ⟨q, hq⟩ := mixed_determinant closeRoot a.rootedU b.rootedU c.rootedU d.rootedU
    e f (t ^ 2) (t ^ 3) he hf
  have h : t ^ 6 ∣ leftTree.cutPolynomial - rightTree.cutPolynomial := by
    refine ⟨q, ?_⟩
    rw [leftTree, rightTree, cut_link, cut_link]
    simp only [Tree.cutPolynomial, Tree.rootedU.eq_3]
    rw [show a.rootedU * c.rootedU * (b.rootedU * d.rootedU) =
       a.rootedU * d.rootedU * (b.rootedU * c.rootedU) by ring]
    linear_combination t * hq
  intro j hj
  exact sub_eq_zero.mp <| by
    simpa only [Polynomial.coeff_sub] using (Polynomial.X_pow_dvd_iff.mp h j (by omega))

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
