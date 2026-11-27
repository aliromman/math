module

public import conjectures.RestrictedUMinimum.Statement
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

@[expose] public section

namespace RestrictedUMinimum.Tree

/-- A Boolean choice for each edge. True means cut. -/
def CutMask : Tree → Type
  | .point => Unit
  | .plant t => Bool × t.CutMask
  | .merge a b => a.CutMask × b.CutMask

instance maskFintype : (t : Tree) → Fintype t.CutMask
  | .point => inferInstanceAs (Fintype Unit)
  | .plant t => @instFintypeProd _ _ inferInstance (maskFintype t)
  | .merge a b => @instFintypeProd _ _ (maskFintype a) (maskFintype b)

theorem edges_length : (t : Tree) → t.edges.length = t.branchesSize
  | .point => rfl
  | .plant t => by simp [edges, branchesSize, edges_length t]
  | .merge a b => by simp [edges, branchesSize, edges_length a, edges_length b]

def maskEquiv : (t : Tree) → t.CutMask ≃ (Fin t.branchesSize → Bool)
  | .point => Equiv.ofUnique Unit (Fin 0 → Bool)
  | .plant t => (Equiv.prodCongr (Equiv.refl _) (maskEquiv t)).trans (Fin.consEquiv fun _ : Fin (t.branchesSize + 1) => Bool)
  | .merge a b => (Equiv.prodCongr (maskEquiv a) (maskEquiv b)).trans (Fin.appendEquiv _ _)

/-- Mask positions follow the list of actual edges, with the new root edge first. -/
def maskEquivEdges (t : Tree) : t.CutMask ≃ (Fin t.edges.length → Bool) :=
  (maskEquiv t).trans (Equiv.arrowCongr (finCongr (edges_length t).symm) (Equiv.refl _))

/-- The root component and the components detached by an edge cut. -/
structure CutForest where
  root : Tree
  detached : List Tree

/-- Construct the components that remain after the chosen edges are cut. -/
def cutForest : (t : Tree) → t.CutMask → CutForest
  | .point, _ => ⟨.point, []⟩
  | .plant t, (false, m) => let f := cutForest t m; ⟨f.root.plant, f.detached⟩
  | .plant t, (true, m) => let f := cutForest t m; ⟨.point, f.root :: f.detached⟩
  | .merge a b, (m, n) =>
    let f := cutForest a m
    let g := cutForest b n
    ⟨f.root.merge g.root, f.detached ++ g.detached⟩

/-- Count the selected edges in a mask. -/
def cutCount : (t : Tree) → t.CutMask → ℕ
  | .point, _ => 0
  | .plant t, (cut, m) => t.cutCount m + cut.toNat
  | .merge a b, (m, n) => a.cutCount m + b.cutCount n

theorem detached_length : (t : Tree) → (m : t.CutMask) →
    (t.cutForest m).detached.length = t.cutCount m
  | .point, _ => rfl
  | .plant t, (false, m) => detached_length t m
  | .plant t, (true, m) => congrArg (· + 1) (detached_length t m)
  | .merge a b, (m, n) => by simp [cutForest, cutCount, detached_length a m, detached_length b n]

noncomputable section

def parts (l : List Tree) : MvPolynomial ℕ ℤ := (l.map fun v => MvPolynomial.X v.order).prod

def weight (l : List Tree) : CutRing :=
  Polynomial.X ^ l.length * Polynomial.C (parts l)

def CutForest.rootedTerm (f : CutForest) : RootRing :=
  Polynomial.C (weight f.detached) * Polynomial.X ^ f.root.branchesSize

/-- One cut marker for each detached component and one variable for each component order. -/
def CutForest.term (f : CutForest) : CutRing :=
  Polynomial.X ^ f.detached.length * Polynomial.C (parts (f.root :: f.detached))

private theorem close_monomial (c : CutRing) (n : ℕ) :
    closeRoot (Polynomial.C c * Polynomial.X ^ n) = c * Polynomial.C (MvPolynomial.X (n + 1)) := by
  rw [Polynomial.C_mul_X_pow_eq_monomial, closeRoot, Polynomial.lsum_apply]
  simp [Polynomial.sum_monomial_index]

private theorem close_rootedTerm (f : CutForest) : closeRoot f.rootedTerm = f.term := by
  rw [CutForest.rootedTerm, close_monomial]
  simp only [weight, CutForest.term, parts, List.map_cons,
    List.prod_cons, map_mul, order]
  ring

private theorem rooted_keep (f : CutForest) :
    (CutForest.mk f.root.plant f.detached).rootedTerm = Polynomial.X * f.rootedTerm := by
  simp only [CutForest.rootedTerm, branchesSize, pow_succ]
  ring

private theorem rooted_cut (f : CutForest) :
    (CutForest.mk .point (f.root :: f.detached)).rootedTerm = Polynomial.C (Polynomial.X * f.term) := by
  simp only [CutForest.rootedTerm, branchesSize, pow_zero, mul_one, weight, CutForest.term,
    List.length_cons, pow_succ, map_mul]
  ring

private theorem rooted_merge (f g : CutForest) :
    (CutForest.mk (f.root.merge g.root) (f.detached ++ g.detached)).rootedTerm =
      f.rootedTerm * g.rootedTerm := by
  simp only [CutForest.rootedTerm, branchesSize, pow_add, weight, parts, List.length_append,
    List.map_append, List.prod_append, map_mul]
  ring

/-- The rooted polynomial is the sum over all edge masks of the resulting forest terms. -/
theorem rootedU_eq_sum_cuts : (t : Tree) → t.rootedU = ∑ m : t.CutMask, (t.cutForest m).rootedTerm
  | .point => by
    change (1 : RootRing) = ∑ _ : Unit, _
    simp [cutForest, CutForest.rootedTerm, branchesSize, weight, parts]
  | .plant t => by
    change _ = ∑ p : Bool × t.CutMask, _
    rw [rootedU, rootedU_eq_sum_cuts t, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, cutForest, rooted_keep, rooted_cut, map_sum, Finset.mul_sum,
      close_rootedTerm]
    exact add_comm _ _
  | .merge a b => by
    change _ = ∑ p : a.CutMask × b.CutMask, _
    rw [rootedU, rootedU_eq_sum_cuts a, rootedU_eq_sum_cuts b, Fintype.sum_prod_type,
      Finset.sum_mul_sum]
    simp only [cutForest, rooted_merge]

/-- This is the unrooted cut-state sum, with multiplicities from distinct edge masks. -/
theorem cutPolynomial_eq_sum_cuts (t : Tree) :
    t.cutPolynomial = ∑ m : t.CutMask, (t.cutForest m).term := by
  rw [cutPolynomial, rootedU_eq_sum_cuts, map_sum]
  simp only [close_rootedTerm]

/-- The coefficient at j sums the component partitions of exactly the j-edge cuts. -/
theorem cutPolynomial_coeff (t : Tree) (j : ℕ) :
    t.cutPolynomial.coeff j =
      ∑ m : t.CutMask, if t.cutCount m = j then
        parts ((t.cutForest m).root :: (t.cutForest m).detached) else 0 := by
  rw [cutPolynomial_eq_sum_cuts, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m _
  simp only [CutForest.term, mul_comm (Polynomial.X ^ _) (Polynomial.C _),
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial_apply, detached_length]

/-- info: 'RestrictedUMinimum.Tree.cutPolynomial_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cutPolynomial_coeff

end
end RestrictedUMinimum.Tree
