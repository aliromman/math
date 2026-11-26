module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Data.Rat.Defs

@[expose] public section

namespace EngbersErey

abbrev Edge := ℕ × ℕ

/-- Each undirected edge occurs once, with its smaller endpoint first. -/
def Valid (n : ℕ) (edges : List Edge) : Prop :=
  edges.Nodup ∧ ∀ e ∈ edges, e.1 < e.2 ∧ e.2 < n

def graph (n : ℕ) (edges : List Edge) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u.val, v.val) ∈ edges ∨ (v.val, u.val) ∈ edges)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def meet (e f : Edge) : Bool :=
  e.1 == f.1 || e.1 == f.2 || e.2 == f.1 || e.2 == f.2

/-- A matching is maximal if every edge meets a selected edge. -/
def maximalMatchingSizes (edges : List Edge) : List ℕ :=
  (edges.sublists.filter fun m =>
    decide (m.Pairwise fun e f => meet e f = false) &&
      edges.all (fun e => m.any (meet e))).map List.length

def average (edges : List Edge) : ℚ :=
  let sizes := maximalMatchingSizes edges
  (sizes.sum : ℚ) / sizes.length

/-- Add two-edge arms at vertex 2 of a path of length `d`.
The odd-order, odd-diameter case has an extra leaf at vertex `d - 2`. -/
def candidateEdges (n d : ℕ) (leaf : Bool) : List Edge :=
  (List.range d).map (fun i => (i, i + 1)) ++
  (List.range ((n - d - 1) / 2)).flatMap (fun j =>
    let v := d + 1 + 2 * j
    [(2, v), (v, v + 1)]) ++
  (if leaf then [(d - 2, n - 1)] else [])

def UniqueMax (n d : ℕ) (candidate : List Edge) : Prop :=
  Valid n candidate ∧ (graph n candidate).IsTree ∧ (graph n candidate).diam = d ∧
  ∀ edges, Valid n edges → (graph n edges).IsTree → (graph n edges).diam = d →
    average edges ≤ average candidate ∧
    (average edges = average candidate → Nonempty (graph n edges ≃g graph n candidate))

/-- The maximum conjecture of Engbers and Erey, as stated in
Conjecture 1.2 of Sui and Li. -/
def Conjecture : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d < n →
    ((n + d) % 2 = 1 → UniqueMax n d (candidateEdges n d false)) ∧
    (n % 2 = 1 → d % 2 = 1 → UniqueMax n d (candidateEdges n d true))

end EngbersErey
