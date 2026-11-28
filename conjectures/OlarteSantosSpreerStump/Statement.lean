module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace OlarteSantosSpreerStump

abbrev Family (V : Type*) := Set (Finset V)

/-- A flag complex consists of all finite cliques in its graph. This includes the empty face. -/
def flagComplex {V : Type*} (G : SimpleGraph V) : Family V :=
  {s | G.IsClique (s : Set V)}

/-- Every face lies in a facet of size `d + 1`, and every ridge lies in two distinct facets. -/
def PureWithoutBoundary {V : Type*} (d : ℕ) (D : Family V) : Prop :=
  (∃ s ∈ D, s.card = d + 1) ∧
  (∀ s ∈ D, s.card ≤ d + 1 ∧ ∃ t ∈ D, s ⊆ t ∧ t.card = d + 1) ∧
  ∀ r ∈ D, r.card = d → ∃ p ∈ D, ∃ q ∈ D,
    p ≠ q ∧ r ⊆ p ∧ r ⊆ q ∧ p.card = d + 1 ∧ q.card = d + 1

/-- The intersecting dual contains each face that meets every member of the family. -/
def dual {V : Type*} (D U : Family V) : Family V :=
  {s | s ∈ D ∧ ∀ t ∈ U, ∃ v ∈ s, v ∈ t}

def IsDualPair {V : Type*} (D U₁ U₂ : Family V) : Prop :=
  U₁ = dual D U₂ ∧ U₂ = dual D U₁

def minimalFaces {V : Type*} (U : Family V) : Family V :=
  {s | s ∈ U ∧ ∀ t ∈ U, t ⊆ s → s ⊆ t}

/-- The essential vertices are those in the minimal faces. For a dual pair either side
gives the same set, by Proposition 2.2(3) of the source. -/
def essential {V : Type*} (U : Family V) : Set V :=
  {v | ∃ s ∈ minimalFaces U, v ∈ s}

def CarriesMinima {V W : Type*} {E : Set V} {F : Set W} (e : E ≃ F)
    (U : Family V) (T : Family W) : Prop :=
  ∀ s : Finset E, s.map (Function.Embedding.subtype _) ∈ minimalFaces U ↔
    s.map (e.toEmbedding.trans (Function.Embedding.subtype _)) ∈ minimalFaces T

/-- Isomorphism of dual pairs, including the possible interchange of their two sides. -/
def Isomorphic {V W : Type*} (U₁ U₂ : Family V) (T₁ T₂ : Family W) : Prop :=
  ∃ e : essential U₁ ≃ essential T₁,
    (CarriesMinima e U₁ T₁ ∧ CarriesMinima e U₂ T₂) ∨
    (CarriesMinima e U₁ T₂ ∧ CarriesMinima e U₂ T₁)

/-- A boundary face of the `(d + 1)`-cross-polytope contains at most one signed
vertex from each coordinate axis. -/
def crossBoundary (d : ℕ) : Family (Fin (d + 1) × Bool) :=
  {s | ∀ i, ¬ ((i, false) ∈ s ∧ (i, true) ∈ s)}

/-- Olarte, Santos, Spreer and Stump, Conjecture 3.5 (journal), 3.8 (preprint). -/
def Conjecture : Prop :=
  ∀ (d : ℕ) (V : Type) (G : SimpleGraph V) (U₁ U₂ : Family V),
    PureWithoutBoundary d (flagComplex G) → IsDualPair (flagComplex G) U₁ U₂ →
    ∃ T₁ T₂, IsDualPair (crossBoundary d) T₁ T₂ ∧ Isomorphic U₁ U₂ T₁ T₂

end OlarteSantosSpreerStump
