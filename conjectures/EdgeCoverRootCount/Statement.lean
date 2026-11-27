module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

open scoped Classical Polynomial
open Polynomial

namespace EdgeCoverRootCount

/-- The selected edges meet every vertex. -/
def Covers {n : ℕ} (s : Finset (Sym2 (Fin n))) : Prop :=
  ∀ v : Fin n, ∃ e ∈ s, v ∈ e

noncomputable def edgeCoverPolynomial {n : ℕ} (G : SimpleGraph (Fin n)) : ℂ[X] :=
  ∑ s ∈ G.edgeFinset.powerset.filter Covers, X ^ s.card

/-- Alikhani, Conjecture 5, attributed to Akbari and Oboudi. -/
def Conjecture : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.minDegree ≤ (edgeCoverPolynomial G).roots.toFinset.card

end EdgeCoverRootCount
