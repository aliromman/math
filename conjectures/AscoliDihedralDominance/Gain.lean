module

public import conjectures.AscoliDihedralDominance.Statement

@[expose] public section
namespace AscoliDihedral
open Finset

/-- The excess number of product-dominant subsets at a fixed size. -/
def gainAt (G : Type*) [Group G] [Fintype G] [DecidableEq G] (m : ℕ) : ℤ :=
  (((univ.powersetCard m).filter fun A : Finset G ↦ (quotients A).card < (products A).card).card : ℤ) -
    (((univ.powersetCard m).filter fun A : Finset G ↦ (products A).card < (quotients A).card).card : ℤ)

end AscoliDihedral
