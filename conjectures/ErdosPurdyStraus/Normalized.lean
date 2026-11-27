module

public import conjectures.ErdosPurdyStraus.Statement

@[expose] public section
noncomputable section
namespace ErdosPurdyStraus
open Set MeasureTheory

abbrev baseLo : Plane := (0,-1/2)
abbrev baseHi : Plane := (0,1/2)
abbrev apex : Plane := (1,0)

/-- Affine coordinates put the supporting side at height zero and the opposite vertex at height one. -/
structure Standard (K : Set Plane) : Prop where
  convex : Convex ℝ K
  compact : IsCompact K
  lo : baseLo ∈ K
  hi : baseHi ∈ K
  top : apex ∈ K
  height : ∀ p ∈ K, p.1 ∈ Icc 0 1
  triangles : ∀ p ∈ K, ∀ q ∈ K, ∀ r ∈ K, |cross p q r| ≤ 1

end ErdosPurdyStraus
end
