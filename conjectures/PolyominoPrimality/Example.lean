module

public import conjectures.PolyominoPrimality.Statement

@[expose] public section
namespace PolyominoPrimality

def exampleCells : List Point :=
  [(1,0),(2,0),(0,1),(2,1),(3,1),(0,2),(1,2),(2,2),(0,3),(2,3),(3,3),(1,4),(2,4)]

private def toCentre : Point → List Point
  | (1,0) => [(1,0),(2,0),(2,1),(2,2)]
  | (2,0) => [(2,0),(2,1),(2,2)]
  | (0,1) => [(0,1),(0,2),(1,2),(2,2)]
  | (2,1) => [(2,1),(2,2)]
  | (3,1) => [(3,1),(2,1),(2,2)]
  | (0,2) => [(0,2),(1,2),(2,2)]
  | (1,2) => [(1,2),(2,2)]
  | (0,3) => [(0,3),(0,2),(1,2),(2,2)]
  | (2,3) => [(2,3),(2,2)]
  | (3,3) => [(3,3),(2,3),(2,2)]
  | (1,4) => [(1,4),(2,4),(2,3),(2,2)]
  | (2,4) => [(2,4),(2,3),(2,2)]
  | p => [p]

theorem connectedExample : Polyomino exampleCells := by
  refine ⟨by decide, by decide, ?_⟩
  let route (a b : Point) := toCentre a ++ (toCentre b).reverse.tail
  have routes : ∀ a ∈ exampleCells, ∀ b ∈ exampleCells,
      (route a b).head? = some a ∧ (route a b).getLast? = some b ∧
      (∀ p ∈ route a b, p ∈ exampleCells) ∧ (route a b).IsChain adjacent := by decide +kernel
  exact fun a ha b hb => ⟨route a b,routes a ha b hb⟩

end PolyominoPrimality
