module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.List.Cycle
public import Mathlib.Data.List.FinRange

@[expose] public section
namespace PolyominoPrimality

abbrev Point := ℕ × ℕ

/-- The vertices at opposite corners of a closed lattice rectangle. -/
structure Rect where
  lo : Point
  hi : Point
deriving DecidableEq, Repr, Inhabited

def Rect.contains (r : Rect) (p : Point) : Bool :=
  r.lo.1 ≤ p.1 && p.1 ≤ r.hi.1 && r.lo.2 ≤ p.2 && p.2 ≤ r.hi.2

def Rect.corner (r : Rect) (right top : Bool) : Point :=
  (if right then r.hi.1 else r.lo.1, if top then r.hi.2 else r.lo.2)

def four (p : Point) : List Point :=
  [p, (p.1+1,p.2), (p.1,p.2+1), (p.1+1,p.2+1)]

def vertices (cells : List Point) := (cells.flatMap four).eraseDups

def adjacent (a b : Point) : Prop :=
  (a.1 = b.1 ∧ (a.2+1 = b.2 ∨ b.2+1 = a.2)) ∨
  (a.2 = b.2 ∧ (a.1+1 = b.1 ∨ b.1+1 = a.1))

instance (a b : Point) : Decidable (adjacent a b) := by unfold adjacent; infer_instance

/-- List the lower left corners of the edge-connected cells, once each. -/
def Polyomino (cells : List Point) : Prop :=
  cells ≠ [] ∧ cells.Nodup ∧ ∀ a ∈ cells, ∀ b ∈ cells,
    ∃ path : List Point, path.head? = some a ∧ path.getLast? = some b ∧
      (∀ p ∈ path, p ∈ cells) ∧ path.IsChain adjacent

/-- Every unit cell of the rectangle must belong to the polyomino. -/
def innerIntervals (cells : List Point) : List Rect :=
  cells.flatMap fun a => cells.filterMap fun b =>
    if a.1 ≤ b.1 && a.2 ≤ b.2 &&
      (List.range (b.1+1-a.1)).all (fun x =>
        (List.range (b.2+1-a.2)).all fun y => cells.contains (a.1+x,a.2+y)) then
      some ⟨a,(b.1+1,b.2+1)⟩ else none

structure Side where
  rect : Rect
  right : Bool
  top : Bool
  vertical : Bool
deriving DecidableEq, Repr, Inhabited

def Side.v (s : Side) := s.rect.corner s.right s.top
def Side.w (s : Side) := s.rect.corner (s.right != !s.vertical) (s.top != s.vertical)
def Side.z (s : Side) := s.rect.corner (!s.right) (!s.top)
def Side.u (s : Side) := s.rect.corner (s.right != s.vertical) (s.top != !s.vertical)

def sides (r : Rect) : List Side :=
  [false,true].flatMap fun x => [false,true].flatMap fun y =>
    [false,true].map fun v => ⟨r,x,y,v⟩

/-- At a common corner the two rectangles occupy opposite quadrants. Thus their
intersection is that corner alone. Each oriented side lies on an edge interval. -/
def Side.follows (a b : Side) : Bool :=
  a.w == b.v && b.right == !(a.right != !a.vertical) && b.top == !(a.top != a.vertical)

def separateMarks (rs : List Rect) (s t : Side) : Bool :=
  !rs.any (fun r => r.contains s.z && r.contains t.z)

/-- The distinct inner intervals form a nonempty closed walk. No inner interval
contains two marked vertices of that walk. This is Definition 3.2 of the paper. -/
def Zigzag (cells : List Point) : Prop :=
  ∃ s : Side, ∃ rest : List Side,
    (∀ t ∈ s::rest, t.rect ∈ innerIntervals cells) ∧
    ((s::rest).map Side.rect).Nodup ∧
    (s::rest).Pairwise (fun a b => separateMarks (innerIntervals cells) a b = true) ∧
    (s::rest++[s]).IsChain (fun a b => a.follows b = true)

abbrev Vertex (cells : List Point) := {v : Point // v ∈ vertices cells}

noncomputable def variableAt (K : Type*) [Field K] (cells : List Point) (v : Point) :
    MvPolynomial (Vertex cells) K :=
  if h : v ∈ vertices cells then MvPolynomial.X ⟨v,h⟩ else 0

noncomputable def minor (K : Type*) [Field K] (cells : List Point) (r : Rect) :=
  let x := variableAt K cells
  x (r.corner false false) * x (r.corner true true) -
    x (r.corner true false) * x (r.corner false true)

noncomputable def polyominoIdeal (K : Type*) [Field K] (cells : List Point) :
    Ideal (MvPolynomial (Vertex cells) K) :=
  Ideal.span {f | ∃ r ∈ innerIntervals cells, minor K cells r = f}

/-- Mascia, Rinaldo and Romeo, Conjecture 1.2. -/
def Conjecture (K : Type*) [Field K] : Prop := ∀ cells : List Point, Polyomino cells →
  ((polyominoIdeal K cells).IsPrime ↔ ¬ Zigzag cells)

end PolyominoPrimality
