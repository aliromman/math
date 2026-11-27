module

public import conjectures.PresuttiStromquist.RangeCount
public meta import conjectures.PresuttiStromquist.RangeCount
public meta import Mathlib.Tactic.Eval
public meta import Lean.Elab.Deriving.ToExpr

@[expose] public section
namespace PresuttiStromquist.Discrete

abbrev Atom := Pos × ℕ

def Cloud.join (a b : Cloud) : Cloud := .node (a.frame.union b.frame) a b

def row : List Atom → Cloud
  | [] => .leaf (0,0) 0
  | (p,w) :: xs => .join (.leaf p w) (row xs)

/-- Median splits keep the integer certificate short. -/
def cloud : ℕ → Bool → List Atom → Cloud
  | _,_,[] => .leaf (0,0) 0
  | _,_,[(p,w)] => .leaf p w
  | 0,_,xs => row xs
  | n+1,dir,p :: q :: xs =>
    let ps := p :: q :: xs
    let sorted := ps.mergeSort (fun a b => if dir then a.1.1 ≤ b.1.1 else a.1.2 ≤ b.1.2)
    let half := ps.length / 2
    .join (cloud n (!dir) (sorted.take half)) (cloud n (!dir) (sorted.drop half))
termination_by structural n _ _ => n

def extent : ℕ := 230400

def orbit (p : Pos) (w : ℕ) : List Atom :=
  [(p,w),((extent-p.2,p.1),w),((extent-p.1,extent-p.2),w),((p.2,extent-p.1),w)]

/-- Each segment contains 32 equally spaced atoms. Four rotations use the same weights. -/
def segment (lo hi F G : ℕ) : List Atom :=
  (List.range 32).flatMap (fun j =>
    let b := 96*lo+(hi-lo)*(3*j+1)
    orbit (extent/4+10*b,5*(11520-b)) (2*(G-F)))

/-- Replace a corner rectangle by four atoms with the relative order 2413. -/
def corner (lo hi : ℕ) : List Atom :=
  ([(1,2),(2,4),(3,1),(4,3)] : List Pos).flatMap (fun p =>
    orbit (extent/4+960*lo+192*(hi-lo)*p.1,480*(120-hi)+96*(hi-lo)*p.2)
      ((hi-lo)*32))

def exampleAtoms : Cloud := cloud 10 true
  (segment 21 38 2 16 ++ segment 38 60 16 36 ++ segment 60 82 36 60 ++
   segment 82 99 60 80 ++ corner 20 21 ++ corner 100 120)

meta section
deriving instance Lean.ToExpr for Frame
deriving instance Lean.ToExpr for Cloud
end

/-- Store only the integer coordinates and bounds. Their validity and weighted counts are checked in the kernel. -/
def exampleCloud : Cloud := eval% exampleAtoms

end PresuttiStromquist.Discrete
