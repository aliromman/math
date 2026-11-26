module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.GCD.Basic

@[expose] public section
namespace MarkovNearestFour
open MvPolynomial

abbrev Poly := MvPolynomial (Fin 2) ℤ
noncomputable abbrev u : Poly := X 0
noncomputable abbrev v : Poly := X 1

structure Vertex where
  a : ℕ
  b : ℕ
  num : Poly

/-- The left and right Farey fractions, with the numerator at their mediant. -/
structure Triangle where
  left : Vertex
  right : Vertex
  middle : Poly

def center (T : Triangle) : Vertex :=
  ⟨T.left.a + T.right.a, T.left.b + T.right.b, T.middle⟩

/-- Equation (8) for the numerators, with the homogeneous variable w set to 1. -/
noncomputable def extend (p q : Vertex) (middle : Poly) : Poly :=
  (1 + u + v) * p.num * middle - u ^ p.a * v ^ p.b * q.num

noncomputable def leftChild (T : Triangle) : Triangle :=
  ⟨T.left, center T, extend T.left T.right T.middle⟩

noncomputable def rightChild (T : Triangle) : Triangle :=
  ⟨center T, T.right, extend T.right T.left T.middle⟩

noncomputable def follow (T : Triangle) : List Bool → Triangle
  | [] => T
  | false :: rest => follow (leftChild T) rest
  | true :: rest => follow (rightChild T) rest

/-- The fractions 0/1 and 1/0 have numerator 1; the mediant 1/1 has u+v. -/
noncomputable def initial : Triangle := ⟨⟨0, 1, 1⟩, ⟨1, 0, 1⟩, u + v⟩

/-- The subtractive Euclidean algorithm gives the path to a positive reduced fraction. -/
def path (l r : ℕ) : List Bool :=
  if l = 0 ∨ r = 0 ∨ l = r then [] else
    if l > r then false :: path (l-r) r else true :: path l (r-l)
termination_by l+r
decreasing_by all_goals omega

noncomputable def numerator (a b : ℕ) : Poly :=
  (follow initial (path b a)).middle

noncomputable def exponent (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

abbrev Fraction := ℕ × ℕ

/-- Consecutive convergents, in numerator-denominator order, after each partial quotient. -/
def continuants : List ℕ → Fraction × Fraction :=
  List.foldl (fun (p : Fraction × Fraction) k =>
    (p.2, (k*p.2.1+p.1.1, k*p.2.2+p.1.2))) ((0,1),(1,0))

/-- Conjecture 8.4 at the penultimate convergent of b/a. The critical triangle is nonempty
when 1<a<b. The reflected coordinates for the two parities follow equation (32). -/
def Conjecture : Prop :=
  ∀ ds : List ℕ, (∀ k ∈ ds, 0<k) →
    let (prev, cur) := continuants ds
    let (b,a) := cur
    1<a → a<b →
      (numerator a b).coeff (if ds.length % 2=0 then exponent prev.2 (b-prev.1)
        else exponent (a-prev.2) prev.1)=4

end MarkovNearestFour
