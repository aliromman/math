module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.GCD.Basic

@[expose] public section
namespace MarkovFactorFour
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

/-- Evans, Veselov and Winn, Conjecture 8.1. The last inequality is i/a+j/b>1. -/
def Conjecture : Prop :=
  ∀ a b : ℕ, 0 < a → a ≤ b → Nat.Coprime a b → ∀ i j : ℕ,
    i < a → j < b → a*b < i*b + j*a → (4 : ℤ) ∣ (numerator a b).coeff (exponent i j)

end MarkovFactorFour
