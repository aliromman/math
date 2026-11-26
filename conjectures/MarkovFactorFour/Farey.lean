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

/-- The path selects the indicated positive combination of the two Farey endpoints. -/
private theorem path_coordinate (f : Vertex → ℕ) (hf : ∀ T, f (center T) = f T.left + f T.right)
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) (h : l.Coprime r) (T : Triangle) :
    f (center (follow T (path l r))) = l*f T.left + r*f T.right := by
  rw [path]
  split
  · rename_i he
    have heq : l=r := by omega
    subst r
    have hl1 : l=1 := by simpa [Nat.Coprime] using h
    subst l
    simp [follow, hf]
  · rename_i he
    split
    · rename_i hgt
      change f (center (follow (leftChild T) (path (l-r) r))) = _
      rw [path_coordinate f hf (l-r) r (by omega) hr ((Nat.coprime_sub_self_left hgt.le).2 h)]
      change (l-r)*f T.left + r*f (center T) = _
      rw [hf, Nat.mul_add, ← Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel hgt.le]
    · rename_i hle
      change f (center (follow (rightChild T) (path l (r-l)))) = _
      rw [path_coordinate f hf l (r-l) hl (by omega) ((Nat.coprime_sub_self_right (by omega)).2 h)]
      change l*f (center T) + (r-l)*f T.right = _
      have heq : l+(r-l)=r := by omega
      rw [hf, Nat.mul_add, Nat.add_assoc, ←Nat.add_mul, heq]
termination_by l+r

theorem selected_coordinates (a b : ℕ) (ha : 0<a) (hb : 0<b) (h : a.Coprime b) :
    (center (follow initial (path b a))).a = a ∧ (center (follow initial (path b a))).b = b := by
  constructor
  · simpa [initial] using path_coordinate Vertex.a (fun _ => rfl) b a hb ha h.symm initial
  · simpa [initial] using path_coordinate Vertex.b (fun _ => rfl) b a hb ha h.symm initial

end MarkovFactorFour
