module

public import conjectures.MarkovFactorFour.Statement

@[expose] public section
namespace MarkovFactorFour

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
