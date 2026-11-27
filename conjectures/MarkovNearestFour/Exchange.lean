module

public import conjectures.MarkovNearestFour.Statement
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section
namespace MarkovNearestFour
open MarkovFactorFour

noncomputable def det (p : Vertex) : Poly := u^p.a*v^p.b

def Balanced (T : Triangle) : Prop :=
  det T.right*T.left.num^2 + det T.left*T.right.num^2 + T.middle^2 =
    (1+u+v)*T.left.num*T.right.num*T.middle

theorem balanced_initial : Balanced initial := by
  simp [Balanced,initial,det]
  ring

private theorem det_center (T : Triangle) : det (center T)=det T.left*det T.right := by
  simp only [det,center,pow_add]
  ring

theorem balanced_left (T : Triangle) (h : Balanced T) : Balanced (leftChild T) := by
  change det (center T)*T.left.num^2+det T.left*T.middle^2+(extend T.left T.right T.middle)^2=_
  rw [det_center]
  dsimp [Balanced,leftChild,center,extend,det] at h ⊢
  linear_combination (u^T.left.a*v^T.left.b)*h

theorem balanced_right (T : Triangle) (h : Balanced T) : Balanced (rightChild T) := by
  change det T.right*T.middle^2+det (center T)*T.right.num^2+(extend T.right T.left T.middle)^2=_
  rw [det_center]
  dsimp [Balanced,rightChild,center,extend,det] at h ⊢
  linear_combination (u^T.right.a*v^T.right.b)*h

theorem exchange_left (T : Triangle) (h : Balanced T) :
    T.right.num*(leftChild T).middle = det T.right*T.left.num^2+T.middle^2 := by
  dsimp [Balanced,leftChild,extend,det] at h ⊢
  linear_combination -h

theorem exchange_right (T : Triangle) (h : Balanced T) :
    T.left.num*(rightChild T).middle = det T.left*T.right.num^2+T.middle^2 := by
  dsimp [Balanced,rightChild,extend,det] at h ⊢
  linear_combination -h

end MarkovNearestFour
