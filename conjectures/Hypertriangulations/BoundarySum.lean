module

public import conjectures.Hypertriangulations.Mesh
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace Hypertriangulations
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {P : V→Plane} {E : V→V→Prop}

/-- The number of triangles that traverse the directed edge from i to j. -/
def edgeCount (T : Mesh P E) (i j : V) : ℤ := by
  classical
  exact ((T.faces.filter fun t ↦ t.edge i j).card : ℤ)

private def delta (a b i j : V) : ℤ := if i=a ∧ j=b then 1 else 0

private theorem delta_sum (a b : V) (g : V→V→ℤ) :
    ∑ i, ∑ j, delta a b i j*g i j = g a b := by
  simp [delta,ite_and,ite_mul]

private theorem edge_sum (T : Mesh P E) (g : V→V→ℤ) :
    (∑ t∈T.faces, (g t.a t.b+g t.b t.c+g t.c t.a)) =
      ∑ i, ∑ j, edgeCount T i j*g i j := by
  classical
  let D (t : Face V) (i j : V) := delta t.a t.b i j+delta t.b t.c i j+delta t.c t.a i j
  have h (t : Face V) (ht : t∈T.faces) (i j : V) :
      D t i j = if t.edge i j then 1 else 0 := by
    obtain ⟨a,b,c⟩ := t.neighbors (T.positive t ht)
    dsimp only [D,delta]
    split_ifs <;> grind [Face.edge]
  have count (i j : V) : ∑ t∈T.faces,D t i j=edgeCount T i j := by
    rw [sum_congr rfl (fun t ht ↦ h t ht i j)]
    simp [edgeCount,Finset.sum_boole]
  calc
    _ = ∑ t∈T.faces, ∑ i, ∑ j, D t i j*g i j := by
      apply sum_congr rfl
      intro t _
      simp only [D,add_mul,sum_add_distrib,delta_sum]
    _ = ∑ i, ∑ j, ∑ t∈T.faces, D t i j*g i j := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = _ := by simp_rw [←sum_mul,count]

/-- Equal signed edge multiplicities give equal sums for every antisymmetric potential. -/
theorem boundary_of_coefficients (T S : Mesh P E)
    (h : ∀ i j,edgeCount T i j-edgeCount T j i=edgeCount S i j-edgeCount S j i)
    (g : V→V→ℤ) (anti : ∀ i j,g j i= -g i j) :
    (∑ t∈T.faces,(g t.a t.b+g t.b t.c+g t.c t.a)) =
      ∑ t∈S.faces,(g t.a t.b+g t.b t.c+g t.c t.a) := by
  have rev (U : Mesh P E) :
      (∑ i, ∑ j, edgeCount U j i*g i j) = -(∑ i, ∑ j,edgeCount U i j*g i j) := by
    rw [sum_comm]
    simp only [←sum_neg_distrib,←mul_neg]
    apply sum_congr rfl
    intro j _
    exact sum_congr rfl fun i _ ↦ congrArg (edgeCount U j i*·) (anti j i)
  have eq := congrArg (fun f : V→V→ℤ ↦ ∑ i,∑ j,f i j*g i j) (funext fun i ↦ funext (h i))
  simp only [sub_mul,sum_sub_distrib,rev] at eq
  rw [edge_sum,edge_sum]
  omega

end Hypertriangulations
end
