module

public import conjectures.Hypertriangulations.Labels
public import conjectures.Hypertriangulations.Mesh

@[expose] public section
namespace Hypertriangulations
open Finset

/-- Squared Euclidean distance in the coordinate plane. -/
def squaredDistance (x y : Plane) : ℝ := (x.1-y.1)^2+(x.2-y.2)^2

/-- The source excludes three collinear points and four points on a common Euclidean circle. -/
def Generic (A : Finset Plane) : Prop := GeneralPosition ((↑) : A→Plane) ∧
  ∀ a b c d : A, a≠b → a≠c → a≠d → b≠c → b≠d → c≠d →
    ¬∃ o : Plane, squaredDistance a o=squaredDistance b o ∧ squaredDistance a o=squaredDistance c o ∧
      squaredDistance a o=squaredDistance d o

abbrev Level (α : Type*) (k : ℕ) := {I : Finset α // I.card=k}

abbrev LevelMesh {α : Type*} [Fintype α] [DecidableEq α] (P : α→Plane) (k : ℕ) :=
  Mesh (fun i : Level α k ↦ average P k i.val) (fun i j ↦ Exchange i.val j.val)

/-- Edelsbrunner, Garber and Saghafian, Conjecture C, §6. -/
def Conjecture : Prop := ∀ (A : Finset Plane), Generic A → ∀ k : ℕ, 1≤k → k<A.card →
  ∀ T : LevelMesh ((↑) : A→Plane) k, IsMaximal T → IsMaximum T

end Hypertriangulations
