module

public import conjectures.Hypertriangulations.Statement
public import conjectures.Hypertriangulations.FaceValue
public import conjectures.Hypertriangulations.Support
public import conjectures.Hypertriangulations.Boundary
public import conjectures.Hypertriangulations.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace Hypertriangulations
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] (P : α→Plane) {k : ℕ}

omit [Fintype α] in
private theorem forced_support (gp : GeneralPosition P) (hk : 0<k) (i j : Level α k)
    (ne : average P k i.val≠average P k j.val)
    (side : ∀ z : Level α k,0≤orient (average P k i.val) (average P k j.val) (average P k z.val))
    (z : Level α k) (onLine : orient (average P k i.val) (average P k j.val) (average P k z.val)=0) :
    z=i ∨ z=j := by
  let X := average P k i.val
  let Y := average P k j.val
  let u := Y.2-X.2
  let v := X.1-Y.1
  have linear : u≠0 ∨ v≠0 := by
    by_contra! e
    apply ne; apply Prod.ext <;> dsimp only [u,v] at e <;> linarith only [e.1,e.2]
  have eval (p : Plane) : orient X Y p=projection u v X-projection u v p := by unfold orient projection u v;ring
  have top (t : Level α k) (h : orient X Y (average P k t.val)=0) : MaxScore (projection u v ∘ P) k t.val := by
    refine (maxScore_iff_average P hk u v).mpr ⟨t.property,?_⟩
    intro L hL
    have low := side ⟨L,hL⟩
    change 0≤orient X Y (average P k L) at low
    rw [eval] at h low
    linarith only [h,low]
  have iMax := top i (by change orient X Y X=0; simp [orient])
  have jMax := top j (by change orient X Y Y=0; unfold orient;ring)
  rcases support_labels gp linear iMax jMax (top z onLine) with eq|eq|eq
  · exact False.elim (ne (congrArg (average P k) eq))
  · exact Or.inl (Subtype.ext eq.symm)
  · exact Or.inr (Subtype.ext eq.symm)

private theorem maximum_of_weights (gp : GeneralPosition P) (hk : 0<k) (T : LevelMesh P k)
    (ins : ∀ {t : Face (Level α k)},t∈T.faces → ∀ {d : Level α k},
      (Exchange t.a.val d.val ∧ Exchange t.b.val d.val ∧ Exchange t.c.val d.val) →
      ¬StrictInside (average P k t.a.val) (average P k t.b.val) (average P k t.c.val) (average P k d.val))
    (invar : ∀ (S : LevelMesh P k) (g : Level α k→Level α k→ℤ), (∀ i j,g j i= -g i j) →
      (∑ t∈T.faces,(g t.a t.b+g t.b t.c+g t.c t.a))=∑ t∈S.faces,(g t.a t.b+g t.b t.c+g t.c t.a)) : IsMaximum T := by
  obtain ⟨g,anti,faces⟩ := mesh_weights P gp
  let q (t : Face (Level α k)) := faceValue g t.a.val t.b.val t.c.val
  have val (S : LevelMesh P k) (t : Face (Level α k)) (ht : t∈S.faces) :=
    faces hk t.a.val t.b.val t.c.val t.a.property (S.edges t ht).1 (S.edges t ht).2.1 (S.edges t ht).2.2 (S.positive t ht)
  have unit (t : Face (Level α k)) (ht : t∈T.faces) : q t=1 := by
    obtain ⟨one,high⟩ := val T t ht
    have low : ¬1<q t := by
      intro gt
      obtain ⟨D,card,ad,bd,cd,inside⟩ := high gt
      exact ins ht (d:=⟨D,card⟩) ⟨ad,bd,cd⟩ inside
    dsimp only [q] at low ⊢;omega
  intro S
  have equal : ∑t∈T.faces,q t=∑t∈S.faces,q t := invar S (fun i j ↦ g i.val j.val) (fun i j ↦ anti i.val j.val)
  have lower : (S.faces.card : ℤ)≤∑t∈S.faces,q t := by
    calc (S.faces.card : ℤ) = ∑ _t∈S.faces,(1:ℤ) := by simp
         _ ≤ ∑ t∈S.faces,q t := sum_le_sum fun t ht ↦ (val S t ht).1
  rw [←equal,sum_congr rfl unit] at lower
  simpa using lower

/-- No single face admits an interior subdivision by a new adjacent label. -/
def LocallyFull (T : LevelMesh P k) : Prop := ∀ {t : Face (Level α k)},t∈T.faces → ∀ {d : Level α k},
  (Exchange t.a.val d.val ∧ Exchange t.b.val d.val ∧ Exchange t.c.val d.val) →
  ¬StrictInside (average P k t.a.val) (average P k t.b.val) (average P k t.c.val) (average P k d.val)

/-- A hypertriangulation attains the maximum exactly when no elementary face insertion is possible. -/
theorem maximum_iff_locallyFull (gp : GeneralPosition P) (hk : 0<k) (T : LevelMesh P k) : IsMaximum T ↔ LocallyFull P T := by
  constructor
  · intro max t ht d edges
    exact no_insert T (fun e ↦ e.symm) (fun S _ ↦ max S) ht edges
  · intro full
    exact maximum_of_weights P gp hk T full (fun S g anti ↦ boundary_invariant T S (forced_support P gp hk) g anti)

/-- The conclusion holds whenever no three points are collinear. -/
theorem maximal_is_maximum (gp : GeneralPosition P) (hk : 0<k) (T : LevelMesh P k) (maximal : IsMaximal T) : IsMaximum T := by
  apply (maximum_iff_locallyFull P gp hk T).mpr
  intro t ht d edges
  exact no_insert T (fun e ↦ e.symm) maximal ht edges

theorem resolution : Conjecture := by
  intro A generic k hk _ T maximal
  exact maximal_is_maximum _ generic.1 hk T maximal

/-- info: 'Hypertriangulations.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end Hypertriangulations
