module

public import conjectures.Hypertriangulations.SignedAreas
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace Hypertriangulations
open Set Finset
open scoped BigOperators Topology
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Counterclockwise vertices of a triangular face. -/
structure Face (V : Type*) where
  a : V
  b : V
  c : V
  deriving DecidableEq

def Face.vertices (t : Face V) : Finset V := {t.a,t.b,t.c}
def Face.area (t : Face V) (P : V→Plane) := orient (P t.a) (P t.b) (P t.c)

def Face.edge (t : Face V) (i j : V) : Prop :=
  (t.a=i ∧ t.b=j) ∨ (t.b=i ∧ t.c=j) ∨ (t.c=i ∧ t.a=j)

def probability (w : V→ℝ) : Prop := (∀ i,0≤w i) ∧ ∑ i,w i=1
def supported (w : V→ℝ) (s : Finset V) : Prop := ∀ i∉s,w i=0
def eval (P : V→Plane) (w : V→ℝ) := ∑ i, w i • P i

def Face.realize (P : V→Plane) (t : Face V) : Set Plane :=
  {x | ∃ w, probability w ∧ supported w t.vertices ∧ eval P w=x}

def weights (faces : Finset (Face V)) : Set (V→ℝ) :=
  {w | probability w ∧ ∃ t∈faces, supported w t.vertices}

/-- An edge-to-edge subdivision of the hull. The same barycentric coordinates on shared faces
give a single label to each used location. Unused labels may have coincident locations. -/
structure Mesh (P : V→Plane) (E : V→V→Prop) where
  faces : Finset (Face V)
  positive : ∀ t∈faces, 0<t.area P
  unique_faces : ∀ t∈faces, ∀ u∈faces, t.vertices=u.vertices → t=u
  edges : ∀ t∈faces, E t.a t.b ∧ E t.b t.c ∧ E t.c t.a
  cover : (∃ a b c, orient (P a) (P b) (P c)≠0) →
    convexHull ℝ (range P) ⊆ eval P '' weights faces
  embedded : InjOn (eval P) (weights faces)

def Refines {P : V→Plane} {E} (S T : Mesh P E) : Prop :=
  ∀ s∈S.faces, ∃ t∈T.faces, Face.realize P s ⊆ Face.realize P t

def IsMaximal {P : V→Plane} {E} (T : Mesh P E) : Prop :=
  ∀ S : Mesh P E, Refines S T → S.faces.card ≤ T.faces.card

def IsMaximum {P : V→Plane} {E} (T : Mesh P E) : Prop :=
  ∀ S : Mesh P E, S.faces.card ≤ T.faces.card

def massAt (i : V) (r : ℝ) (j : V) := if j=i then r else 0

@[simp] theorem sum_massAt (i : V) (r : ℝ) : ∑ j, massAt i r j = r := by simp [massAt]
@[simp] theorem eval_massAt (P : V→Plane) (i : V) (r : ℝ) : eval P (massAt i r)=r • P i := by
  classical
  simp [eval,massAt,ite_smul]

omit [DecidableEq V] in
theorem eval_add (P : V→Plane) (v w : V→ℝ) : eval P (v+w) = eval P v + eval P w := by
  simp [eval,add_smul,sum_add_distrib]

omit [DecidableEq V] in
theorem eval_scale (P : V→Plane) (v : V→ℝ) (c : ℝ) : eval P (c • v) = c • eval P v := by
  simp [eval,Finset.smul_sum,smul_smul]

def coords (f : Face V) (u v w : ℝ) := massAt f.a u + massAt f.b v + massAt f.c w

theorem coords_sum (f : Face V) (u v w : ℝ) : ∑ i, coords f u v w i = u+v+w := by
  simp [coords,Finset.sum_add_distrib]

theorem coords_eval (P : V→Plane) (f : Face V) (u v w : ℝ) :
    eval P (coords f u v w) = u • P f.a + v • P f.b + w • P f.c := by
  simp [coords,eval_add]

omit [Fintype V] in
theorem coords_supported (f : Face V) (u v w : ℝ) : supported (coords f u v w) f.vertices := by
  intro i h
  simp [Face.vertices] at h
  simp [coords,massAt,h]

omit [Fintype V] [DecidableEq V] in
theorem Face.neighbors {P : V→Plane} {t : Face V} (h : 0 < t.area P) :
    t.a≠t.b ∧ t.b≠t.c ∧ t.c≠t.a := by
  unfold Face.area at h
  constructor
  · rintro e; simp [e,orient,mul_comm] at h
  constructor
  · rintro e; simp [e,orient,mul_comm] at h
  · rintro e; simp [e,orient] at h

omit [Fintype V] in
theorem coords_entries {P : V→Plane} {f : Face V} (h : 0<f.area P) (u v w : ℝ) :
    coords f u v w f.a=u ∧ coords f u v w f.b=v ∧ coords f u v w f.c=w := by
  obtain ⟨a,b,c⟩ := f.neighbors h
  simp [coords,massAt,a,a.symm,b,b.symm,c,c.symm]

theorem coords_probability (f : Face V) {u v w : ℝ} (a : 0≤u) (b : 0≤v) (c : 0≤w) (s : u+v+w=1) :
    probability (coords f u v w) := by
  refine ⟨fun i ↦ ?_, (coords_sum _ _ _ _).trans s⟩
  simp only [coords,Pi.add_apply,massAt]
  positivity

/-- Positive barycentric coordinates of a geometric interior point. -/
theorem inside_coordinates {P : V→Plane} {f : Face V} (hf : 0 < f.area P) {p : Plane}
    (hp : StrictInside (P f.a) (P f.b) (P f.c) p) :
    ∃ w : V→ℝ, probability w ∧ supported w f.vertices ∧ eval P w=p ∧ ∀ i∈f.vertices,0<w i := by
  let A := orient p (P f.b) (P f.c)
  let B := orient p (P f.c) (P f.a)
  let C := orient p (P f.a) (P f.b)
  let D := f.area P
  have total : A+B+C=D := by unfold A B C D Face.area orient; ring
  have h : 0<C ∧ 0<A ∧ 0<B := by rcases hp with pos|neg; exact pos; change _<D at hf; change C<0 ∧ A<0 ∧ B<0 at neg; linarith [neg.1,neg.2.1,neg.2.2]
  have d : D≠0 := ne_of_gt hf
  let w := coords f (A/D) (B/D) (C/D)
  refine ⟨w,coords_probability f (div_nonneg h.2.1.le hf.le) (div_nonneg h.2.2.le hf.le) (div_nonneg h.1.le hf.le)
    (by field_simp; linarith),coords_supported _ _ _ _,?_,?_⟩
  · rw [show w=coords f (A/D) (B/D) (C/D) by rfl,coords_eval]
    ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;>
      field_simp <;> unfold A B C D Face.area orient <;> ring
  · intro i hi
    have e := coords_entries hf (A/D) (B/D) (C/D)
    simp only [Face.vertices,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · dsimp only [w]; rw [e.1]; exact div_pos h.2.1 hf
    · dsimp only [w]; rw [e.2.1]; exact div_pos h.2.2 hf
    · dsimp only [w]; rw [e.2.2]; exact div_pos h.1 hf

end Hypertriangulations
end
