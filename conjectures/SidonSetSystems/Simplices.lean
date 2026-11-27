module

public import conjectures.SidonSetSystems.Detection
public import conjectures.SidonSetSystems.Dimension
public import conjectures.SidonSetSystems.Projection
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

@[expose] public section
namespace SidonSetSystems
open Finset Module
open scoped Classical
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem Balanced.detect {A B C D : Figure V} (h : Balanced A B C D) (af : A.Free) :
    A.directions≤B.directions ∨ A.directions≤C.directions ∨ A.directions≤D.directions := by
  let P : Fin 3 → Figure V := ![B,C,D]
  let w : Fin 3 → ℚ := ![-1,1,1]
  obtain ⟨i,hi⟩ := detect_directions A P w af (fun f => by
    simp [P,w,Fin.sum_univ_three]
    linarith [h f])
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

theorem Balanced.flip_left {A B C D : Figure V} (h : Balanced A B C D) : Balanced B A C D :=
  fun f => (add_comm ..).trans (h f)

theorem Balanced.flip_right {A B C D : Figure V} (h : Balanced A B C D) : Balanced A B D C :=
  fun f => (h f).trans (add_comm ..)

theorem Balanced.symm {A B C D : Figure V} (h : Balanced A B C D) : Balanced C D A B :=
  fun f => (h f).symm

private theorem le_of_disjoint_le {X Y Z : Submodule ℚ V} (d : Disjoint X Y) (h : X≤Y) : X≤Z := by
  intro x hx
  rw [Submodule.disjoint_def.mp d x hx (h hx)]
  exact Z.zero_mem

private theorem matched_gap [FiniteDimensional ℚ V] {A B C D : Figure V}
    (h : Balanced A B C D) (af : A.Free) (cf : C.Free)
    (ac : A.directions=C.directions) (bd : B.directions=D.directions)
    (different : ¬A.directions≤B.directions) :
    ∃ t : V, ∀ f : Probe V, A.support f = C.support f+f.1 t := by
  obtain ⟨v,va,vb⟩ := Set.not_subset.mp different
  obtain ⟨p,pos,pb⟩ := B.probe_of_outside vb
  have kill : ∀ x∈B.directions,p.1 x=0 := B.constant_on (fun i j => (pb i i.2).trans (pb j j.2).symm)
  have negA := A.opposite_faces p va pos.ne'
  have negC := C.opposite_faces p (ac ▸ va) pos.ne'
  obtain ⟨d,hd⟩ := D.exists_site
  have pd := D.flat_directions p hd (bd ▸ kill)
  have fb := B.face_of_constant pb
  have fd := D.face_of_constant pd
  have eb (x : V) (hx : x∈B.sites) : (-p).read x=0 := by rw [Figure.read_neg,pb x hx,neg_zero]
  have ed (x : V) (hx : x∈D.sites) : (-p).read x= -p.read d := by rw [Figure.read_neg,pd x hx]
  have plus := h.face p
  have minus := h.face (-p)
  rw [fb,fd] at plus
  rw [B.face_of_constant eb,D.face_of_constant ed] at minus
  have crossed : Balanced (A.face p) (C.face (-p)) (A.face (-p)) (C.face p) :=
    fun f => by linarith only [plus f,minus f]
  let X := (A.face p).directions
  let Y := (A.face (-p)).directions
  let Z := (C.face p).directions
  let W := (C.face (-p)).directions
  have xy : Disjoint X Y := Figure.disjoint_directions af (A.face_subset _) (A.face_subset _) negA
  have zw : Disjoint Z W := Figure.disjoint_directions cf (C.face_subset _) (C.face_subset _) negC
  obtain ⟨xw,yz,xz,yw⟩ := crossed_spaces X Y Z W xy zw crossed.directions
  have ux : X≤Z := by
    rcases crossed.detect (A.free_of_subset af (A.face_subset _)) with bad|bad|yes
    · exact le_of_disjoint_le xw bad
    · exact le_of_disjoint_le xy bad
    · exact yes
  have uy : Y≤W := by
    rcases crossed.symm.detect (A.free_of_subset af (A.face_subset _)) with bad|bad|yes
    · exact le_of_disjoint_le yz bad
    · exact le_of_disjoint_le xy.symm bad
    · exact yes
  have XZ := Submodule.eq_of_le_of_finrank_eq ux xz
  have YW := Submodule.eq_of_le_of_finrank_eq uy yw
  obtain ⟨t,ht⟩ := gap_of_disjoint crossed.flip_right X Y xy le_rfl YW.ge XZ.ge le_rfl
  exact ⟨t,fun f => by linarith only [h f,plus f,ht f]⟩

def Translates (A C : Figure V) : Prop :=
  ∃ t : V, (∀ a∈A.sites, ∃ c∈C.sites, a=c+t) ∧ (∀ c∈C.sites, ∃ a∈A.sites, a=c+t)

private theorem translates_of_gap {A C : Figure V} (af : A.Free) (cf : C.Free) {t : V}
    (eq : ∀ f : Probe V, A.support f=C.support f+f.1 t) : Translates A C := by
  refine ⟨t,fun _ ha => points_of_gap af eq ha,fun c hc => ?_⟩
  have back (f : Probe V) : C.support f=A.support f+f.1 (-t) := by rw [map_neg]; linarith only [eq f]
  obtain ⟨a,ha,e⟩ := points_of_gap cf back hc
  exact ⟨a,ha,by rw [e]; simp⟩

/-- A sum of two equally large simplices with different direction spaces determines both
sets of vertices up to translation and exchange. -/
theorem separate_simplices [FiniteDimensional ℚ V] (A B C D : Figure V)
    (h : Balanced A B C D) (af : A.Free) (bf : B.Free) (cf : C.Free) (df : D.Free)
    (ab : A.sites.card=B.sites.card) (ac : A.sites.card=C.sites.card) (ad : A.sites.card=D.sites.card)
    (diff : A.directions≠B.directions) :
    (Translates A C ∧ Translates B D) ∨ (Translates A D ∧ Translates B C) := by
  have ra := A.free_dimension af
  have rb := B.free_dimension bf
  have rc := C.free_dimension cf
  have rd := D.free_dimension df
  have neAB : ¬A.directions≤B.directions := fun le => diff (Submodule.eq_of_le_of_finrank_eq le (by omega))
  have neBA : ¬B.directions≤A.directions := fun le => diff (Submodule.eq_of_le_of_finrank_eq le (by omega)).symm
  have pair (P Q : Figure V) (pf : P.Free) (qf : Q.Free) (bal : Balanced A B P Q)
      (ap : A.directions=P.directions) (bq : B.directions=Q.directions) :
      Translates A P ∧ Translates B Q := by
    obtain ⟨t,e⟩ := matched_gap bal af pf ap bq neAB
    exact ⟨translates_of_gap af pf e,translates_of_gap bf qf (t:= -t)
      (fun f => by rw [map_neg]; linarith only [bal f,e f])⟩
  rcases (h.detect af).resolve_left neAB with av|av <;>
    rcases (h.flip_left.detect bf).resolve_left neBA with bv|bv
  · exact (diff ((Submodule.eq_of_le_of_finrank_eq av (by omega)).trans
      (Submodule.eq_of_le_of_finrank_eq bv (by omega)).symm)).elim
  · exact Or.inl (pair C D cf df h (Submodule.eq_of_le_of_finrank_eq av (by omega))
      (Submodule.eq_of_le_of_finrank_eq bv (by omega)))
  · exact Or.inr (pair D C df cf h.flip_right (Submodule.eq_of_le_of_finrank_eq av (by omega))
      (Submodule.eq_of_le_of_finrank_eq bv (by omega)))
  · exact (diff ((Submodule.eq_of_le_of_finrank_eq av (by omega)).trans
      (Submodule.eq_of_le_of_finrank_eq bv (by omega)).symm)).elim

end SidonSetSystems
