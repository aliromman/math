module

public import conjectures.SidonSetSystems.Faces
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

public section
namespace SidonSetSystems
open Finset
open scoped Classical
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

private theorem simultaneous_projection (U W : Submodule ℚ V) (d : Disjoint U W) :
    ∃ π : V→ₗ[ℚ] V, (∀ x∈U, π x=x) ∧ (∀ x∈W, π x=0) := by
  let j := U.subtype.coprod W.subtype
  have inj : j.ker=⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨u,w⟩ h
    change (u:V)+(w:V)=0 at h
    have he := eq_neg_of_add_eq_zero_left h
    have hu : (u:V)=0 := Submodule.disjoint_def.mp d _ u.property (he ▸ W.neg_mem w.property)
    have hw : (w:V)=0 := by simpa [hu] using h
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hw)
  obtain ⟨L,hL⟩ := j.exists_leftInverse_of_injective inj
  let π := U.subtype.comp ((LinearMap.fst ℚ U W).comp L)
  have eq (u : U) (w : W) : L ((u:V)+(w:V))=(u,w) := LinearMap.congr_fun hL (u,w)
  refine ⟨π,?_,?_⟩
  · intro x hx
    have ex := eq ⟨x,hx⟩ 0
    simpa [π] using congrArg (fun z : U×W => (z.1:V)) ex
  · intro x hx
    have ex := eq 0 ⟨x,hx⟩
    simpa [π] using congrArg (fun z : U×W => (z.1:V)) ex

private theorem support_project (A : Figure V) (f : Probe V) (π : V→ₗ[ℚ] V) {a : V} (ha : a∈A.sites)
    (h : ∀ x∈A.directions, π x=x) :
    A.support (f.1.comp π,f.2)=A.support f+f.1 (π a-a) := by
  apply A.support_offset
  intro x hx
  have eq := h (x-a) (A.sub_mem hx ha)
  rw [map_sub] at eq
  have ex : π x=x+(π a-a) := by calc
    π x = (x-a)+π a := sub_eq_iff_eq_add.mp eq
    _ = _ := by abel
  simp only [Probe.read,LinearMap.comp_apply,ex,map_add,map_sub]
  ring

private theorem support_vanish (A : Figure V) (f : Probe V) (π : V→ₗ[ℚ] V) {a : V} (ha : a∈A.sites)
    (h : ∀ x∈A.directions, π x=0) : A.support (f.1.comp π,f.2)=f.1 (π a)+f.2 := by
  apply A.support_constant
  intro x hx
  have eq := h (x-a) (A.sub_mem hx ha)
  rw [map_sub,sub_eq_zero] at eq
  simp [Probe.read,eq]

/-- Factors with independent directions can only exchange an overall translation. -/
theorem gap_of_disjoint {A B C D : Figure V} (bal : Balanced A B C D)
    (U W : Submodule ℚ V) (dis : Disjoint U W)
    (hA : A.directions≤U) (hB : B.directions≤W) (hC : C.directions≤U) (hD : D.directions≤W) :
    ∃ t : V, ∀ f : Probe V, A.support f=C.support f+f.1 t := by
  obtain ⟨π,fix,kill⟩ := simultaneous_projection U W dis
  obtain ⟨a,ha⟩ := A.exists_site
  obtain ⟨b,hb⟩ := B.exists_site
  obtain ⟨c,hc⟩ := C.exists_site
  obtain ⟨d,hd⟩ := D.exists_site
  refine ⟨(π c-c)+π d-(π a-a)-π b,fun f => ?_⟩
  have eq := bal (f.1.comp π,f.2)
  rw [support_project A f π ha (fun x hx => fix x (hA hx)),
    support_vanish B f π hb (fun x hx => kill x (hB hx)),
    support_project C f π hc (fun x hx => fix x (hC hx)),
    support_vanish D f π hd (fun x hx => kill x (hD hx))] at eq
  simp only [map_add,map_sub] at eq ⊢
  linarith

/-- Independent points are the exposed vertices; their supports determine all of them. -/
theorem points_of_gap {A C : Figure V} (af : A.Free) {t : V}
    (gap : ∀ f : Probe V, A.support f=C.support f+f.1 t) {a : V} (ha : a∈A.sites) :
    ∃ c ∈ C.sites, a=c+t := by
  classical
  obtain ⟨p,hp⟩ := af (fun x => if x.val=a then 1 else 0)
  have htop : A.support p=1 := by
    apply le_antisymm (high_le fun i => by rw [hp i]; split <;> norm_num)
    have e := hp ⟨a,ha⟩
    simp at e
    exact e.symm.trans_le (A.read_le_support p ha)
  have only (x : V) (hx : x∈(A.face p).sites) : x=a := by
    obtain ⟨hx,eq⟩ := mem_filter.mp hx
    have e := hp ⟨x,hx⟩
    by_contra no
    simp [no] at e
    linarith
  obtain ⟨c,hc⟩ := (C.face p).exists_site
  refine ⟨c,C.face_subset p hc,?_⟩
  have test (f : Probe V) : f.read a = (C.face p).support f +f.1 t := by
    obtain ⟨n,ae,ce⟩ := ((A.leading p f).and (C.leading p f)).exists
    have h := gap ((n:ℚ) • p+f)
    rw [ae,ce] at h
    have single := (A.face p).support_constant (fun x hx => congrArg f.read (only x hx))
    rw [single] at h
    change _=_+((n:ℚ)*p.1 t+f.1 t) at h
    linarith only [h,congrArg (fun z : ℚ => (n:ℚ)*z) (gap p)]
  have bounds (f : Probe V) : f.read c+f.1 t≤f.read a := by
    rw [test]
    linarith [(C.face p).read_le_support f hc]
  have hf : ∀ q : Module.Dual ℚ V, q (a-(c+t))=0 := by
    intro q
    have pos := bounds (q,0)
    have neg := bounds (-q,0)
    simp [Probe.read] at pos neg
    simp only [map_sub,map_add]
    linarith
  exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℚ _).mp hf)
end SidonSetSystems
