module

public import conjectures.SidonSetSystems.Support
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith

@[expose] public section
namespace SidonSetSystems
open Finset
open scoped Classical
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Equality of the support functions of two sums. -/
def Balanced (A B C D : Figure V) : Prop :=
  ∀ f : Probe V, A.support f+B.support f=C.support f+D.support f

theorem Balanced.face {A B C D : Figure V} (h : Balanced A B C D) (p : Probe V) :
    Balanced (A.face p) (B.face p) (C.face p) (D.face p) := by
  intro q
  obtain ⟨n,⟨⟨ha,hb⟩,hc⟩,hd⟩ := ((((A.leading p q).and (B.leading p q)).and (C.leading p q)).and
    (D.leading p q)).exists
  have e := h ((n:ℚ) • p+q)
  rw [ha,hb,hc,hd] at e
  linarith only [e,congrArg (fun z : ℚ => (n:ℚ)*z) (h p)]

namespace Figure

@[simp] theorem read_neg (f : Probe V) (x : V) : (-f).read x= -f.read x := by
  simp [Probe.read,neg_add_rev,add_comm]

theorem flat_directions (A : Figure V) (f : Probe V) {p : V} (hp : p∈A.sites)
    (h : ∀ v∈A.directions, f.1 v=0) : ∀ x∈A.sites, f.read x=f.read p := by
  intro x hx
  have eq := h (x-p) (A.sub_mem hx hp)
  simp only [map_sub,sub_eq_zero] at eq
  simp [Probe.read,eq]

theorem opposite_faces (A : Figure V) (f : Probe V) {v : V} (hv : v∈A.directions)
    (hf : f.1 v≠0) : Disjoint (A.face f).sites (A.face (-f)).sites := by
  apply disjoint_left.mpr
  intro x hp hn
  obtain ⟨_,hp⟩ := mem_filter.mp hp
  obtain ⟨_,hn⟩ := mem_filter.mp hn
  rw [read_neg] at hn
  have e (j : A.sites) : f.read j=f.read x := by
    have jh := A.read_le_support f j.property
    have jn := A.read_le_support (-f) j.property
    rw [read_neg] at jn
    linarith
  exact hf (A.constant_on (fun i j => (e i).trans (e j).symm) v hv)

theorem disjoint_directions {A B C : Figure V} (h : A.Free)
    (hb : B.sites⊆A.sites) (hc : C.sites⊆A.sites) (d : Disjoint B.sites C.sites) :
    Disjoint B.directions C.directions := by
  apply Submodule.disjoint_def.mpr
  intro v hvB hvC
  by_contra hv
  obtain ⟨q,hq⟩ := Module.Projective.exists_dual_ne_zero ℚ hv
  obtain ⟨f,hf⟩ := h (fun x => if x.val∈B.sites then q x else 0)
  have b (x : B.sites) : Probe.read (f.1-q,f.2) x=0 := by
    have eq := hf ⟨x,hb x.2⟩
    simp only [x.2,ite_true,Probe.read] at eq ⊢
    simp only [LinearMap.sub_apply]
    linarith
  have c (x : C.sites) : f.read x=0 := by
    have out : x.val∉B.sites := fun mem => disjoint_left.mp d mem x.2
    simpa [out] using hf ⟨x,hc x.2⟩
  have one := B.constant_on (fun i j => (b i).trans (b j).symm) v hvB
  have two := C.constant_on (fun i j => (c i).trans (c j).symm) v hvC
  change f.1 v-q v=0 at one
  exact hq (by linarith)

noncomputable def width (A : Figure V) (f : Module.Dual ℚ V) :=
  A.support (f,0)+A.support (-((f,0):Probe V))

theorem width_nonneg (A : Figure V) (f : Module.Dual ℚ V) : 0≤A.width f := by
  obtain ⟨a,ha⟩ := A.exists_site
  have u := A.read_le_support (f,0) ha
  have v := A.read_le_support (-((f,0):Probe V)) ha
  rw [read_neg] at v
  unfold width
  linarith

theorem width_zero_iff (A : Figure V) (f : Module.Dual ℚ V) :
    A.width f=0 ↔ ∀ v ∈ A.directions, f v=0 := by
  constructor
  · intro h
    apply A.constant_on (f:=(f,0))
    intro i j
    have hi := A.read_le_support (f,0) i.2
    have hj := A.read_le_support (-((f,0):Probe V)) j.2
    have gi := A.read_le_support (-((f,0):Probe V)) i.2
    have gj := A.read_le_support (f,0) j.2
    rw [read_neg] at hj gi
    dsimp only [width] at h
    linarith
  · intro h
    obtain ⟨a,ha⟩ := A.exists_site
    have flat := A.flat_directions (f,0) ha h
    have neg (x : V) (hx : x∈A.sites) : Probe.read (-((f,0):Probe V)) x= -Probe.read (f,0) a := by
      rw [read_neg,flat x hx]
    unfold width
    rw [A.support_constant flat,A.support_constant neg,add_neg_cancel]

end Figure

theorem Balanced.directions {A B C D : Figure V} (h : Balanced A B C D) :
    A.directions⊔B.directions=C.directions⊔D.directions := by
  have side (A B C D : Figure V) (bal : Balanced A B C D) :
      A.directions≤C.directions⊔D.directions := by
    intro v hv
    by_contra no
    obtain ⟨f,non,zero⟩ := Submodule.exists_dual_map_eq_bot_of_notMem no inferInstance
    have flat (x : V) (hx : x∈C.directions⊔D.directions) : f x=0 := by
      have mem : f x∈(C.directions⊔D.directions).map f := ⟨x,hx,rfl⟩
      rwa [zero,Submodule.mem_bot] at mem
    have zc := (C.width_zero_iff f).mpr fun x hx => flat x ((show C.directions≤_ from le_sup_left) hx)
    have zd := (D.width_zero_iff f).mpr fun x hx => flat x ((show D.directions≤_ from le_sup_right) hx)
    have eq : A.width f+B.width f=C.width f+D.width f := by
      unfold Figure.width
      linarith only [bal (f,0),bal (-((f,0):Probe V))]
    have za : A.width f=0 := by linarith [A.width_nonneg f,B.width_nonneg f]
    exact non ((A.width_zero_iff f).mp za v hv)
  apply le_antisymm
  · exact sup_le (side A B C D h) (side B A C D (fun f => by rw [add_comm]; exact h f))
  · exact sup_le (side C D A B (fun f => (h f).symm))
      (side D C A B (fun f => by rw [add_comm]; exact (h f).symm))

end SidonSetSystems
