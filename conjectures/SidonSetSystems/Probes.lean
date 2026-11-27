module

public import conjectures.SidonSetSystems.Corners
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Data.Rat.Denumerable
import Mathlib.Tactic.Linarith

@[expose] public section
namespace SidonSetSystems
open Finset
open scoped Classical

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- A linear reading with an arbitrary constant offset. -/
abbrev Probe := Module.Dual ℚ V × ℚ

variable {V}
def Probe.read (f : Probe V) (x : V) : ℚ := f.1 x + f.2

@[simp] theorem Probe.read_add (f g : Probe V) (x : V) : (f+g).read x=f.read x+g.read x := by
  simp [Probe.read]
  ring

@[simp] theorem Probe.read_zero (x : V) : (0 : Probe V).read x=0 := by simp [Probe.read]

theorem Probe.read_sum {ι : Type*} (s : Finset ι) (f : ι → Probe V) (x : V) :
    (∑ i ∈ s, f i).read x=∑ i ∈ s, (f i).read x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi,ih]

variable (V) in
/-- A nonempty finite set of points. -/
@[ext] structure Figure where
  sites : Finset V
  exists_site : sites.Nonempty

namespace Figure
variable (A : Figure V)

instance : Nonempty A.sites := ⟨⟨A.exists_site.choose,A.exists_site.choose_spec⟩⟩

/-- The maximum value of an affine reading on these points. -/
noncomputable def support (f : Probe V) : ℚ := high (fun x : A.sites => f.read x)

theorem support_congr {f g : Probe V} (h : ∀ x ∈ A.sites, f.read x=g.read x) :
    A.support f=A.support g := congrArg high (funext fun x : A.sites => h x x.2)

/-- Every assignment of readings to the vertices extends to an affine reading. -/
def Free : Prop := ∀ w : A.sites → ℚ, ∃ f : Probe V, ∀ x : A.sites, f.read x=w x

/-- The subspace of differences of points of this figure. -/
def directions : Submodule ℚ V :=
  Submodule.span ℚ {v | ∃ x∈A.sites, ∃ y∈A.sites, x-y=v}

theorem sub_mem {x y : V} (hx : x∈A.sites) (hy : y∈A.sites) : x-y∈A.directions :=
  Submodule.subset_span ⟨x,hx,y,hy,rfl⟩

theorem constant_on {f : Probe V} (h : ∀ x y : A.sites, f.read x=f.read y) :
    ∀ v∈A.directions, f.1 v=0 := by
  suffices A.directions ≤ LinearMap.ker f.1 by exact fun _ hv => this hv
  apply Submodule.span_le.mpr
  rintro v ⟨x,hx,y,hy,rfl⟩
  change f.1 (x-y)=0
  rw [map_sub,sub_eq_zero]
  have := h ⟨x,hx⟩ ⟨y,hy⟩
  simpa only [Probe.read,add_left_inj] using this

theorem probe_of_outside {v : V} (hv : v∉A.directions) :
    ∃ f : Probe V, 0<f.1 v ∧ ∀ x∈A.sites, f.read x=0 := by
  obtain ⟨f,hf,zero⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  obtain ⟨x,hx⟩ := A.exists_site
  let g := (f v)⁻¹ • f
  have h1 : g v=1 := by simp [g,hf]
  refine ⟨(g, -g x),by change 0<g v; rw [h1]; decide,?_⟩
  intro y hy
  have hz : f (y-x)∈A.directions.map f := ⟨_,A.sub_mem hy hx,rfl⟩
  rw [zero,Submodule.mem_bot,map_sub,sub_eq_zero] at hz
  simp [Probe.read,g,hz]

end Figure

/-- A vector that avoids each of three subspaces which do not contain the given subspace. -/
theorem avoid_three (A : Submodule ℚ V) (W : Fin 3 → Submodule ℚ V) (h : ∀i, ¬A≤W i) :
    ∃ v ∈ A, ∀ i, v∉W i := by
  classical
  let P (i : Fin 3) := (W i).comap A.subtype
  have hp (i : Fin 3) : P i ≠ ⊤ := by
    intro he
    apply h i
    intro v hv
    have : (⟨v,hv⟩ : A)∈P i := by rw [he]; exact Submodule.mem_top
    exact this
  have all := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt univ P hp (by
    rw [ENat.card_eq_top_of_infinite]
    exact WithTop.coe_lt_top _)
  obtain ⟨v,_,hv⟩ := Set.exists_of_ssubset all
  refine ⟨v,v.2,fun i hi => hv ?_⟩
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨mem_univ i,hi⟩⟩

end SidonSetSystems
