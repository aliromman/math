module

public import conjectures.SidonSetSystems.Simplices
public import conjectures.SidonSetSystems.CountingInput
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith

@[expose] public section
namespace SidonSetSystems
open Finset Module
open scoped Classical Pointwise

abbrev Slot (d : ℕ) := Option (Fin d)
abbrev Edge (d : ℕ) := Slot d × Slot d
abbrev Pattern (d : ℕ) := (Edge d → Edge d) × (Edge d → Edge d)
abbrev Entries (d : ℕ) := Fin 4 → Fin d → ℚ

namespace Pattern
variable {d : ℕ}

def mark (r : Fin 4) : Slot d → Module.Dual ℚ (Entries d)
  | none => 0
  | some i => (LinearMap.proj i : (Fin d → ℚ) →ₗ[ℚ] ℚ).comp (LinearMap.proj r)

def pair (r s : Fin 4) (e : Edge d) : Module.Dual ℚ (Entries d) := mark r e.1+mark s e.2

/-- Coordinates that satisfy every matched pair equality in both directions. -/
def solutions (p : Pattern d) : Submodule ℚ (Entries d) :=
  (⨅ e, (pair 0 1 e-pair 2 3 (p.1 e)).ker) ⊓
  (⨅ e, (pair 2 3 e-pair 0 1 (p.2 e)).ker)

theorem mem_solutions (p : Pattern d) (x : Entries d) : x∈solutions p ↔
    (∀ e, pair 0 1 e x=pair 2 3 (p.1 e) x) ∧ (∀ e, pair 2 3 e x=pair 0 1 (p.2 e) x) := by
  simp [solutions,Submodule.mem_iInf,LinearMap.mem_ker,sub_eq_zero]

def row (p : Pattern d) (r : Fin 4) : solutions p →ₗ[ℚ] (Fin d → ℚ) :=
  (LinearMap.proj r).comp (solutions p).subtype

def site (p : Pattern d) (r : Fin 4) (i : Slot d) : Module.Dual ℚ (solutions p) :=
  (mark r i).comp (solutions p).subtype

@[simp] theorem site_none (p : Pattern d) (r : Fin 4) : site p r none=0 := by ext; rfl

noncomputable def figure (p : Pattern d) (r : Fin 4) : Figure (Module.Dual ℚ (solutions p)) where
  sites := univ.image (site p r)
  exists_site := ⟨site p r none,mem_image_of_mem _ (mem_univ _)⟩

theorem mem_figure (p : Pattern d) (r : Fin 4) (a : Module.Dual ℚ (solutions p)) :
    a∈(figure p r).sites ↔ ∃ i, site p r i=a := by simp [figure]

theorem site_mem (p : Pattern d) (r : Fin 4) (i : Slot d) : site p r i∈(figure p r).sites :=
  (mem_figure p r _).mpr ⟨i,rfl⟩

theorem zero_mem (p : Pattern d) (r : Fin 4) : 0∈(figure p r).sites := by simpa using site_mem p r none

theorem forward (p : Pattern d) (e : Edge d) :
    site p 0 e.1+site p 1 e.2=site p 2 (p.1 e).1+site p 3 (p.1 e).2 := by
  ext x
  exact ((mem_solutions p x).mp x.2).1 e

theorem backward (p : Pattern d) (e : Edge d) :
    site p 2 e.1+site p 3 e.2=site p 0 (p.2 e).1+site p 1 (p.2 e).2 := by
  ext x
  exact ((mem_solutions p x).mp x.2).2 e

theorem balanced (p : Pattern d) : Balanced (figure p 0) (figure p 1) (figure p 2) (figure p 3) := by
  intro f
  have side (i j k l : Fin 4) (dest : Edge d → Edge d)
      (rule : ∀ e : Edge d, site p i e.1+site p j e.2=site p k (dest e).1+site p l (dest e).2) :
      (figure p i).support f+(figure p j).support f≤(figure p k).support f+(figure p l).support f := by
    obtain ⟨a,ha,ea⟩ := (figure p i).support_attained f
    obtain ⟨b,hb,eb⟩ := (figure p j).support_attained f
    obtain ⟨u,rfl⟩ := (mem_figure ..).mp ha
    obtain ⟨v,rfl⟩ := (mem_figure ..).mp hb
    let e : Edge d := (u,v)
    have he := congrArg f.1 (rule e)
    have hc := (figure p k).read_le_support f (site_mem p k (dest e).1)
    have hd := (figure p l).read_le_support f (site_mem p l (dest e).2)
    simp only [map_add] at he
    simp only [Probe.read] at ea eb hc hd
    change f.1 (site p i u)+f.1 (site p j v)=_ at he
    linarith
  exact le_antisymm (side 0 1 2 3 p.1 (forward p)) (side 2 3 0 1 p.2 (backward p))

theorem free_of_surjective (p : Pattern d) (r : Fin 4) (sur : Function.Surjective (row p r)) :
    (figure p r).Free := by
  classical
  intro w
  let b := w ⟨0,zero_mem p r⟩
  obtain ⟨x,hx⟩ := sur (fun i => w ⟨site p r (some i),site_mem ..⟩-b)
  refine ⟨(Module.Dual.eval ℚ _ x,b),?_⟩
  rintro ⟨y,hy⟩
  obtain ⟨i,rfl⟩ := (mem_figure ..).mp hy
  cases i with
  | none => simp [Probe.read,b]
  | some i =>
    have h := congrFun hx i
    change x.val r i=_ at h
    change x.val r i+b=_
    linarith

theorem card_of_surjective (p : Pattern d) (r : Fin 4) (sur : Function.Surjective (row p r)) :
    (figure p r).sites.card=d+1 := by
  classical
  have inj : Function.Injective (site p r) := by
    intro a b eq
    let w : Slot d→ℚ := fun j => if j=a then 1 else 0
    obtain ⟨x,hx⟩ := sur (fun j => w (some j)-w none)
    have get (i : Slot d) : site p r i x = w i - w none := by
      cases i with
      | none => simp [site,mark]
      | some j => exact congrFun hx j
    have vals := LinearMap.congr_fun eq x
    rw [get,get] at vals
    by_contra ne
    simp [w] at vals
    exact ne vals.symm
  simp [figure,card_image_of_injective _ inj,Fintype.card_option]

end Pattern
end SidonSetSystems
