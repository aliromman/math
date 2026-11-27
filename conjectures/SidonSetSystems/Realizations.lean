module

public import conjectures.SidonSetSystems.Patterns
import Mathlib.Tactic.Linarith

@[expose] public section
namespace SidonSetSystems
open Finset Module
open scoped Classical Pointwise
variable {d : ℕ}

def digit (v : Fin d → ℕ) : Slot d → ℕ
  | none => 0
  | some i => v i

def shape (v : Fin d → ℕ) : Finset ℕ := univ.image (digit v)

theorem mem_shape (v : Fin d → ℕ) (z : ℕ) : z∈shape v ↔ ∃ j, digit v j=z := by simp [shape]

def rationalRows (v : Fin 4 → Fin d → ℕ) : Entries d := fun i j => (v i j:ℚ)

theorem mark_rows (v : Fin 4 → Fin d → ℕ) (i : Fin 4) (j : Slot d) :
    Pattern.mark i j (rationalRows v) = digit (v i) j := by cases j <;> rfl

/-- The equality of two finite sumsets gives matchings of all the entries in both directions. -/
theorem realize_pattern (v : Fin 4 → Fin d → ℕ)
    (eq : shape (v 0)+shape (v 1)=shape (v 2)+shape (v 3)) :
    ∃ p : Pattern d, rationalRows v∈p.solutions := by
  classical
  have direct (i j k l : Fin 4) (same : shape (v i)+shape (v j)=shape (v k)+shape (v l)) (e : Edge d) :
      ∃ b : Edge d, Pattern.pair i j e (rationalRows v)=Pattern.pair k l b (rationalRows v) := by
    have mem : digit (v i) e.1+digit (v j) e.2 ∈ shape (v k)+shape (v l) := by
      rw [←same]
      exact mem_add.mpr ⟨_,(mem_shape ..).mpr ⟨_,rfl⟩,_,(mem_shape ..).mpr ⟨_,rfl⟩,rfl⟩
    obtain ⟨a,ha,b,hb,ab⟩ := mem_add.mp mem
    obtain ⟨u,rfl⟩ := (mem_shape ..).mp ha
    obtain ⟨s,rfl⟩ := (mem_shape ..).mp hb
    refine ⟨(u,s),?_⟩
    simp only [Pattern.pair,LinearMap.add_apply,mark_rows]
    exact_mod_cast ab.symm
  choose F hF using direct 0 1 2 3 eq
  choose G hG using direct 2 3 0 1 eq.symm
  exact ⟨(F,G),(Pattern.mem_solutions ..).mpr ⟨hF,hG⟩⟩

namespace Pattern
variable (p : Pattern d) (v : Fin 4 → Fin d → ℕ) (mem : rationalRows v∈p.solutions)

private theorem value_of_site (r : Fin 4) {a : Module.Dual ℚ p.solutions} (ha : a∈(p.figure r).sites) :
    ∃ z∈shape (v r), a ⟨rationalRows v,mem⟩=(z:ℚ) := by
  obtain ⟨i,rfl⟩ := (mem_figure ..).mp ha
  exact ⟨digit (v r) i,(mem_shape ..).mpr ⟨i,rfl⟩,mark_rows v r i⟩

private theorem site_of_value (r : Fin 4) {z : ℕ} (hz : z∈shape (v r)) :
    ∃ a∈(p.figure r).sites, a ⟨rationalRows v,mem⟩=(z:ℚ) := by
  obtain ⟨i,rfl⟩ := (mem_shape ..).mp hz
  exact ⟨p.site r i,site_mem ..,mark_rows v r i⟩

include mem

theorem equal_of_translates {r s : Fin 4} (trans : Translates (p.figure r) (p.figure s)) :
    shape (v r)=shape (v s) := by
  obtain ⟨t,ac,ca⟩ := trans
  let x : p.solutions := ⟨rationalRows v,mem⟩
  have nonneg (i : Fin 4) (a : Module.Dual ℚ p.solutions) (ha : a∈(p.figure i).sites) : 0≤a x := by
    obtain ⟨z,_,h⟩ := p.value_of_site v mem i ha
    rw [show a x=(z:ℚ) from h]
    positivity
  obtain ⟨c,hc,ec⟩ := ac 0 (p.zero_mem r)
  obtain ⟨a,ha,ea⟩ := ca 0 (p.zero_mem s)
  have l := LinearMap.congr_fun ea x
  have u := LinearMap.congr_fun ec x
  simp only [LinearMap.zero_apply,LinearMap.add_apply] at l u
  have tx : t x=0 := by linarith [nonneg s c hc,nonneg r a ha]
  ext z
  constructor
  · intro hz
    obtain ⟨a,ha,eq⟩ := p.site_of_value v mem r hz
    obtain ⟨c,hc,e⟩ := ac a ha
    obtain ⟨m,hm,ce⟩ := p.value_of_site v mem s hc
    have co := LinearMap.congr_fun e x
    change a x=c x+t x at co
    rw [tx,add_zero,ce,eq] at co
    exact (show z=m by exact_mod_cast co) ▸ hm
  · intro hz
    obtain ⟨c,hc,eq⟩ := p.site_of_value v mem s hz
    obtain ⟨a,ha,e⟩ := ca c hc
    obtain ⟨m,hm,ae⟩ := p.value_of_site v mem r ha
    have co := LinearMap.congr_fun e x
    change a x=c x+t x at co
    rw [tx,add_zero,eq,ae] at co
    exact (show m=z by exact_mod_cast co) ▸ hm

/-- In a nontrivial collision of generic shapes, each single row determines the full solution. -/
theorem row_controls (sur : ∀ r, Function.Surjective (p.row r))
    (bad : Bad (shape (v 0)) (shape (v 1)) (shape (v 2)) (shape (v 3))) :
    ∀ r, Function.Injective (p.row r) := by
  let F := p.figure
  have free (i : Fin 4) : (F i).Free := p.free_of_surjective i (sur i)
  have card (i : Fin 4) : (F i).sites.card=d+1 := p.card_of_surjective i (sur i)
  have dim (i : Fin 4) : finrank ℚ (F i).directions=d := by
    have h := (F i).free_dimension (free i)
    rw [card] at h
    omega
  have equal : (F 0).directions=(F 1).directions := by
    by_contra diff
    have choice := separate_simplices (F 0) (F 1) (F 2) (F 3) p.balanced
      (free 0) (free 1) (free 2) (free 3) (by rw [card,card]) (by rw [card,card]) (by rw [card,card]) diff
    exact bad.2 (choice.imp
      (fun h => ⟨p.equal_of_translates v mem h.1,p.equal_of_translates v mem h.2⟩)
      (fun h => ⟨p.equal_of_translates v mem h.1,p.equal_of_translates v mem h.2⟩))
  have joint := p.balanced.directions
  change (F 0).directions⊔(F 1).directions=(F 2).directions⊔(F 3).directions at joint
  rw [←equal,sup_idem] at joint
  have all (i : Fin 4) : (F i).directions=(F 0).directions := by
    apply Submodule.eq_of_le_of_finrank_eq _ ((dim i).trans (dim 0).symm)
    fin_cases i
    · exact le_rfl
    · exact equal.ge
    · rw [joint]; exact le_sup_left
    · rw [joint]; exact le_sup_right
  intro r x y he
  let q : Module.Dual ℚ (Module.Dual ℚ p.solutions) := Module.Dual.eval ℚ _ (x-y)
  have flat (a : (F r).sites) : q a=0 := by
    obtain ⟨j,e⟩ := (mem_figure ..).mp a.property
    rw [←e]
    cases j with
    | none => simp
    | some j =>
      change x.val r j-y.val r j=0
      exact sub_eq_zero.mpr (congrFun he j)
  have ann := (F r).constant_on (f:=(q,0)) (fun i j => by simp [Probe.read,flat])
  apply Subtype.ext
  funext i j
  have dmem := (F i).sub_mem (p.site_mem i (some j)) (p.zero_mem i)
  rw [sub_zero,all i,←all r] at dmem
  exact sub_eq_zero.mp (ann _ dmem)

end Pattern
end SidonSetSystems
