module

public import conjectures.SplitMatroidFlags.Exchange
import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

namespace SplitMatroidFlags

open Finset

variable {E : Type} [DecidableEq E]

/-- The span of the oriented incidence vectors. Either orientation gives the same space. -/
def directions (P : Finset (E × E)) := Submodule.span ℝ {z | ∃ e ∈ P, z = unit e.2 - unit e.1}

lemma edge_mem {P : Finset (E × E)} {e : E × E} (he : e ∈ P) :
    unit e.2 - unit e.1 ∈ directions P := Submodule.subset_span ⟨e,he,rfl⟩

private def star (A : Finset E) (r : E → E) :=
  Submodule.span ℝ (Set.range fun i : A => unit (i : E) - unit (r i))

private lemma star_rank {A : Finset E} {r : E → E} (hr : ∀ i ∈ A, r i ∉ A) :
    Module.finrank ℝ (star A r) = A.card := by
  have ind : LinearIndependent ℝ (fun i : A => unit (i : E) - unit (r i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro w h i
    have at_i (j : A) : (unit (j : E) - unit (r j)) i = if j = i then 1 else 0 := by
      have ne : r j ≠ i := fun e => hr j j.property (e ▸ i.property)
      by_cases eq : j = i
      · subst j
        simp [unit,ne]
      · have ne' : (j : E) ≠ i := fun he => eq (Subtype.ext he)
        simp [unit,ne,ne',eq]
    have eq := congrFun h (i : E)
    simp only [Pi.zero_apply] at eq
    simpa [at_i] using eq
  exact (finrank_span_eq_card ind).trans (Fintype.card_coe A)

structure Components (P : Finset (E × E)) (r : E → E) : Prop where
  idempotent : ∀ i, r (r i) = r i
  constant : ∀ e ∈ P, r e.1 = r e.2
  path : ∀ i, unit i - unit (r i) ∈ directions P

lemma Components.rank [Fintype E] {P : Finset (E × E)} {r : E → E} (h : Components P r) :
    Module.finrank ℝ (directions P) = (univ.filter (fun i => r i ≠ i)).card := by
  let A := univ.filter fun i => r i ≠ i
  have outside i : r i ∉ A := by simp [A,h.idempotent]
  have into (i : E) : unit i - unit (r i) ∈ star A r := by
    by_cases he : r i = i
    · simp [he]
    · exact Submodule.subset_span ⟨⟨i,mem_filter.mpr ⟨mem_univ _,he⟩⟩,rfl⟩
  have eq : directions P = star A r := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨e,he,rfl⟩
      have hh := (star A r).sub_mem (into e.2) (into e.1)
      rwa [h.constant e he,sub_sub_sub_cancel_right] at hh
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact h.path i
  rw [eq,star_rank (fun i _ => outside i)]

/-- Merge the two classes joined by an edge. -/
def join (e : E × E) (r : E → E) (i : E) := if r i = r e.2 then r e.1 else r i

lemma Components.join {P : Finset (E × E)} {r : E → E} (h : Components P r) (e : E × E) :
    Components (insert e P) (join e r) := by
  let D := directions (insert e P)
  have mono : directions P ≤ D := Submodule.span_mono (by
    rintro z ⟨f,hf,rfl⟩
    exact ⟨f,mem_insert_of_mem hf,rfl⟩)
  have link : unit (r e.2) - unit (r e.1) ∈ D := by
    have he := edge_mem (mem_insert_self e P)
    have hh := D.add_mem (D.sub_mem he (mono (h.path e.2))) (mono (h.path e.1))
    convert hh using 1
    abel
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases he : r i = r e.2
    · simp [SplitMatroidFlags.join,he,h.idempotent]
    · simp [SplitMatroidFlags.join,he,h.idempotent]
  · intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · simp [SplitMatroidFlags.join]
    · simp [SplitMatroidFlags.join,h.constant f hf]
  · intro i
    by_cases he : r i = r e.2
    · have hh := D.add_mem (mono (h.path i)) (he.symm ▸ link)
      simpa [SplitMatroidFlags.join,he] using hh
    · simpa [SplitMatroidFlags.join,he] using mono (h.path i)

def roots (edges : List (E × E)) : E → E :=
  edges.foldr join id

lemma roots_correct (edges : List (E × E)) : Components edges.toFinset (roots edges) := by
  induction edges with
  | nil => exact ⟨fun _ => rfl,by simp,by simp [roots]⟩
  | cons e es ih => simpa [roots] using ih.join e

end SplitMatroidFlags
