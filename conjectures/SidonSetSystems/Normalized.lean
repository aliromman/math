module

public import conjectures.SidonSetSystems.Realizations
public import conjectures.SidonSetSystems.Hyperspace
public import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace SidonSetSystems
open Finset
open scoped Classical

noncomputable def listing (d : ℕ) (A : Finset ℕ) : Fin d→ℕ :=
  if h : (A.erase 0).card=d then (A.erase 0).orderEmbOfFin h else fun _ => 0

theorem normalized_spec {d n : ℕ} {A : Finset ℕ} (ha : A∈shapes (d+1) n) :
    shape (listing d A)=A ∧ ∀ i, listing d A i<n := by
  obtain ⟨hA,h0⟩ := mem_filter.mp ha
  obtain ⟨sub,card⟩ := mem_powersetCard.mp hA
  have erase : (A.erase 0).card=d := by rw [card_erase_of_mem h0,card]; omega
  have val (i : Fin d) : listing d A i∈A.erase 0 := by
    simp only [listing,dite_eq_left erase]
    exact orderEmbOfFin_mem ..
  refine ⟨?_,fun i => mem_range.mp (sub (mem_of_mem_erase (val i)))⟩
  ext a
  rw [mem_shape]
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | none => exact h0
    | some i => exact mem_of_mem_erase (val i)
  · intro mem
    by_cases zero : a=0
    · exact ⟨none,zero.symm⟩
    · obtain ⟨i,hi⟩ := (Finset.range_orderEmbOfFin (A.erase 0) erase).ge (mem_erase.mpr ⟨zero,mem⟩)
      exact ⟨some i,by simpa [digit,listing,erase] using hi⟩

def Allowed {d : ℕ} (v : Fin d→ℕ) : Prop :=
  ∀ p : Pattern d, ∀ i : Fin 4, (fun j => (v j:ℚ))∈(p.row i).range → Function.Surjective (p.row i)

noncomputable def good (d n : ℕ) : Finset (Finset ℕ) :=
  (shapes (d+1) n).filter (fun A => Allowed (listing d A))

/-- Only a fixed number of proper rational hyperplanes need to be discarded. -/
theorem count_good (m n : ℕ) : (shapes (m+2) n).card ≤ (good (m+1) n).card+
    Fintype.card (Pattern (m+1) × Fin 4) * n^m := by
  classical
  let I := Pattern (m+1) × Fin 4
  let rows (a : I) : Finset (Fin (m+1)→Fin n) :=
    if Function.Surjective (a.1.row a.2) then ∅ else univ.filter fun v =>
      (fun i => ((v i).val : ℚ))∈(a.1.row a.2).range
  have size (a : I) : (rows a).card≤n^m := by
    dsimp [rows]
    split
    · simp
    · rename_i h
      exact proper_row_count m n _ (fun top => h (LinearMap.range_eq_top.mp top))
  let tab (a : I) := (rows a).image (fun v => shape (fun i => (v i).val))
  let extras := univ.biUnion tab
  have cover : shapes (m+2) n ⊆ good (m+1) n ∪ extras := by
    intro A ha
    by_cases ok : Allowed (listing (m+1) A)
    · exact mem_union_left _ (mem_filter.mpr ⟨ha,ok⟩)
    · simp only [Allowed,not_forall] at ok
      obtain ⟨p,i,mem,notSur⟩ := ok
      obtain ⟨restore,bounds⟩ := normalized_spec ha
      let v : Fin (m+1)→Fin n := fun j => ⟨listing (m+1) A j,bounds j⟩
      have rv : v∈rows (p,i) := by simpa [rows,notSur,v] using mem
      exact mem_union_right _ (mem_biUnion.mpr ⟨(p,i),mem_univ _,mem_image.mpr ⟨v,rv,restore⟩⟩)
  have bound : extras.card≤Fintype.card I*n^m := by
    refine (card_biUnion_le ..).trans ?_
    calc
      _ ≤ ∑ _i : I, n^m := sum_le_sum fun a _ => card_image_le.trans (size a)
      _ = _ := by simp
  exact (card_le_card cover).trans ((card_union_le _ _).trans (Nat.add_le_add_left bound _))

end SidonSetSystems
