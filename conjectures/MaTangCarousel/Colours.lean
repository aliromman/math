module

public import conjectures.MaTangCarousel.Statement
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Fin2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section
namespace MaTangCarousel
open Finset

def forward (a b : Fin 3) : Bool := (a.val+1)%3==b.val

/-- Three equal transitive parts, oriented cyclically. -/
def threeParts (m : ℕ) : Tournament (Fin 3 × Fin m) where
  arc x y := forward x.1 y.1 || (x.1==y.1 && decide (x.2<y.2))
  loopless := by
    rintro ⟨i,t⟩
    fin_cases i <;> simp [forward]
  orientation := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases eq : i=j
    · subst j
      have ne : x≠y := by rintro rfl; exact h rfl
      have hh : decide (x<y) = !decide (y<x) := by rcases lt_or_gt_of_ne ne with l|l <;> simp [l,l.asymm]
      fin_cases i <;> simpa [forward] using hh
    · fin_cases i <;> fin_cases j <;> simp_all [forward]

def ascents {l : ℕ} {α : Type*} [LT α] [DecidableLT α] (r : Fin l→α) (i : Fin l) : Bool :=
  decide (r i<r (next i))

def colourTest {l : ℕ} (b : Fin l→Bool) (c : Fin l→Fin 3) : Bool :=
  decide (∀ i,(forward (c i) (c (next i)) || (c i==c (next i) && b i))=true)

def colours {l : ℕ} (b : Fin l→Bool) : ℕ :=
  ∑ c : Fin l→Fin 3, if colourTest b c then 1 else 0

theorem count_colours (l m : ℕ) :
    homCount (threeParts m) l = ∑ r : Fin l→Fin m,colours (ascents r) := by
  let e := Equiv.arrowProdEquivProdArrow (Fin l) (fun _ ↦ Fin 3) (fun _ ↦ Fin m)
  unfold homCount
  rw [←e.symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  rfl

theorem colours_mono {l : ℕ} {b b' : Fin l→Bool}
    (h : ∀ i,b i=true → b' i=true) : colours b≤colours b' := by
  apply sum_le_sum
  intro c _
  by_cases H : colourTest b c=true
  · have hc : colourTest b' c=true := by
      simp only [colourTest,decide_eq_true_eq,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at H ⊢
      exact fun i ↦ (H i).imp_right (fun z ↦ ⟨z.1,h i z.2⟩)
    simp [H,hc]
  · simp [H]

private theorem three_colours : ∀ b : Fin 3→Bool, colours b = if ∀ i,b i=true then 6 else 3 := by
  decide +kernel

theorem triangle_count (m : ℕ) : homCount (threeParts m) 3=3*m^3 := by
  rw [count_colours]
  have C (r : Fin 3→Fin m) : colours (ascents r)=3 := by
    rw [three_colours,ite_eq_right_iff]
    intro all
    have a : r 0<r 1 := of_decide_eq_true (all 0)
    have b : r 1<r 2 := of_decide_eq_true (all 1)
    have c : r 2<r 0 := of_decide_eq_true (all 2)
    exact False.elim ((lt_trans a b).asymm c)
  simp [C,Nat.mul_comm]

end MaTangCarousel
