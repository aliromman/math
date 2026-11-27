module

public import conjectures.KurzBanzhaf.Profiles

@[expose] public section
namespace KurzBanzhaf
open Finset

namespace Seeds

abbrev Box := ℕ × ℕ × ℕ × ℕ

private def label (n a b i : ℕ) : ℕ :=
  if i+1=n then 3 else if i<a then 0 else if i<b then 1 else 2

private def occupied {n : ℕ} (a b : ℕ) (S : Finset (Fin n)) (j : ℕ) :=
  (S.filter fun (i : Fin n) ↦ label n a b i.val=j).card

private def fits {n} (a b : ℕ) (S : Finset (Fin n)) (x : Box) : Prop :=
  occupied a b S 0≤x.1 ∧ occupied a b S 1≤x.2.1 ∧
    occupied a b S 2≤x.2.2.1 ∧ occupied a b S 3≤x.2.2.2

private instance {n} (a b : ℕ) (S : Finset (Fin n)) (x : Box) : Decidable (fits a b S x) := by
  unfold fits
  infer_instance

private def region {n} (a b : ℕ) (boxes : List Box) (S : Finset (Fin n)) : Prop :=
  ∃ x ∈ boxes, fits a b S x

private instance {n} (a b : ℕ) (bs : List Box) (S : Finset (Fin n)) : Decidable (region a b bs S) := by
  unfold region
  infer_instance

private def rule (n a b : ℕ) (bs : List Box)
    (lo : region a b bs (∅ : Finset (Fin n))) (hi : ¬region a b bs (univ : Finset (Fin n))) :
    VotingGame (Fin n) where
  losing := univ.filter (region a b bs)
  empty_loses := mem_filter.mpr ⟨mem_univ _,lo⟩
  full_wins mem := hi (mem_filter.mp mem).2
  down {S T} sub hT := by
    obtain ⟨x,hx,h⟩ := (mem_filter.mp hT).2
    have mono (j) : occupied a b S j ≤ occupied a b T j := card_le_card (filter_subset_filter _ sub)
    exact mem_filter.mpr ⟨mem_univ _,x,hx,(mono 0).trans h.1,(mono 1).trans h.2.1,
      (mono 2).trans h.2.2.1,(mono 3).trans h.2.2.2⟩

private theorem measured {n j t L : ℕ} (g : VotingGame (Fin n)) (hj : j<n) (ht : 0<t) (flag : Bool)
    (total : g.losing.card=L)
    (inc : ∀ i, (if i.val=j then t else 2*t)+2*(g.losing.filter fun S ↦ i∈S).card=L)
    (lock : flag=true → L=6*t) : Profile n flag := by
  refine ⟨g,⟨j,hj⟩,t,ht,?_,fun b ↦ total.trans (lock b)⟩
  intro i
  have a := g.swing_count i
  rw [total] at a
  have b := inc i
  simp only [Fin.ext_iff]
  exact Nat.add_right_cancel (a.trans b.symm)

private def rule6 : VotingGame (Fin 6) := rule 6 1 3
  [(0,0,2,0), (1,1,0,0), (0,0,1,1), (0,1,0,1)] (by decide +kernel) (by decide +kernel)

theorem seed6 : Profile 6 false :=
  measured (j := 5) (t := 4) (L := 14) rule6 (by decide) (by decide) false
    (by decide +kernel) (by decide +kernel) (by decide)

private def rule7 : VotingGame (Fin 7) := rule 7 3 6
  [(0,2,0,0), (2,0,0,0), (0,1,0,1), (1,0,0,1)] (by decide +kernel) (by decide +kernel)

theorem seed7 : Profile 7 false :=
  measured (j := 6) (t := 6) (L := 20) rule7 (by decide) (by decide) false
    (by decide +kernel) (by decide +kernel) (by decide)

private def rule8 : VotingGame (Fin 8) := rule 8 2 4
  [(0,1,3,0), (2,0,1,0), (1,1,1,1)] (by decide +kernel) (by decide +kernel)

theorem seed8 : Profile 8 false :=
  measured (j := 7) (t := 16) (L := 88) rule8 (by decide) (by decide) false
    (by decide +kernel) (by decide +kernel) (by decide)

private def rule9 : VotingGame (Fin 9) := rule 9 1 4
  [(0,0,4,0), (0,1,3,0), (1,2,1,0), (1,3,0,0), (0,1,2,1), (0,2,1,1), (1,0,2,1), (1,1,1,1)] (by decide +kernel) (by decide +kernel)

theorem seed9 : Profile 9 true :=
  measured (j := 8) (t := 34) (L := 204) rule9 (by decide) (by decide) true
    (by decide +kernel) (by decide +kernel) (by decide)

private def rule10 : VotingGame (Fin 10) := rule 10 2 5
  [(1,0,3,0), (1,1,2,0), (2,0,2,0), (2,1,1,0), (0,0,4,1), (0,2,2,1), (1,0,2,1), (1,1,1,1), (2,0,1,1), (2,3,0,1)] (by decide +kernel) (by decide +kernel)

theorem seed10 : Profile 10 true :=
  measured (j := 9) (t := 62) (L := 372) rule10 (by decide) (by decide) true
    (by decide +kernel) (by decide +kernel) (by decide)

private def pair : VotingGame (Fin 2) := rule 2 1 1 [(1,0,0,0),(0,0,0,1)]
  (by decide +kernel) (by decide +kernel)

private theorem pair_loss : pair.losing.card = 3 := by decide +kernel

private theorem pair_swing : ∀ i, pair.swings i=1 := by decide +kernel

theorem extend {n} (h : Profile n true) : Profile (n+2) true :=
  h.grow pair pair_loss pair_swing

end Seeds
end KurzBanzhaf
