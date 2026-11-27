module

public import conjectures.KurzWeighted.Influence
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith

@[expose] public section
namespace KurzWeighted
open Finset Equiv
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem ordinary_embedding (d : V) (A T : Finset V) (ha : d∉A) (ht : d∉T)
    (size : A.card≤T.card) : ∃ p : Perm V, p d=d ∧ p.finsetCongr A ⊆ T := by
  obtain ⟨C,sub,card⟩ := exists_subset_card_eq size
  obtain ⟨p,hp⟩ := Perm.exists_map_finset_eq A C card.symm
  have out : p d∉C := by rw [←hp]; simpa using ha
  have out' : d∉C := fun h ↦ ht (sub h)
  let t := swap (p d) d
  have fixed : t.finsetCongr C=C := map_swap_of_same _ (by simp [out,out'])
  refine ⟨t*p,by simp [t],?_⟩
  rw [show (t*p).finsetCongr A = t.finsetCongr (p.finsetCongr A) by
    simp [finsetCongr_apply,map_map,Function.Embedding.trans]; rfl]
  rw [show p.finsetCongr A=C from hp,fixed]
  exact sub

omit [Fintype V] in
private theorem slice_mono (d : V) {g : Rule V} (mon : Monotone g)
    (sym : ∀ (p : Perm V), p d=d → ∀ S, g (p.finsetCongr S)=g S)
    (A T : Finset V) (ha : d∉A) (ht : d∉T) (size : A.card≤T.card) :
    g A ≤ g T ∧ g (insert d A) ≤ g (insert d T) := by
  obtain ⟨p,fix,sub⟩ := ordinary_embedding d A T ha ht size
  constructor
  · rw [←sym p fix A]
    exact mon sub
  · rw [←sym p fix (insert d A)]
    simp only [finsetCongr_apply,map_insert,Equiv.coe_toEmbedding,fix]
    exact mon (insert_subset_insert d sub)

/-- With interchangeable ordinary voters, the distinguished voter has zero power or at least
as much power as each ordinary voter. -/
theorem symmetric_dichotomy (d : V) (g : Rule V) (mon : Monotone g)
    (binary : ∀ S,g S=0 ∨ g S=1)
    (sym : ∀ p : Perm V, p d=d → ∀ S, g (p.finsetCongr S)=g S) :
    swings g d=0 ∨ ∀ i, swings g i≤swings g d := by
  by_cases dummy : ∀ A, d∉A → g (insert d A)=g A
  · left
    apply sum_eq_zero
    intro S _
    by_cases h : d∈S <;> simp [h,dummy S]
  right
  push Not at dummy
  obtain ⟨A,ha,changeVote⟩ := dummy
  have m := mon (subset_insert d A)
  obtain ⟨lose,win⟩ : g A=0 ∧ g (insert d A)=1 := by
    rcases binary A with h|h <;> rcases binary (insert d A) with j|j <;> grind
  intro i
  by_cases eq : i=d
  · simp [eq]
  have order (S : Finset V) (hd : d∈S) (hi : i∉S) : rename (swap d i) g S ≤ g S := by
    let T := S.erase d
    have dt : d∉T := notMem_erase _ _
    have it : i∉T := fun h ↦ hi (mem_of_mem_erase h)
    have orig : insert d T=S := insert_erase hd
    change g ((swap d i).finsetCongr S)≤g S
    rw [map_swap_of_mem S hd hi]
    change g (insert i T)≤g S
    by_cases size : A.card≤T.card
    · have bound := (slice_mono d mon sym A T ha dt size).2
      rw [win,orig] at bound
      rcases binary (insert i T) with h|h <;> linarith
    · have size' : (insert i T).card ≤ A.card := by rw [card_insert_of_notMem it]; omega
      have outside : d∉insert i T := by simp [Ne.symm eq,dt]
      have bound := (slice_mono d mon sym (insert i T) A outside ha size').1
      rw [lose] at bound
      rcases binary S with h|h <;> linarith
  have eq := dist_swap_ordered g order
  have nonneg : 0≤distance g (rename (swap d i) g) := sum_nonneg fun _ _ ↦ abs_nonneg _
  linarith

end KurzWeighted
