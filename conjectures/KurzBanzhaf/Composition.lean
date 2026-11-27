module

public import conjectures.KurzBanzhaf.Statement
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Tauto

@[expose] public section
namespace KurzBanzhaf
open Finset

namespace VotingGame
variable {V W : Type*}

def joined (A : Finset (Finset V)) (B : Finset (Finset W)) :=
  (A ×ˢ B).map Finset.sumEquiv.symm.toEquiv.toEmbedding

theorem mem_joined {A : Finset (Finset V)} {B : Finset (Finset W)} {S : Finset (V ⊕ W)} :
    S ∈ joined A B ↔ S.toLeft ∈ A ∧ S.toRight ∈ B := by
  simp [joined]

variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Either component can pass the proposal. A coalition loses precisely when both components lose. -/
def disjoin (g : VotingGame V) (h : VotingGame W) : VotingGame (V ⊕ W) where
  losing := joined g.losing h.losing
  empty_loses := by
    apply mem_joined.mpr
    exact ⟨g.empty_loses,h.empty_loses⟩
  full_wins := by
    intro hu
    exact g.full_wins (by simpa using (mem_joined.mp hu).1)
  down sub hST := mem_joined.mpr ⟨g.down (toLeft_subset_toLeft sub) (mem_joined.mp hST).1,
    h.down (toRight_subset_toRight sub) (mem_joined.mp hST).2⟩

theorem disjoin_losses (g : VotingGame V) (h : VotingGame W) :
    (g.disjoin h).losing.card = g.losing.card*h.losing.card := by simp [disjoin,joined]

theorem disjoin_left (g : VotingGame V) (h : VotingGame W) (i : V) :
    (g.disjoin h).swings (.inl i) = g.swings i*h.losing.card := by
  have hs : (g.disjoin h).swingSets (.inl i) = joined (g.swingSets i) h.losing := by
    ext A
    simp only [swingSets,disjoin,mem_filter,mem_joined,toLeft_insert_inl,toRight_insert_inl]
    tauto
  simp [swings,hs,joined]

theorem disjoin_right (g : VotingGame V) (h : VotingGame W) (j : W) :
    (g.disjoin h).swings (.inr j) = g.losing.card*h.swings j := by
  have hs : (g.disjoin h).swingSets (.inr j) = joined g.losing (h.swingSets j) := by
    ext A
    simp only [swingSets,disjoin,mem_filter,mem_joined,toLeft_insert_inr,toRight_insert_inr]
    tauto
  simp [swings,hs,joined]

/-- For a fixed voter, each losing set that contains the voter pairs with its deletion. -/
theorem swing_count (g : VotingGame V) (i : V) :
    g.swings i + 2*(g.losing.filter fun S ↦ i∈S).card = g.losing.card := by
  let present := g.losing.filter (fun S ↦ i∈S)
  let absent := g.losing.filter (fun S ↦ i∉S ∧ insert i S ∈ g.losing)
  have eq : absent.card = present.card := by
    apply Finset.card_bij (fun S _ ↦ insert i S)
    · intro S hS
      exact mem_filter.mpr ⟨(mem_filter.mp hS).2.2,mem_insert_self _ _⟩
    · intro S hS T hT he
      have same := congrArg (fun U : Finset V ↦ U.erase i) he
      simpa [(mem_filter.mp hS).2.1,(mem_filter.mp hT).2.1] using same
    · intro T hT
      obtain ⟨ht,hi⟩ := mem_filter.mp hT
      refine ⟨T.erase i,mem_filter.mpr ⟨g.down (erase_subset _ _) ht,(notMem_erase _ _),?_⟩,?_⟩
      · rwa [insert_erase hi]
      · exact insert_erase hi
  have parts : g.swingSets i ∪ absent ∪ present = g.losing := by
    ext S
    simp only [swingSets,absent,present,mem_union,mem_filter]
    by_cases hi : i∈S
    · simp [hi]
    · tauto
  have disj1 : Disjoint (g.swingSets i) absent := by
    apply disjoint_left.mpr
    intro S hS hA
    exact (mem_filter.mp hS).2 (mem_filter.mp hA).2.2
  have disj2 : Disjoint (g.swingSets i ∪ absent) present := by
    apply disjoint_left.mpr
    intro S hS hP
    obtain ⟨hl,hi⟩ := mem_filter.mp hP
    obtain hs|ha := mem_union.mp hS
    · exact (mem_filter.mp hs).2 (by simpa [insert_eq_of_mem hi] using hl)
    · exact (mem_filter.mp ha).2.1 hi
  have e := congrArg Finset.card parts
  rw [card_union_of_disjoint disj2,card_union_of_disjoint disj1,eq] at e
  change (g.swingSets i).card + 2*present.card = _
  omega

def relabel (g : VotingGame V) (e : V ≃ W) : VotingGame W where
  losing := g.losing.map e.finsetCongr.toEmbedding
  empty_loses := by
    rw [mem_map_equiv]
    exact g.empty_loses
  full_wins := by
    rw [mem_map_equiv]
    change univ.map e.symm.toEmbedding ∉ g.losing
    simpa using g.full_wins
  down sub hT := by
    rw [mem_map_equiv] at hT ⊢
    exact g.down (Finset.map_subset_map.mpr sub) hT

theorem relabel_swings (g : VotingGame V) (e : V ≃ W) (i : V) :
    (g.relabel e).swings (e i) = g.swings i := by
  have sets : (g.relabel e).swingSets (e i) = (g.swingSets i).map e.finsetCongr.toEmbedding := by
    ext S
    obtain ⟨T,rfl⟩ := e.finsetCongr.surjective S
    have ins : insert (e i) (e.finsetCongr T) = e.finsetCongr (insert i T) := by
      simp [Equiv.finsetCongr_apply]
    simp only [swingSets,relabel,mem_filter,mem_map_equiv,ins,Equiv.symm_apply_apply]
  simp [swings,sets]

end VotingGame
end KurzBanzhaf
