module

public import conjectures.KurzBanzhaf.Composition
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace KurzBanzhaf
open Finset

/-- A repeatable base has six losing coalitions per swing of the distinguished voter. -/
def Profile (n : ℕ) (repeatable : Bool) : Prop :=
  ∃ (g : VotingGame (Fin n)) (j : Fin n) (t : ℕ), 0<t ∧
    (∀ i, g.swings i = if i=j then t else 2*t) ∧ (repeatable=true → g.losing.card=6*t)

theorem Profile.forget {n} (h : Profile n true) : Profile n false := by
  obtain ⟨g,j,t,ht,sw,_⟩ := h
  exact ⟨g,j,t,ht,sw,by simp⟩

theorem Profile.grow {n} (base : Profile n true) (pair : VotingGame (Fin 2))
    (loss : pair.losing.card=3) (sw : ∀ i, pair.swings i=1) : Profile (n+2) true := by
  obtain ⟨g,j,t,ht,hv,hl⟩ := base
  let joined := g.disjoin pair
  let e := finSumFinEquiv (m := n) (n := 2)
  refine ⟨joined.relabel e,e (.inl j),3*t,by omega,?_,?_⟩
  · intro i
    obtain ⟨a,rfl⟩ := e.surjective i
    rw [VotingGame.relabel_swings]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    cases a with
    | inl b =>
        rw [VotingGame.disjoin_left,hv,loss]
        split <;> simp_all <;> omega
    | inr b =>
        simp [joined,VotingGame.disjoin_right,hl rfl,sw]
        omega
  · intro _
    change (joined.losing.map e.finsetCongr.toEmbedding).card = 6*(3*t)
    rw [card_map,VotingGame.disjoin_losses,loss,hl rfl]
    omega

theorem Profile.vector {n : ℕ} (hn : 6≤n) (p : Profile n false) :
    ∃ g : VotingGame (Fin n), ∀ i, g.banzhaf i =
      (if i.val+1=n then 1 else 2) / (2*(n:ℝ)-1) := by
  obtain ⟨g,j,t,ht,raw,_⟩ := p
  let last : Fin n := ⟨n-1,by omega⟩
  let e := Equiv.swap j last
  let G := g.relabel e
  refine ⟨G,?_⟩
  have atLast : e j=last := Equiv.swap_apply_left _ _
  have counts (i : Fin n) : G.swings i = if i=last then t else 2*t := by
    obtain ⟨a,rfl⟩ := e.surjective i
    change (g.relabel e).swings (e a) = _
    rw [VotingGame.relabel_swings,raw,←atLast]
    simp
  have total : ∑ i, (G.swings i : ℝ) = (2*(n:ℝ)-1)*t := by
    rw [←add_sum_erase univ (fun i ↦ (G.swings i : ℝ)) (mem_univ last),counts last,ite_eq_left rfl]
    have tail : (∑ i ∈ univ.erase last, (G.swings i : ℝ)) =
        ∑ _i ∈ univ.erase last, ((2*t:ℕ):ℝ) := by
      apply sum_congr rfl
      intro i hi
      exact_mod_cast (show G.swings i=2*t by rw [counts,ite_eq_right (mem_erase.mp hi).1])
    rw [tail,sum_const,card_erase_of_mem (mem_univ last),card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast [Nat.cast_sub (show 1≤n by omega)]
    ring
  intro i
  have cond : i.val+1=n ↔ i=last := by
    change i.val+1=n ↔ i=⟨n-1,_⟩
    rw [Fin.ext_iff]
    have := i.isLt
    dsimp
    omega
  have tr : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have nr : (2*(n:ℝ)-1) ≠ 0 := by
    have : (6:ℝ)≤n := by exact_mod_cast hn
    linarith
  rw [VotingGame.banzhaf,total,counts]
  simp only [cond]
  split <;> push_cast <;> field_simp

end KurzBanzhaf
