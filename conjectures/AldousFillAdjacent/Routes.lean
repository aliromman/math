module

public import conjectures.AldousFillAdjacent.Operator
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.Linarith

@[expose] public section
namespace AldousFillAdjacent
open Equiv Finset

variable {m : ℕ}

def route (l : List (Option (Fin m))) : Deck m := (l.map move).prod

private theorem route_append (a b : List (Option (Fin m))) : route (a++b)=route a*route b := by
  simp [route]

private theorem ordered_swap (i j : Fin m) (h : i≤j) :
    ∃ l : List (Option (Fin m)), route l=swap i j ∧ l.length ≤ 2*(j.val-i.val) := by
  induction v : j.val generalizing j with
  | zero =>
    have eq : i=j := Fin.ext (by have := Fin.le_iff_val_le_val.mp h; omega)
    subst i
    exact ⟨[],by simp [route,← Equiv.Perm.one_def],by simp⟩
  | succ k ih =>
    by_cases ij : i=j
    · subst i; exact ⟨[],by simp [route,← Equiv.Perm.one_def],by simp⟩
    have ij' : i.val<j.val := Fin.lt_def.mp (lt_of_le_of_ne h ij)
    let p : Fin m := ⟨k,by have := j.isLt; omega⟩
    have ip : i≤p := Fin.le_iff_val_le_val.mpr (by dsimp [p];omega)
    have mv : move (some p)=swap p j := by
      simp only [move]
      congr 1
      apply Fin.ext
      simp only [p,Nat.mod_eq_of_lt (by omega : k+1<m),v]
    by_cases same : i=p
    · refine ⟨[some p],by simp [route,mv,same],?_⟩
      simp only [List.length_cons,List.length_nil]
      have vv := congrArg Fin.val same
      dsimp [p] at vv
      omega
    obtain ⟨l,hl,hlen⟩ := ih p ip rfl
    refine ⟨[some p]++l++[some p],?_,?_⟩
    · simp only [route_append,hl,show route [some p]=swap p j by simp [route,mv]]
      rw [swap_mul_swap_mul_swap same ij,swap_comm]
    · simp only [List.length_append,List.length_cons,List.length_nil]
      change l.length≤2*(k-i.val) at hlen
      omega

private theorem route_swap (i j : Fin m) : ∃ l : List (Option (Fin m)),
    route l=swap i j ∧ l.length≤2*m := by
  rcases le_total i j with hij|hji
  · obtain ⟨l,hl,h⟩ := ordered_swap i j hij
    exact ⟨l,hl,by have := j.isLt;omega⟩
  · obtain ⟨l,hl,h⟩ := ordered_swap j i hji
    exact ⟨l,hl.trans (swap_comm _ _),by have := i.isLt;omega⟩

private theorem route_support (g : Deck m) :
    ∃ l : List (Option (Fin m)), route l=g ∧ l.length≤(2*m)*g.support.card := by
  by_cases e : g=1
  · subst g; exact ⟨[],by simp [route],by simp⟩
  have mask : ∃ x, g x≠x := by
    by_contra! h
    exact e (Equiv.ext h)
  obtain ⟨x,hx⟩ := mask
  let s := swap x (g x)
  have card : (s*g).support.card<g.support.card := Equiv.Perm.card_support_swap_mul hx
  obtain ⟨a,ha,hlen⟩ := route_swap x (g x)
  obtain ⟨b,hb,hlen'⟩ := route_support (s*g)
  refine ⟨a++b,?_,?_⟩
  · rw [route_append,ha,hb]
    simp [s]
  · rw [List.length_append]
    have d := Nat.mul_le_mul_left (2*m) card
    rw [Nat.mul_succ] at d
    omega
termination_by g.support.card

theorem short_route (g : Deck m) : ∃ l : List (Option (Fin m)),
    route l=g ∧ l.length≤2*m^2 := by
  obtain ⟨l,hl,h⟩ := route_support g
  refine ⟨l,hl,h.trans ?_⟩
  have a : g.support.card≤m := by simpa using (card_le_univ g.support)
  have b := Nat.mul_le_mul_left (2*m) a
  simpa [pow_two,Nat.mul_assoc] using b

end AldousFillAdjacent
