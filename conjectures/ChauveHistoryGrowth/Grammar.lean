module

public import conjectures.ChauveHistoryGrowth.Statement
public import conjectures.ChauveHistoryGrowth.Series
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Positivity

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth

open Finset PowerSeries

theorem card_choice (a b : Family) : Fintype.card (a.choice b) = Fintype.card a+Fintype.card b :=
  Fintype.card_sum

theorem card_pairs (n : ℕ) (u v : Fin n → Family) :
    Fintype.card (Family.pairs n u v)=∑ i, Fintype.card (u i)*Fintype.card (v i) := by
  change Fintype.card ((i : Fin n) × u i × v i) = _
  simp [Fintype.card_sigma,Fintype.card_prod]

def splits (a b : Tree) (n : ℕ) :=
  ∑ i : Fin n, count a (i.val+1) * count b (n-(i.val+1)+1)

theorem leaf_count (n : ℕ) : count .tip (n+1)=(if n=0 then 1 else 0)+splits .tip .tip n := by
  rw [count,histories,card_choice,card_pairs]
  have h : Fintype.card (Family.terminal n)=(if n=0 then 1 else 0) := Fintype.card_fin _
  rw [h]
  rfl

theorem fork_count (a b : Tree) (n : ℕ) :
    count (.fork a b) (n+1)=splits (.fork a b) (.fork a b) n+
      (splits a b n+(count a (n+1)+count b (n+1))) := by
  rw [count,histories,card_choice,card_choice,card_choice,card_pairs,card_pairs]
  rfl

def H (t : Tree) : S := PowerSeries.mk fun n => (count t n : ℝ)
theorem hc (t : Tree) (n : ℕ) : coeff n (H t) = count t n := coeff_mk _ _
theorem hz (t : Tree) : constantCoeff (H t)=0 := by
  rw [← coeff_zero_eq_constantCoeff_apply,hc,count,Nat.cast_zero]
theorem hp (t : Tree) : 0 ≼ H t := by
  rw [zeroBelow]; intro n; rw [hc]; positivity

theorem split_coeff (a b : Tree) (n : ℕ) : coeff (n+1) (H a*H b) = (splits a b n : ℝ) := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (H a)*coeff j (H b))]
  simp only [hc]
  rw [sum_range_succ',sum_range_succ]
  have zero_count (t : Tree) : count t 0=0 := rfl
  simp only [Nat.sub_zero,Nat.sub_self,zero_count, Nat.cast_zero,zero_mul,mul_zero,add_zero]
  unfold splits
  rw [Nat.cast_sum,Fin.sum_univ_eq_sum_range
    (fun j => ((count a (j+1)*count b (n-(j+1)+1) : ℕ) : ℝ))]
  apply sum_congr rfl
  intro i hi
  have lt := mem_range.mp hi
  have eq : n+1-(i+1)=n-(i+1)+1 := by omega
  simp [eq]

theorem leaf_grammar : H .tip = X + H .tip * H .tip := by
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply,hz]
  | succ n =>
    simp only [map_add,hc,split_coeff,leaf_count,Nat.cast_add]
    congr 1
    by_cases h : n=0 <;> simp [coeff_X,h]

theorem fork_grammar (a b : Tree) :
    H (.fork a b)=H (.fork a b)*H (.fork a b)+(H a*H b+(H a+H b)) := by
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply,hz]
  | succ n => simp only [map_add,hc,split_coeff,fork_count,Nat.cast_add]

def P (t : Tree) : S := 1+H t

def input : Tree → S
  | .tip => 1+X
  | .fork a b => P a*P b

theorem input_eq (t : Tree) : input t = 1+H t-H t*H t := by
  cases t with
  | tip => dsimp [input]; linear_combination -leaf_grammar
  | fork a b => dsimp [input,P]; linear_combination -fork_grammar a b

theorem Ppos (t : Tree) : 0 ≼ P t := addP onePos (hp t)

theorem leaf_one (t : Tree) : count t 1=t.leaves := by
  induction t with
  | tip => rw [leaf_count 0]; simp [splits,Tree.leaves]
  | fork a b ha hb => rw [fork_count a b 0]; simp [splits,Tree.leaves,ha,hb]

end ChauveHistoryGrowth
end
