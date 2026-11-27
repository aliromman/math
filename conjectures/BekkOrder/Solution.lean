module

public import conjectures.BekkOrder.Coverage
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
namespace BekkOrder
open Finset Polynomial

def initial : Basis 3 1 where
  start _ := 0
  separated i j h := by have := i.isLt;have := j.isLt;omega
  below _ := by decide

private theorem initial_nodes : initial.nodes={0,1,3} := by
  ext x
  simp [Basis.mem_nodes,initial];tauto

private theorem initial_weights (p : ℝ) :
    weight initial p 0=(1-p)*(1-2*p) ∧ weight initial p 1=3*p*(1-p) ∧ weight initial p 3=p^2 := by
  have e0 : ({0,1,3} : Finset ℕ).erase 0={1,3} := by decide
  have e1 : ({0,1,3} : Finset ℕ).erase 1={0,3} := by decide
  have e3 : ({0,1,3} : Finset ℕ).erase 3={0,1} := by decide
  unfold weight
  constructor <;> try constructor
  all_goals norm_num [lag,initial_nodes,Lagrange.basis,Lagrange.basisDivisor,avg,binWeight,e0,e1,e3,
    Finset.sum_range_succ,eval_prod,Nat.choose]; ring

/-- At order two on three bits, the first basis is feasible on [0,1/2] and again at one. -/
theorem literal_endpoint (p : ℝ) (hp : p∈Set.Icc (0:ℝ) 1) :
    Feasible initial p ↔ p≤1/2 ∨ p=1 := by
  rw [feasible_iff]
  have ⟨a,b,c⟩ := initial_weights p
  constructor
  · intro h
    have zero := h 0 (by rw [initial_nodes];simp)
    rw [a] at zero
    by_cases e : p=1
    · exact Or.inr e
    · have lt : p<1 := lt_of_le_of_ne hp.2 e
      have l := (mul_nonneg_iff_of_pos_left (sub_pos.mpr lt)).mp zero
      left;linarith
  · intro h x hx
    rw [initial_nodes] at hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · rw [a]
      rcases h with l|rfl
      · exact mul_nonneg (sub_nonneg.mpr hp.2) (by linarith)
      · norm_num
    · rw [b];exact mul_nonneg (by linarith only [hp.1]) (sub_nonneg.mpr hp.2)
    · rw [c];exact sq_nonneg _

private theorem literal_fails : ¬Published := by
  intro h
  have real : Realizable initial := by
    refine ⟨0,1/2,by norm_num,?_⟩
    intro x hx
    have ok : x∈Set.Icc (0:ℝ) 1 := ⟨hx.1,hx.2.trans (by norm_num)⟩
    exact ⟨ok,(literal_endpoint x ok).mpr (Or.inl hx.2)⟩
  obtain ⟨a,b,_,sets⟩ := (h 3 1 (by decide) (by decide)).1 initial real
  have zero : (0:ℝ)∈Set.Icc a b := by
    rw [←sets];exact ⟨by constructor <;> norm_num,(literal_endpoint _ (by constructor <;> norm_num)).mpr (Or.inl (by norm_num))⟩
  have one : (1:ℝ)∈Set.Icc a b := by
    rw [←sets];exact ⟨by constructor <;> norm_num,(literal_endpoint _ (by constructor <;> norm_num)).mpr (Or.inr rfl)⟩
  have mid : (3/4:ℝ)∈ClosedFeasible initial := by
    rw [sets];exact ⟨zero.1.trans (by norm_num),(show (3/4:ℝ)≤1 by norm_num).trans one.2⟩
  have e := (literal_endpoint _ mid.1).mp mid.2
  norm_num at e

/-- The interval order holds after taking nondegenerate parameters, with an explicit correction at deterministic bias. -/
theorem resolution : OrderedIntervals ∧ Covers ∧ ¬Published := ⟨intervals,coverage,literal_fails⟩

/-- info: 'BekkOrder.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end BekkOrder
end
