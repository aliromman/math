module

public import conjectures.CFPLogDensity.DenseInterval
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace CFPLogDensity
open Finset Filter

private theorem sq_le_binary (s : ℕ) (hs : 4≤s) : s*s≤2^s := by
  induction s,hs using Nat.le_induction with
  | base => decide
  | succ s hs ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul hs hs, Nat.mul_le_mul_left s hs]

/-- In any coloring with r colors, one color in a large dyadic block represents
every integer from C times the block size times n+1 to the squared block size divided by C. -/
theorem dense_interval (r : ℕ) (hr : 0<r) : ∃ C : ℕ, 0<C ∧
    ∀ᶠ n : ℕ in atTop, ∀ χ : ℕ → Fin r, ∃ i, ∀ x : ℕ,
      C*2^n*(n+1) ≤ x → C*x ≤ (2^n)^2 →
      ∃ S : Finset ℕ, (∀ y∈S, 2^n≤y ∧ y<2*2^n ∧ χ y=i) ∧ S.sum id=x := by
  obtain ⟨c,pattern⟩ := color_pairs r hr
  let B := 2^c
  let K := ColorPairs.batchSize c
  let T := 2*K*(B+1)+B+1
  let C := 4*(T+B+1)
  have tp : 0<T := by dsimp [T]; positivity
  have cp : 0<C := by dsimp [C]; positivity
  refine ⟨C,cp,eventually_atTop.mpr ⟨2*c+2*T+10,?_⟩⟩
  intro n hn χ
  let s := n-(c+2)
  have en : n=c+2+s := by dsimp [s]; omega
  have s4 : 4≤s := by omega
  have wsmall : T*(n+1)≤2^s := by
    refine (Nat.mul_le_mul_left T (show n+1≤2*s by omega)).trans ?_
    have mono := Nat.mul_le_mul_right s (show 2*T≤s by omega)
    have eq : T*(2*s)=2*T*s := by ring
    rw [eq]
    exact mono.trans (sq_le_binary s s4)
  obtain ⟨F⟩ := pattern n (by omega) χ
  have dp : F.d≤B := (Nat.le_mul_of_pos_right _ F.stride_pos).trans F.step_bound
  have sp : F.stride≤B := (Nat.le_mul_of_pos_left _ F.step_pos).trans F.step_bound
  have Sbound : F.work s+F.d≤T*(n+1) := by
    have bs : B+s≤(B+1)*(n+1) := by
      rw [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
      omega
    have m := Nat.mul_le_mul_left (2*K) ((Nat.add_le_add_right sp s).trans bs)
    have bn : B≤(B+1)*(n+1) := (Nat.le_succ B).trans (Nat.le_mul_of_pos_right _ (by omega))
    dsimp [ColorPairs.work,T]
    change 2*(K*F.stride)+2*K*s+F.d≤(2*K*(B+1)+B+1)*(n+1)
    nlinarith only [m,bn,dp]
  have fig : 2^n=B*(4*2^s) := by rw [en,pow_add,pow_add]; dsimp [B]; ring
  have dense : 4*2^s≤F.indices.card := by
    have d := F.dense
    rw [fig] at d
    exact Nat.le_of_mul_le_mul_left d (by dsimp [B]; positivity)
  have limited := Sbound.trans wsmall
  obtain ⟨P,num,long⟩ := F.long_span s en (by rw [pow_add]; norm_num; omega)
  obtain ⟨lo,hi,left,right,get⟩ := F.fill P long (by omega)
  refine ⟨F.color,fun x hx hupper => ?_⟩
  have boundLo : lo≤C*2^n*(n+1) := by
    refine left.trans ((Nat.mul_le_mul_right (2*2^n) (show P.used.card+F.d≤T*(n+1) by omega)).trans ?_)
    have le : 2*T≤C := by dsimp [C]; omega
    calc
      T*(n+1)*(2*2^n) = (2*T)*(2^n*(n+1)) := by ring
      _ ≤ C*(2^n*(n+1)) := Nat.mul_le_mul_right _ le
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have tail : 2^s ≤ F.indices.card-P.used.card-F.d := by omega
  have NN : 2^n≤C*(F.indices.card-P.used.card-F.d) := by
    rw [fig]
    have cb : 4*B≤C := by dsimp [C]; omega
    convert Nat.mul_le_mul cb tail using 1; ring
  have hhi : x≤hi := by
    refine Nat.le_of_mul_le_mul_left (c:=C) ?_ cp
    calc
      C*x ≤ (2^n)^2 := hupper
      _ ≤ (C*(F.indices.card-P.used.card-F.d))*2^n := by
        rw [pow_two]; exact Nat.mul_le_mul_right _ NN
      _ ≤ C*hi := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ right
  obtain ⟨S,hS,he⟩ := get x (boundLo.trans hx) hhi
  exact ⟨S,fun y hy => F.stock_spec (hS hy),he⟩

/-- info: 'CFPLogDensity.dense_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dense_interval

end CFPLogDensity
