module

public import conjectures.TanWuHon.Cases
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

public section
namespace TanWuHon
open Multiset

private theorem optimal_upper {f L m : ℕ} (hf : 0<f) (hL : LeastNondivisor f L)
    (large : sample f≤m) (many : 2*f-1≤m) :
    rho f (f+m*L)<m+L+2*L^2 := by
  have hp := hL.1
  have hm : 0<m*L := Nat.mul_pos (by omega) hp
  obtain ⟨P,p,pk⟩ := optimum hf (by omega : f<f+m*L)
  have lb := base_lower hf hm hL
  rw [←pk,Nat.mul_comm m L] at lb
  have mk := Nat.le_of_mul_le_mul_left lb hp
  have bud : P.sum≤L*P.card+f := by rw [p.2.1,Nat.mul_comm m L]; omega
  have st := stable hf hL p.1 p.2.2 bud (many.trans mk) (large.trans mk)
  have cnt : f/L≤P.count L := (le_max_right _ _).trans st
  obtain ⟨S,eq⟩ := Multiset.le_iff_exists_add.mp (le_count_iff_replicate_le.mp cnt)
  obtain ⟨A,R,k,split,few,ksum⟩ := split_residues hp S
  let Q := replicate (f/L) L+A
  have full : P=Q+R := by rw [eq,split,←add_assoc]
  have sub : Q≤P := by rw [full]; exact Multiset.le_add_right _ _
  have wt : Q.sum=(f/L+k)*L := by
    change (replicate (f/L) L+A).sum=_
    rw [sum_add,sum_replicate,ksum,Nat.add_mul]; rfl
  have mass := congrArg Multiset.sum full
  rw [p.2.1,sum_add] at mass
  have heavy : f<R.sum := by
    by_contra! low
    have res : R.sum ≡ f [MOD L] := by
      change R.sum%L=f%L
      have mod := congrArg (· % L) mass
      simpa [wt,Nat.add_mod] using mod.symm
    have dvd := (Nat.modEq_iff_dvd' low).mp res
    let j := (f-R.sum)/L
    have cap : j≤f/L := Nat.div_le_div_right (Nat.sub_le _ _)
    have add : (replicate j L+R).sum=f := by
      simp only [sum_add,sum_replicate,nsmul_eq_mul]
      change (f-R.sum)/L*L+R.sum=f
      rw [Nat.div_mul_cancel dvd,Nat.sub_add_cancel low]
    apply p.2.2 _ _ add
    rw [full]
    exact add_le_add_left ((replicate_mono _ cap).trans (Multiset.le_add_right _ _)) _
  let cap := fun (_:ℕ) ↦ 2*L-2
  have wb := weight_bound Q 1 L (fun x hx ↦ p.1 x (subset_of_le sub hx)) cap (by
    intro j hj
    exact (count_le_of_le j sub).trans (short_counts hf hL p.1 p.2.2 bud (many.trans mk)
      (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2))
  have defle : (∑ j ∈ Finset.Ico 1 L, (L-j)*cap j)≤deficit L := Finset.sum_le_sum fun j _ ↦
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.le_succ _) _)
  have cards := congrArg Multiset.card full
  rw [card_add] at cards
  have n := Nat.mul_lt_mul_of_pos_left few hp
  have ed := deficit_upper L
  have small : L*P.card<L*(m+L+2*L^2) := by
    rw [cards,Nat.mul_add]
    nlinarith
  rw [←pk]
  exact Nat.lt_of_mul_lt_mul_left small

/-- The last failed step lies within an additive O(L³) of fL or later. -/
theorem lower_scale {f L : ℕ} (hf : 0<f) (hL : LeastNondivisor f L) (large : 8*L^2≤f) :
    ∃ r, f≤r ∧ (f-(L+2*L^2))*L≤r ∧ r≤2*(f-1)*L ∧
      rho f (f+r+L)≠rho f (f+r)+1 := by
  have l2 : 2≤L := by
    have p := hL.1
    by_contra! small
    have eq : L=1 := by omega
    exact hL.2.1 (by simp [eq])
  have sq : L≤L^2 := Nat.le_self_pow (by decide) L
  let c := L+2*L^2
  let t := f-c
  let m := 2*f-1
  have ct : t+c=f := by dsimp [t,c]; omega
  have tm : t≤m := by dsimp [t,m]; omega
  have tf : f≤t*L := by
    have h := Nat.mul_le_mul_left t l2
    dsimp [t,c] at *
    omega
  have ini := ones_lower hf tf
  have sam : sample f=m := by
    have ff : 6<f := by omega
    unfold sample; split <;> dsimp [m] <;> omega
  have cap := optimal_upper hf hL sam.le (show 2*f-1≤m by rfl)
  by_contra! no
  have increase (j : ℕ) (hj : t+j≤m) :
      rho f (f+(t+j)*L)=rho f (f+t*L)+j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have rr : f≤(t+j)*L := tf.trans (Nat.mul_le_mul_right L (Nat.le_add_right _ _))
      have lo : (f-(L+2*L^2))*L≤(t+j)*L := Nat.mul_le_mul_right L (Nat.le_add_right t j)
      have bound : (t+j)*L≤2*(f-1)*L := Nat.mul_le_mul_right L (by dsimp [m] at hj; omega)
      have eq := no ((t+j)*L) rr lo bound
      rw [Nat.add_succ,Nat.succ_mul,←Nat.add_assoc,eq,ih (by omega),Nat.add_assoc]
  have last := increase (m-t) (by omega)
  rw [Nat.add_sub_of_le tm] at last
  dsimp [c] at ct
  omega

/-- The least possible period threshold has order fL, uniformly in f. -/
theorem half_scale {f L : ℕ} (big : 1152≤f) (hL : LeastNondivisor f L) :
    ∃ r, f≤r ∧ f*L≤2*r ∧ r≤2*(f-1)*L ∧ rho f (f+r+L)≠rho f (f+r)+1 := by
  have sq : L≤L^2 := Nat.le_self_pow (by decide) L
  have scale : 8*L^2≤f := by
    by_cases low : L≤12
    · have := Nat.pow_le_pow_left low 2
      omega
    · have g := lcm_growth (by omega : 0<f) hL (by omega)
      have h := Nat.mul_le_mul_right (L^2) (show 2≤L by omega)
      rw [←pow_succ'] at h
      change 2*L^2≤L^3 at h
      omega
  obtain ⟨r,rf,lower,cap,fail⟩ := lower_scale (by omega) hL scale
  refine ⟨r,rf,?_,cap,fail⟩
  have := Nat.mul_le_mul_right L (show f≤2*(f-(L+2*L^2)) by omega)
  rw [Nat.mul_assoc] at this
  omega

/-- info: 'TanWuHon.half_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms half_scale

/-- info: 'TanWuHon.lower_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower_scale

end TanWuHon
