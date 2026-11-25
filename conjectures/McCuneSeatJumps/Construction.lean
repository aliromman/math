module

public import conjectures.McCuneSeatJumps.Cells
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

open Finset MeasureTheory Set
namespace McCuneSeatJumps

/-- Intersect the two intervals for a population difference. -/
private theorem coordinate {h M A B : ℝ} (hh : 0 < h) (hM : h < M) (hB : 1 ≤ B)
    (lo : 0 < h*B-M*A) (up : h*B-M*A < h) :
    ∃ s : ℝ, 0 < s ∧ A-1 < h*s ∧ h*s < A ∧ B-1 < M*s ∧ M*s < B := by
  have hm := hh.trans hM
  have inter : (B-1)/M < A/h := (div_lt_div_iff₀ hm hh).mpr (by linarith)
  obtain ⟨s,hs,hs'⟩ := exists_between inter
  have before : (A-1)/h < (B-1)/M := (div_lt_div_iff₀ hh hm).mpr (by linarith)
  have after : A/h < B/M := (div_lt_div_iff₀ hh hm).mpr (by linarith)
  exact ⟨s,(div_nonneg (by linarith) hm.le).trans_lt hs,
    by linarith only [(div_lt_iff₀ hh).mp (before.trans hs)],
    by linarith only [(lt_div_iff₀ hh).mp hs'],
    by linarith only [(div_lt_iff₀ hm).mp hs],
    by linarith only [(lt_div_iff₀ hm).mp (hs'.trans after)]⟩

private theorem span {e : Fin 3 → ℝ} (a : 0 < e 0-e 2) (b : e 0-e 2 < 1)
    (c : 0 < e 1-e 2) (d : e 1-e 2 < 1) : ∀ i j, e i-e j < 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp <;> linarith

private theorem open_loss {h k : ℕ} {a b : Seats} {x : ℝ × ℝ}
    (hp : ∀ i, 0 < shares x i) (ha : Inside (shares x) h a) (hb : Inside (shares x) (h+k) b)
    (less : ∃ i, b i < a i) : 0 < probability h k := by
  let U := {y : ℝ × ℝ | (∀ i, 0 < shares y i) ∧ (∀ i j, err (shares y) h a i-err (shares y) h a j < 1)
    ∧ (∀ i j, err (shares y) (h+k) b i-err (shares y) (h+k) b j < 1)}
  have cont (t : ℕ) (a : Seats) (i : Fin 3) : Continuous (fun y => err (shares y) t a i) :=
    (continuous_const.mul (continuous_shares i)).sub continuous_const
  have op : IsOpen U := by
    simp only [U,Set.ofPred_and,Set.ofPred_forall]
    apply IsOpen.inter
    · exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_shares i)
    · apply IsOpen.inter <;>
        exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
          isOpen_lt ((cont _ _ i).sub (cont _ _ j)) continuous_const
  have sub : U ⊆ loss h k := fun y ⟨hpos,old,new⟩ =>
    ⟨hpos,a,b,inside_hamilton (sum_shares y) ⟨ha.1,old⟩,
      inside_hamilton (sum_shares y) ⟨hb.1,new⟩,less⟩
  have pos := (op.measure_pos volume ⟨x,hp,ha.2,hb.2⟩).trans_le (measure_mono sub)
  exact pos_iff_ne_zero.mpr (mul_ne_zero (by norm_num) pos.ne')

public theorem sufficient {h k : ℕ} (hk : 0 < k) (kh : k < h) (nd : ¬ h-k ∣ h) :
    0 < probability h k := by
  let r := h-k
  let j := h/r
  have hr : 0 < r := Nat.sub_pos_of_lt kh
  have hr2 : 2 ≤ r := by
    by_contra! hn
    have rr : r=1 := by omega
    exact nd (show r ∣ h by simp [rr])
  have jr : 0 < j := Nat.div_pos (Nat.sub_le ..) hr
  have rem := Nat.mod_add_div h r
  have modlt := Nat.mod_lt h hr
  have modpos : 0 < h%r := Nat.pos_of_ne_zero (fun hz => nd (Nat.dvd_of_mod_eq_zero hz))
  have req : h = r+k := by dsimp [r]; omega
  have dj : k < r*j ∧ r*j < h := by change _ < r*(h/r) ∧ r*(h/r) < _; omega
  have jj : 2*j ≤ h := (Nat.mul_le_mul_right j hr2).trans dj.2.le
  let A := h-j-1
  let B := h+k-2*j
  have ha0 : A+j+1 = h := by dsimp [A]; omega
  have hb0 : B+2*j = h+k := by dsimp [B]; omega
  have haR : (A:ℝ)+j+1 = h := by exact_mod_cast ha0
  have hbR : (B:ℝ)+2*j = h+k := by exact_mod_cast hb0
  have hrR : (h:ℝ) = r+k := by exact_mod_cast req
  have d₁ : (k:ℝ) < (r:ℝ)*j ∧ (r:ℝ)*j < h := by exact_mod_cast dj
  have hh : 0 < (h:ℝ) := by exact_mod_cast hk.trans kh
  have hm : (h:ℝ) < h+k := by exact_mod_cast (show h < h+k by omega)
  have dk₁ : (h:ℝ)*(2*j)-(h+k)*j = r*j := by nlinarith only [congrArg (·*(j:ℝ)) hrR]
  have dk₀ : (h:ℝ)*B-(h+k)*A = (h+k)-r*j := by
    nlinarith only [congrArg ((h:ℝ)*·) hbR, congrArg (((h:ℝ)+k)*·) haR, dk₁]
  obtain ⟨u,u0,uA,uA',uB,uB'⟩ := coordinate hh hm
    (show 1 ≤ (B:ℝ) by exact_mod_cast (show 1 ≤ B by omega))
    (show 0 < (h:ℝ)*B-(h+k)*A by rw [dk₀]; linarith [d₁.2])
    (show (h:ℝ)*B-(h+k)*A < h by rw [dk₀]; linarith [d₁.1])
  obtain ⟨v,v0,vA,vA',vB,vB'⟩ := coordinate hh hm
    (show 1 ≤ 2*(j:ℝ) by exact_mod_cast (show 1 ≤ 2*j by omega))
    (show 0 < (h:ℝ)*(2*j)-(h+k)*j by rw [dk₁]; linarith [d₁.1])
    (show (h:ℝ)*(2*j)-(h+k)*j < h by rw [dk₁]; exact d₁.2)
  let z := (1-u-v)/3
  have zpos : 0 < z := by
    have H : 0 < (h:ℝ)*(1-u-v) := by linarith only [haR,uA',vA']
    exact div_pos (pos_of_mul_pos_right H hh.le) (by norm_num)
  let x : ℝ × ℝ := (u+z,v+z)
  have px : shares x = ![u+z,v+z,z] := by
    ext i; fin_cases i <;> simp [shares,x,z]; ring
  let a : Seats := ![A,j,1]
  let b : Seats := ![B,2*j,0]
  have old₀ : err (shares x) h a 0-err (shares x) h a 2 = h*u-A+1 := by simp [err,px,a]; ring
  have old₁ : err (shares x) h a 1-err (shares x) h a 2 = h*v-j+1 := by simp [err,px,a]; ring
  have new₀ : err (shares x) (h+k) b 2-err (shares x) (h+k) b 0 = B-(h+k:ℝ)*u := by
    simp [err,px,b]; ring
  have new₁ : err (shares x) (h+k) b 2-err (shares x) (h+k) b 1 = 2*j-(h+k:ℝ)*v := by
    simp [err,px,b]; ring
  apply open_loss (a:=a) (b:=b) (x:=x)
  · intro i; rw [px]; fin_cases i <;> simp <;> positivity
  · exact ⟨by simpa [a,Fin.sum_univ_three] using ha0,span
      (by linarith only [old₀,uA]) (by linarith only [old₀,uA'])
      (by linarith only [old₁,vA]) (by linarith only [old₁,vA'])⟩
  · refine ⟨by simpa [b,Fin.sum_univ_three] using hb0,fun i j => ?_⟩
    have s := span (e:=fun i => -err (shares x) (h+k) b i)
      (by linarith only [new₀,uB']) (by linarith only [new₀,uB])
      (by linarith only [new₁,vB']) (by linarith only [new₁,vB]) j i
    linarith only [s]
  · exact ⟨2,by change 0 < (1:ℕ); decide⟩

end McCuneSeatJumps
