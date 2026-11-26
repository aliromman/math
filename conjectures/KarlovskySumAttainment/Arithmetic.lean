module

public import conjectures.KarlovskySumAttainment.Statement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace KarlovskySumAttainment
open Finset
open scoped BigOperators

def tri (k : ℕ) := ∑ i : Fin k, (i.val+1)

theorem tri_twice (k : ℕ) : 2*tri k=k*(k+1) := by
  induction k with
  | zero => simp [tri]
  | succ k ih =>
    have eq : tri (k+1)=tri k+(k+1) := by
      simp [tri,Fin.sum_univ_castSucc]
    rw [eq]
    nlinarith only [ih]

/-- For k increasing entries, the product grows at least k! / k times
    as fast as their sum moves above the sum of 1 through k. -/
theorem prefix_growth (k : ℕ) (x : Fin k → ℕ) (low : ∀ i, i.val+1 ≤ x i) :
    ∃ E G : ℕ, (∑ i,x i)=tri k+E ∧ (∏ i,x i)=k.factorial+G ∧
      k.factorial*E ≤ k*G := by
  induction k with
  | zero => exact ⟨0,0,by simp [tri],by simp,by simp⟩
  | succ k ih =>
    obtain ⟨E,G,hs,hp,le⟩ := ih (fun i => x i.castSucc) (fun i => low i.castSucc)
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (low (Fin.last k))
    change x (Fin.last k) = k+1+d at hd
    refine ⟨E+d, G*(k+1)+(k.factorial+G)*d, ?_, ?_, ?_⟩
    · rw [Fin.sum_univ_castSucc,hs,hd]
      simp only [tri,Fin.sum_univ_castSucc (fun i : Fin (k+1) => i.val+1),Fin.val_castSucc,
        Fin.val_last]
      omega
    · rw [Fin.prod_univ_castSucc,hp,hd,Nat.factorial_succ]
      ring
    · rw [Nat.factorial_succ]
      have t := Nat.mul_le_mul_left (k+1) le
      nlinarith only [t,Nat.zero_le (G*d*(k+1)),Nat.zero_le (G*(k+1))]

theorem rank_lower {n : ℕ} {x : Fin n → ℕ} (pos : ∀ i,0<x i) (inc : StrictMono x)
    (i : Fin n) : i.val+1 ≤ x i := by
  obtain ⟨j,hj⟩ := i
  induction j with
  | zero => exact pos ⟨0,hj⟩
  | succ j ih =>
    have h := inc (show (⟨j,by omega⟩ : Fin n) < ⟨j+1,hj⟩ from Nat.lt_succ_self _)
    exact (ih (by omega)).trans_lt h

/-- The integer gap between the penultimate partial product and F determines
    the bound. Any gap greater than one makes the inequality strict. -/
private theorem gap_bound {F d K C T S : ℕ} (hd : 0<d) (large : d<F*(F+C))
    (rel : d*S=(F+d)*T) (est : K*T ≤ F+d+C) :
    K*S ≤ (F+1)*(F+1+C) ∧
      (K*S=(F+1)*(F+1+C) → d=1 ∧ K*T=F+d+C) := by
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨g,hg⟩ := Nat.exists_eq_add_of_le large
  have id : d*((F+1)*(F+1+C)) = (F+d)*(F+d+C) + j*(g+1) := by
    change F*(F+C)=d+1+g at hg
    rw [hj] at hg ⊢
    nlinarith only [congrArg (fun a : ℕ => j*a) hg]
  have lower : d*(K*S) ≤ (F+d)*(F+d+C) := by
    calc
      _ = (F+d)*(K*T) := by rw [←Nat.mul_left_comm,rel]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ est
  constructor
  · exact Nat.le_of_mul_le_mul_left (lower.trans (id ▸ Nat.le_add_right _ _)) hd
  · intro equal
    rw [equal,id] at lower
    have z : j*(g+1)=0 := by omega
    have je : j=0 := (Nat.mul_eq_zero.mp z).resolve_right (by omega)
    have one : d=1 := by omega
    refine ⟨one,?_⟩
    have exactprod : (F+d)*(K*T) = (F+d)*(F+d+C) := calc
      _ = d*(K*S) := by rw [Nat.mul_left_comm d K,rel]; ring
      _ = (F+d)*(F+d+C) := by rw [equal,id,je]; simp
    exact Nat.eq_of_mul_eq_mul_left (by omega) exactprod

theorem upper_nat (k F : ℕ) :
    ((k.factorial:ℚ)*upper k F)=(F+1 : ℚ)*(F+1+(k.factorial:ℚ)*tri k) := by
  have tri' : 2*(tri k:ℚ)=(k:ℚ)*(k+1) := by exact_mod_cast tri_twice k
  have pos : (0:ℚ)<k.factorial := by exact_mod_cast k.factorial_pos
  unfold upper
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  nlinarith only [congrArg (fun a : ℚ => ((F:ℚ)+1)*k.factorial*a) tri']

private theorem large_gap {k F d : ℕ} (hk : 2≤k) (hF : 0<F) (bound : d≤(k+1)*F) :
    d < F*(F+k.factorial*tri k) := by
  have hi := Nat.mul_le_mul_right (k+1) hk
  have tr : k+1 ≤ tri k := by have := tri_twice k; omega
  have kf := Nat.mul_le_mul_right (tri k) (Nat.succ_le_of_lt k.factorial_pos)
  have h' : k+1 < F+k.factorial*tri k := by omega
  have h'' := Nat.mul_lt_mul_of_pos_left h' hF
  rw [Nat.mul_comm F (k+1)] at h''
  exact bound.trans_lt h''

theorem core_bound {k F : ℕ} (hk : 2≤k) (hF : 0<F)
    {x : Fin (k+2) → ℕ} (sol : Solution F x) :
    let y:=x (Fin.last k).castSucc
    let z:=x (Fin.last (k+1))
    let A:=fun i : Fin k => x i.castSucc.castSucc
    let all:=∑ i,x i
    k.factorial*all ≤ (F+1)*(F+1+k.factorial*tri k) ∧
      (k.factorial*all = (F+1)*(F+1+k.factorial*tri k) →
        F+1=k.factorial*y ∧ k<y ∧ (∑ i,A i)=tri k ∧ z=F*(tri k+y)) := by
  dsimp only
  let A:=fun i : Fin k => x i.castSucc.castSucc
  let y:=x (Fin.last k).castSucc
  let z:=x (Fin.last (k+1))
  let T:=(∑ i,A i)+y
  let Q:=(∏ i,A i)*y
  let K:=k.factorial
  let C:=K*tri k
  obtain ⟨pos,inc,eq⟩ := sol
  have rank := rank_lower pos inc
  obtain ⟨E,G,es,pg,eg⟩ := prefix_growth k A (fun i => rank i.castSucc.castSucc)
  have ky : k<y := rank (Fin.last k).castSucc
  have yp : 0<y := pos _
  have zp : 0<z := pos _
  have tp : 0<T := Nat.add_pos_right _ yp
  have st : (∑ i,x i)=T+z := by
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  have pr : (∏ i,x i)=Q*z := by
    rw [Fin.prod_univ_castSucc,Fin.prod_univ_castSucc]
  rw [pr,st] at eq
  have qf : F<Q := by
    by_contra! h
    have := Nat.mul_le_mul_right z h
    nlinarith only [eq,this,Nat.mul_pos hF tp]
  obtain ⟨d,eqQ⟩ := Nat.exists_eq_add_of_le qf.le
  have dp : 0<d := by omega
  have gap : d*z=F*T := by rw [eqQ] at eq; nlinarith
  have tbound : T ≤ (k+1)*z := by
    change (∑ i : Fin k,x i.castSucc.castSucc)+x (Fin.last k).castSucc ≤ _
    rw [←Fin.sum_univ_castSucc (fun i : Fin (k+1) => x i.castSucc)]
    calc
      _ ≤ ∑ _ : Fin (k+1), z := sum_le_sum fun i _ => inc.monotone (Fin.le_last _)
      _ = _ := by simp
  have db : d≤(k+1)*F := by
    apply Nat.le_of_mul_le_mul_right _ zp
    rw [gap]
    calc
      _ ≤ F*((k+1)*z) := Nat.mul_le_mul_left _ tbound
      _ = _ := by ring
  have est : K*T≤Q+C := by
    dsimp only [T,Q,C,K]
    rw [es,pg]
    have mult := Nat.mul_le_mul_right G ky.le
    nlinarith only [eg,mult]
  have ds : d*(T+z) = (F+d)*T := by nlinarith only [gap]
  have h := gap_bound (K:=K) (C:=C) dp (large_gap hk hF db) ds (by rwa [←eqQ])
  rw [st]
  refine ⟨h.1,fun exact' => ?_⟩
  obtain ⟨one,tight⟩ := h.2 exact'
  have tQ : K*T = Q+C := by simpa only [←eqQ] using tight
  have gz : G=0 := by
    by_contra! gp
    have lt := Nat.mul_lt_mul_of_pos_right ky (Nat.pos_of_ne_zero gp)
    change K*((∑ i,A i)+y)=(∏ i,A i)*y+K*tri k at tQ
    dsimp only [K] at tQ
    rw [es,pg] at tQ
    nlinarith only [tQ,eg,lt]
  have ez : E=0 := by
    rw [gz,Nat.mul_zero] at eg
    exact (Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero eg)).resolve_left k.factorial_ne_zero
  have P : (∏ i,A i)=k.factorial := by simpa only [gz,add_zero] using pg
  have S : (∑ i,A i)=tri k := by simpa only [ez,add_zero] using es
  refine ⟨by simpa only [Q,P,one] using eqQ.symm,ky,S,?_⟩
  simpa only [one,one_mul,T,S] using gap

theorem sum_le {k F : ℕ} (hk : 2≤k) (hF : 0<F)
    {x : Fin (k+2) → ℕ} (sol : Solution F x) : ((∑ i,x i) : ℕ) ≤ upper k F := by
  have h := (core_bound hk hF sol).1
  have pos : (0:ℚ)<k.factorial := by exact_mod_cast k.factorial_pos
  apply le_of_mul_le_mul_left _ pos
  rw [upper_nat]
  exact_mod_cast h

end KarlovskySumAttainment
