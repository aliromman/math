module

public import conjectures.CFPLogDensity.DensePairs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace CFPLogDensity
open Finset

structure ColorPairs {r : ℕ} (c n : ℕ) (χ : ℕ → Fin r) where
  color : Fin r
  d : ℕ
  stride : ℕ
  base : ℕ
  indices : Finset ℕ
  step_pos : 0<d
  stride_pos : 0<stride
  step_bound : d*stride≤2^c
  coprime : base.Coprime d
  indexed : ∀ z∈indices, z<2^n
  dense : 2^n≤2^c*indices.card
  edge : ∀ z∈indices, let x := base+d*stride*z
    2^n≤x ∧ x+d<2*2^n ∧ χ x=color ∧ χ (x+d)=color

private theorem large_fiber {V L : Type*} [DecidableEq L] [Fintype L] [Nonempty L]
    (S : Finset V) (f : V → L) : ∃ v, S.card≤Fintype.card L*(S.filter fun x => f x=v).card := by
  classical
  obtain ⟨v,_,hv⟩ := (univ : Finset L).exists_max_image
    (fun v => (S.filter fun x => f x=v).card) univ_nonempty
  refine ⟨v,?_⟩
  calc
    S.card = ∑ i : L, (S.filter fun x => f x=i).card := card_eq_sum_card_fiberwise (by simp)
    _ ≤ ∑ _i : L, (S.filter fun x => f x=v).card := sum_le_sum hv
    _ = _ := by simp

/-- In each block use r+1 terms of 1 mod (r+1)!. A repeated color gives a
fixed gap after pigeonholing both positions and the color across blocks. -/
theorem color_pairs (r : ℕ) (hr : 0<r) :
    ∃ c : ℕ, ∀ n≥c, ∀ χ : ℕ → Fin r, Nonempty (ColorPairs c n χ) := by
  classical
  let Q := (r+1).factorial
  let B := Q*Q
  let u := 4*B+4
  let v := r*(r+1)*(r+1)+1
  let c := u+v
  have qp : 0<Q := Nat.factorial_pos _
  have qr : r<Q := by
    exact (Nat.lt_succ_self r).trans_le (Nat.le_of_dvd qp (Nat.dvd_factorial (by omega) (le_refl (r+1))))
  have bp : 0<B := Nat.mul_pos qp qp
  have bq : Q≤B := Nat.le_mul_of_pos_right Q qp
  have selfpow (x : ℕ) : x≤2^x := by
    induction x with
    | zero => decide
    | succ x ih =>
      rw [pow_succ]
      have positive : 0<2^x := by positivity
      omega
  have U : 4*B+4≤2^u := selfpow u
  have V : r*(r+1)*(r+1)≤2^v := (Nat.le_succ _).trans (selfpow v)
  refine ⟨c,?_⟩
  intro n hn χ
  let k := n-c
  let blocks := 2^(v+k)
  let first := 1+Q*(2^n/Q+1)
  have startlo : 2^n≤first := by
    have := Nat.mod_add_div (2^n) Q
    have := Nat.mod_lt (2^n) qp
    dsimp [first]
    nlinarith
  have starthi : first≤2^n+Q+1 := by
    have := Nat.mul_div_le (2^n) Q
    dsimp [first]
    nlinarith
  have dim : 2^n=2^u*blocks := by rw [show n=u+(v+k) by dsimp [k,c] at *; omega,pow_add]
  have blockpos : 0<blocks := by dsimp [blocks]; positivity
  let point (z : ℕ) (a : Fin (r+1)) := first+B*z+Q*a.val
  have repeatColor (z : ℕ) : ∃ a b : Fin (r+1), a<b ∧ χ (point z a)=χ (point z b) := by
    obtain ⟨a,b,ne,h⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun x => χ (point z x)) (by simp)
    rcases lt_or_gt_of_ne ne with h'|h'
    · exact ⟨a,b,h',h⟩
    · exact ⟨b,a,h',h.symm⟩
  choose left right ltPoint sameColor using repeatColor
  let label (z : ℕ) := (χ (point z (left z)),left z,right z)
  let : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  obtain ⟨⟨i,a,b⟩,he⟩ := large_fiber (range blocks) label
  let I := (range blocks).filter fun z => label z=(i,a,b)
  change (range blocks).card≤Fintype.card (Fin r × Fin (r+1) × Fin (r+1))*I.card at he
  simp only [card_range,Fintype.card_prod,Fintype.card_fin] at he
  have ip : I.Nonempty := by
    apply card_pos.mp
    by_contra! h
    rw [show I.card=0 by omega] at he
    simp at he
    omega
  have label_at (z) (hz : z∈I) : χ (point z a)=i ∧ left z=a ∧ right z=b := by
    have h := (mem_filter.mp hz).2
    change (χ (point z (left z)),left z,right z)=(i,a,b) at h
    simp only [Prod.mk.injEq] at h
    exact ⟨h.2.1 ▸ h.1,h.2⟩
  obtain ⟨z,hz⟩ := ip
  have ab : a<b := by simpa only [(label_at z hz).2.1,(label_at z hz).2.2] using ltPoint z
  let h := b.val-a.val
  have hpos : 0<h := by dsimp [h]; omega
  have hle : h≤r+1 := by have := b.isLt; dsimp [h]; omega
  obtain ⟨m,hm⟩ := Nat.dvd_factorial hpos hle
  change Q=h*m at hm
  have mp : 0<m := by by_contra! m0; simp [show m=0 by omega] at hm; omega
  let d := Q*h
  have db : d*m=B := by dsimp [d,B]; rw [Nat.mul_assoc,←hm]
  have cb : B≤2^c := by
    have : 2^u≤2^c := Nat.pow_le_pow_right (by decide) (Nat.le_add_right u v)
    omega
  let base := first+Q*a.val
  have coQ : base.Coprime Q := by
    have e : base=1+Q*(2^n/Q+1+a.val) := by dsimp [base,first]; ring
    simp [e]
  have co : base.Coprime d := coQ.mul_right (coQ.of_dvd_right ⟨m,hm⟩)
  refine ⟨⟨i,d,m,base,I,Nat.mul_pos qp hpos,mp,db ▸ cb,co,?_,?_,?_⟩⟩
  · intro t ht
    have htr := mem_range.mp (mem_filter.mp ht).1
    rw [dim]
    exact htr.trans_le (Nat.le_mul_of_pos_left blocks (by positivity))
  · rw [dim,show 2^c=2^u*2^v from pow_add _ _ _]
    refine (Nat.mul_le_mul_left (2^u) he).trans ?_
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (2^u) (Nat.mul_le_mul_right I.card V)
  · intro t ht
    have hl := label_at t ht
    have firstPoint : base+d*m*t=point t a := by dsimp [base,point]; rw [db]; omega
    have lastPoint : base+d*m*t+d=point t b := by
      rw [firstPoint]
      dsimp [point,d]
      have : a.val+h=b.val := by dsimp [h]; omega
      rw [←this,Nat.mul_add]
      omega
    dsimp only
    rw [lastPoint,firstPoint]
    refine ⟨by dsimp [point]; omega,?_,hl.1,?_⟩
    · have tlt := mem_range.mp (mem_filter.mp ht).1
      have tb := Nat.mul_le_mul_left B (show t+1≤blocks by omega)
      have br := Nat.mul_le_mul_left Q (show b.val≤Q by have := b.isLt; omega)
      have ub := Nat.mul_le_mul_right blocks U
      have Bsmall : B≤B*blocks := Nat.le_mul_of_pos_right B blockpos
      dsimp [point]
      rw [dim] at starthi ⊢
      change Q*b.val≤B at br
      nlinarith
    · simpa only [hl.2.1,hl.2.2] using (sameColor t).symm.trans (by simpa only [hl.2.1] using hl.1)

end CFPLogDensity
