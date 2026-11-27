module

public import Mathlib.Data.Nat.Dist
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.Ring

@[expose] public section
namespace MarkovNearestFour
open PowerSeries

abbrev Series := PowerSeries ℤ
noncomputable abbrev z : Series := PowerSeries.X

def lead (d : ℕ) : ℤ := if d = 0 then 2 else 1
def next (d : ℕ) : ℤ := if d = 0 then 4 else if d = 1 then 1 else 0

/-- The first two coefficients after the indicated power of z. -/
def Starts (p : Series) (n : ℕ) (c e : ℤ) : Prop :=
  ∃ f : Series, p=z^n*f ∧ constantCoeff f=c ∧ coeff 1 f=e

/-- At distance d the order k satisfies 2k+d=w. -/
def Profile (p : Series) (w d : ℕ) : Prop :=
  ∃ k, 2*k+d=w ∧ Starts p k (lead d) (next d)

private theorem cancel_initial {p q : Series} {m n : ℕ} {c d : ℤ}
    (h₁ : Starts p m 1 0) (h₂ : Starts (p*q) (m+n) c d) : Starts q n c d := by
  obtain ⟨a,pa,ac,ad⟩ := h₁
  obtain ⟨b,pb,bc,bd⟩ := h₂
  have h : a*q=z^n*b := by
    apply mul_left_cancel₀ (show z^m≠0 from pow_ne_zero _ PowerSeries.X_ne_zero)
    simpa [pa,pow_add,mul_assoc] using pb
  have unit : IsUnit a := isUnit_iff_constantCoeff.mpr (ac ▸ isUnit_one)
  obtain ⟨inv,hi⟩ := unit.exists_right_inv
  have ic : constantCoeff inv=1 := by simpa [ac] using congrArg constantCoeff hi
  have ie : coeff 1 inv=0 := by
    simpa [coeff_one_mul,ac,ad,ic,coeff_one] using congrArg (coeff 1) hi
  refine ⟨b*inv,?_,by simp [bc,ic],by simp [coeff_one_mul,bc,bd,ic,ie]⟩
  calc
    q = (a*q)*inv := by rw [mul_comm a q,mul_assoc,hi,mul_one]
    _ = z^n*(b*inv) := by rw [h,mul_assoc]

private theorem head_sum {a b : Series} {d e : ℕ} (hd : 0<d) (he : 0<e)
    (horder : e≤d) (htie : d=e → d=1)
    (ac : constantCoeff a=1) (ad : coeff 1 a=next d)
    (bc : constantCoeff b=1) (bd : coeff 1 b=next e) :
    constantCoeff (a^2 + z^(d-e)*b^2)=lead (d-e) ∧
    coeff 1 (a^2 + z^(d-e)*b^2)=next (d-e) := by
  by_cases eq : d=e
  · have d1 := htie eq
    subst e
    subst d
    simp [lead,next,coeff_one_pow,ac,ad,bc,bd]
  · have high : d≠1 := by omega
    have ne : d-e≠0 := by omega
    simp [lead,next,ne,coeff_one_mul,coeff_one_pow,coeff_X_pow,ac,bc,ad,high,hd.ne',
      eq_comm (a:=1) (b:=d-e)]

private theorem exchange_ordered {p q r n : Series} (wp wq : ℕ) (d e : ℕ)
    (hd : 0<d) (he : 0<e) (horder : e≤d) (htie : d=e → d=1)
    (hp : Profile p wp d) (hq : Profile q wq (d+e)) (hr : Profile r (wp+wq) e)
    (eq : q*n=z^wq*p^2+r^2) :
    Profile n (2*wp+wq) (d-e) := by
  obtain ⟨kp,ep,A,hp,ac,ad⟩ := hp
  obtain ⟨kq,eq',B,hq,bc,bd⟩ := hq
  obtain ⟨kr,er,C,hr,cc,cd⟩ := hr
  have hk : kq≤wq+2*kp := by omega
  let kn := wq+2*kp-kq
  refine ⟨kn,by dsimp [kn]; omega, ?_⟩
  apply cancel_initial (p:=q) (m:=kq)
  · exact ⟨B,hq,by simpa only [lead,ite_eq_right (show d+e≠0 by omega)] using bc,
      by simpa only [next,ite_eq_right (show d+e≠0 by omega),ite_eq_right (show d+e≠1 by omega)] using bd⟩
  have ha : constantCoeff A=1 := by simpa [lead,hd.ne'] using ac
  have hc : constantCoeff C=1 := by simpa [lead,he.ne'] using cc
  obtain ⟨val0,val1⟩ := head_sum hd he horder htie ha ad hc cd
  refine ⟨A^2+z^(d-e)*C^2, ?_,val0,val1⟩
  have e1 : kq+kn=wq+2*kp := by dsimp [kn]; omega
  have e2 : (wq+2*kp)+(d-e)=2*kr := by omega
  rw [eq,e1,hp,hr,mul_add,←mul_assoc,←pow_add,e2,mul_pow,mul_pow,←pow_mul,←pow_mul]
  ring_nf

/-- The positive exchange remains valid with the two terms in the other order. -/
private theorem exchange_reversed {p q r n : Series} (wp wq : ℕ) (d e : ℕ)
    (hd : 0<d) (he : 0<e) (horder : d≤e) (htie : d=e → d=1)
    (hp : Profile p wp d) (hq : Profile q wq (d+e)) (hr : Profile r (wp+wq) e)
    (eq : q*n=z^wq*p^2+r^2) :
    Profile n (2*wp+wq) (e-d) := by
  obtain ⟨kp,ep,A,hp,ac,ad⟩ := hp
  obtain ⟨kq,eq',B,hq,bc,bd⟩ := hq
  obtain ⟨kr,er,C,hr,cc,cd⟩ := hr
  let kn := 2*kr-kq
  refine ⟨kn,by dsimp [kn]; omega, ?_⟩
  apply cancel_initial (p:=q) (m:=kq)
  · exact ⟨B,hq,by simpa only [lead,ite_eq_right (show d+e≠0 by omega)] using bc,
      by simpa only [next,ite_eq_right (show d+e≠0 by omega),ite_eq_right (show d+e≠1 by omega)] using bd⟩
  have ha : constantCoeff A=1 := by simpa [lead,hd.ne'] using ac
  have hc : constantCoeff C=1 := by simpa [lead,he.ne'] using cc
  obtain ⟨val0,val1⟩ := head_sum he hd horder (fun h => h.trans (htie h.symm)) hc cd ha ad
  refine ⟨C^2+z^(e-d)*A^2, ?_,val0,val1⟩
  have e1 : kq+kn=2*kr := by dsimp [kn]; omega
  have e2 : 2*kr+(e-d)=wq+2*kp := by omega
  rw [eq,e1,hp,hr,mul_add,←mul_assoc,←pow_add,e2,mul_pow,mul_pow,←pow_mul,←pow_mul]
  ring_nf

theorem exchange_profile {p q r n : Series} (wp wq : ℕ) (d e : ℕ)
    (hd : 0<d) (he : 0<e) (htie : d=e → d=1)
    (hp : Profile p wp d) (hq : Profile q wq (d+e)) (hr : Profile r (wp+wq) e)
    (eq : q*n=z^wq*p^2+r^2) :
    Profile n (2*wp+wq) (Nat.dist d e) := by
  rcases le_total e d with h|h
  · simpa [Nat.dist, Nat.sub_eq_zero_of_le h] using
      exchange_ordered wp wq d e hd he h htie hp hq hr eq
  · simpa [Nat.dist, Nat.sub_eq_zero_of_le h] using
      exchange_reversed wp wq d e hd he h htie hp hq hr eq

end MarkovNearestFour
