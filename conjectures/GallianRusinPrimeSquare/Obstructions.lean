module

public import conjectures.GallianRusinPrimeSquare.Factors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
namespace GallianRusinPrimeSquare
open Polynomial Finset

private def Jet (P : ℤ[X]) (v : ℤ) : Prop := P.coeff 0=1 ∧ P.coeff 1=v

private theorem linear_coeff (P Q : ℤ[X]) :
    (P*Q).coeff 1=P.coeff 0*Q.coeff 1+P.coeff 1*Q.coeff 0 := by
  simp [coeff_mul,Finset.Nat.antidiagonal_succ]

private theorem Jet.mul {P Q : ℤ[X]} {u v : ℤ} (h : Jet P u) (g : Jet Q v) :
    Jet (P*Q) (u+v) := ⟨by simp [h.1,g.1],by simp [linear_coeff,h.1,h.2,g.1,g.2,add_comm]⟩

private theorem Jet.pow {P : ℤ[X]} {u : ℤ} (h : Jet P u) (e : ℕ) :
    Jet (P^e) (e*u) := by
  induction e with
  | zero => simp [Jet,coeff_one]
  | succ e ih => simpa [pow_succ,add_mul] using ih.mul h

private theorem Jet.quot {P Q : ℤ[X]} {u v : ℤ} (h : Jet (P*Q) u) (g : Jet Q v) :
    Jet P (u-v) := by
  have h0 := h.1
  simp [g.1] at h0
  have h1 := h.2
  simp [linear_coeff,g.1,g.2,h0] at h1
  exact ⟨h0,by omega⟩

private theorem geom_jet {r : ℕ} (hr : 1<r) : Jet (geom r 1) 1 := by
  simp [Jet,geom_coeff (by decide : 0<1),hr,show 0<r by omega]

private theorem wide_jet {r s : ℕ} (hr : 0<r) (hs : 1<s) : Jet (geom r s) 0 :=
  ⟨by simpa using geom_low hr (by omega : 0<s) 0 (by omega),
   by simpa [coeff_one] using geom_low hr (by omega : 0<s) 1 hs⟩

/-- The linear coefficient is a+1-c. -/
theorem first_bound {p q a b c d : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (hn : NN (product p q a b c d)) : c≤a+1 := by
  have pq : 1<p*q := by nlinarith [hp.two_le,hq.two_le]
  have A := geom_jet hp.one_lt
  have B := wide_jet hp.pos hp.one_lt
  have Q := geom_jet hq.one_lt
  have C : Jet (F (p*q)) (0-1) := Jet.quot (pair_geom hp hq hne ▸ wide_jet hp.pos hq.one_lt) A
  have D : Jet (F (p^2*q)) (0-0) := Jet.quot (tall_geom hp hq hne ▸ wide_jet hp.pos pq) B
  have e := ((((Q.mul (A.pow a)).mul (B.pow b)).mul (C.pow c)).mul (D.pow d)).2
  have v := hn 1
  change 0≤_ at v
  unfold product at v
  rw [e] at v
  omega

/-- Remove copies of the largest factor without changing positivity below pq. -/
private theorem first_nonneg {p q a b c d e : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (he : e≤d) (hn : NN (product p q a b c d)) {k : ℕ} (hk : k<p*q) :
    0≤(product p q a b c e).coeff k := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le he
  have eq : product p q a b c e * geom p (p*q)^l =
      product p q a b c (e+l) * geom p p^l := by
    rw [←tall_geom hp hq hne]
    simp only [product,mul_pow,pow_add]
    ring
  have small := ((geom_low hp.pos (Nat.mul_pos hp.pos hq.pos)).pow l).congr_left
    (product p q a b c e) k hk
  rw [eq,one_pow,mul_one] at small
  exact small ▸ (hn.mul ((geom_nn hp.pos).pow l) k)

private theorem tall_shift {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    (1-X^(p^2))*F (p^2*q)=(1-X^p)*geom p (p*q) := by
  calc
    _ = ((1-X^p)*geom p p)*F (p^2*q) := by rw [geom_shift,pow_two]
    _ = _ := by rw [mul_assoc,mul_comm (geom p p),tall_geom hp hq hne]

private theorem zero_prefix {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    Prefix (p*q) ((1-X^(p^2))*product p q a b 0 (b+1))
      ((1-X^q)*geom p 1^(a+1)) := by
  have cross : (1-X^p)*geom q 1=(1-X^q)*geom p 1 := by
    have sq := geom_shift q 1
    have sp := geom_shift p 1
    simp only [pow_one,one_mul] at sq sp
    rw [←sp,←sq]
    ac_rfl
  have split0 : product p q a b 0 (b+1)=geom q 1*geom p 1^a*geom p (p*q)^b*F (p^2*q) := by
    rw [product,pow_zero,mul_one,pow_succ (F _) b,←tall_geom hp hq hne,mul_pow]
    ac_rfl
  have eq : (1-X^(p^2))*product p q a b 0 (b+1) =
      (1-X^q)*geom p 1^(a+1)*geom p (p*q)^(b+1) := by
    calc
      _ = ((1-X^(p^2))*F (p^2*q))*(geom q 1*geom p 1^a*geom p (p*q)^b) := by rw [split0]; ac_rfl
      _ = ((1-X^p)*geom q 1)*(geom p 1^a*geom p (p*q)^b*geom p (p*q)) := by
        rw [tall_shift hp hq hne]; ac_rfl
      _ = _ := by rw [cross,pow_succ (geom p 1) a,pow_succ (geom p (p*q)) b]; ac_rfl
  rw [eq]
  simpa using ((geom_low hp.pos (Nat.mul_pos hp.pos hq.pos)).pow (b+1)).congr_left
    ((1-X^q)*geom p 1^(a+1))

private theorem positive_prefix {p q t u b : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    {k : ℕ} (hs : k<p^2) (hm : k<p*q) :
    (product p q (t+u) b (u+1) (b+2)).coeff k =
    ((1-X^p)*(geom p 1^t*geom p q^u)).coeff k := by
  let B := geom p 1^t*geom p q^u
  have e : product p q (t+u) b (u+1) (b+2) =
      B*geom q (p^2)*geom p (p*q)^b*F (p^2*q) := by
    dsimp [B]
    rw [←tall_geom' hp hq hne,←pair_geom' hp hq hne,←pair_geom hp hq hne,←tall_geom hp hq hne]
    simp only [product,pow_add,pow_one,pow_two,mul_pow]
    ring
  have et : (1-X^(p^2))*product p q (t+u) b (u+1) (b+2)=
      (1-X^p)*B*geom q (p^2)*geom p (p*q)^(b+1) := by
    calc
      _ = ((1-X^(p^2))*F (p^2*q))*(B*geom q (p^2)*geom p (p*q)^b) := by rw [e]; ac_rfl
      _ = _ := by rw [tall_shift hp hq hne,pow_succ (geom p (p*q)) b]; ac_rfl
  have ek := congrArg (fun U : ℤ[X] ↦ U.coeff k) et
  have r := ((geom_low hp.pos (Nat.mul_pos hp.pos hq.pos)).pow (b+1)).congr_left
    ((1-X^p)*B*geom q (p^2)) k hm
  have s := (geom_low hq.pos (pow_pos hp.pos _)).congr_left ((1-X^p)*B) k hs
  simpa only [coeff_shift,ite_eq_right hs.not_ge,sub_zero,r,one_pow,mul_one,s] using ek

private theorem drop {p q t u : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (size : t+u≤2) :
    ∃ k<2*p, ((1-X^p)*(geom p 1^t*geom p q^u)).coeff k<0 := by
  have pp := hp.two_le
  have qq := hq.two_le
  have nd : ¬q∣p := fun h ↦ hne ((Nat.dvd_prime hp).mp h |>.resolve_left hq.ne_one).symm
  by_cases hu : u=0
  · subst u
    simp only [pow_zero,mul_one]
    by_cases ht : t≤1
    · refine ⟨p,by omega,?_⟩
      rw [coeff_shift,ite_eq_left (le_refl p),Nat.sub_self,
        (geom_power_support hp.pos t p).2 (by have h := Nat.mul_le_mul_right (p-1) ht; simp only [one_mul] at h; omega)]
      have h := (geom_power_support hp.pos t 0).1.mpr (Nat.zero_le _)
      omega
    · have ht : t=2 := by omega
      subst t
      refine ⟨2*p-1,by omega,?_⟩
      rw [coeff_shift,ite_eq_left (by omega), (square_window pp).2]
      have h := (geom_power_support hp.pos 2 (2*p-1-p)).1.mpr (by omega)
      omega
  · by_cases ht : t=0
    · subst t
      refine ⟨p,by omega,?_⟩
      simp only [pow_zero,one_mul,coeff_shift,ite_eq_left (le_refl p),Nat.sub_self]
      have e : geom p q^u = expand ℤ q (geom p 1^u) := by rw [map_pow,expand_geom,mul_one]
      rw [e,coeff_expand hq.pos,ite_eq_right nd,coeff_expand hq.pos,ite_eq_left (dvd_zero _),
        Nat.zero_div]
      have h := (geom_power_support hp.pos u 0).1.mpr (Nat.zero_le _)
      omega
    · have t1 : t=1 := by omega
      have u1 : u=1 := by omega
      subst t; subst u
      let h := p/q
      let r := p%q
      have hr : 0<r := by dsimp [r]; exact Nat.pos_of_ne_zero fun z ↦ nd (Nat.dvd_of_mod_eq_zero z)
      have rq : r<q := Nat.mod_lt _ hq.pos
      have eq : p=q*h+r := (Nat.div_add_mod p q).symm
      have ub : 2*h<p := by have := Nat.mul_le_mul_right h qq; omega
      refine ⟨p+q*h,by omega,?_⟩
      simp only [pow_one,coeff_shift,ite_eq_left (Nat.le_add_right p (q*h)),Nat.add_sub_cancel_left]
      rw [window_high hq.pos rq eq ub,window_low hq.pos (by omega)]
      omega

theorem upper_positive {p q a b c d : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (hab : a+b=2) (hc : 0<c) (hn : NN (product p q a b c d)) : d≤b+1 := by
  have ca := first_bound hp hq hne hn
  let u := c-1
  let t := a-u
  have e : a=t+u := by dsimp [t,u]; omega
  have f : c=u+1 := by dsimp [u]; omega
  obtain ⟨k,hk,neg⟩ := drop (p:=p) (q:=q) (t:=t) (u:=u) hp hq hne (by omega)
  have hs : k<p^2 := by rw [pow_two]; exact hk.trans_le (Nat.mul_le_mul_right _ hp.two_le)
  have hm : k<p*q := hk.trans_le ((Nat.mul_le_mul_right p hq.two_le).trans_eq (Nat.mul_comm _ _))
  by_contra! high
  have bound := first_nonneg hp hq hne (e:=b+2) (by omega) hn hm
  rw [e,f,positive_prefix hp hq hne hs hm] at bound
  omega

/-- Move a positive coefficient past the end of its support in one period. -/
private theorem span_drop {p q s N : ℕ} (pp : 2≤p) (nd : ¬s∣q)
    (span : N+1<s) (short : N+1<p*q) :
    ∃ j, j<s ∧ j≤N ∧ N<(q+j)%s ∧ q+j<p*q := by
  let r := q%s
  have sr : 0<r := Nat.pos_of_ne_zero fun e ↦ nd (Nat.dvd_of_mod_eq_zero e)
  have rs : r<s := Nat.mod_lt _ (by omega)
  let j := N+1-r
  have js : j<s := by dsimp [j]; omega
  have jn : j≤N := by dsimp [j]; omega
  have pos : N<r+j := by dsimp [j]; omega
  have end' : r+j<s := by dsimp [j]; omega
  refine ⟨j,js,jn,?_,?_⟩
  · rw [Nat.add_mod,Nat.mod_eq_of_lt js]
    change N<(r+j)%s
    rwa [Nat.mod_eq_of_lt end']
  · have twice := Nat.mul_le_mul_right q pp
    by_cases small : q<s
    · have h : r=q := Nat.mod_eq_of_lt small
      dsimp [j]
      rw [h]
      omega
    · omega

private theorem short_cube {p : ℕ} (hp : 2≤p) :
    ((1-X^2)*geom p 1^3).coeff (2*p-1)<0 := by
  let C := geom p 1^2
  have e : (1-X^2)*geom p 1^3=(1-X^p)*((1+X)*C) := by
    have h := geom_shift p 1
    simp only [pow_one,one_mul] at h
    change (1-X^2)*geom p 1^3=(1-X^p)*((1+X)*geom p 1^2)
    rw [←h]
    ring
  have coeff (k : ℕ) (hk : 1≤k) : ((1+X)*C).coeff k=C.coeff k+C.coeff (k-1) := by
    rw [add_mul,one_mul,coeff_add,←pow_one (X:ℤ[X]),coeff_X_pow_mul',ite_eq_left hk]
  rw [e,coeff_shift,ite_eq_left (by omega),coeff _ (by omega),coeff _ (by omega)]
  have square := square_window hp
  have e1 : 2*p-1-1=2*p-2 := by omega
  have e2 : 2*p-1-p=p-1 := by omega
  have c1 := (geom_power_support (by omega : 0<p) 2 (p-1)).1.mpr (by omega)
  have c2 := (geom_power_support (by omega : 0<p) 2 (p-1-1)).1.mpr (by omega)
  dsimp only [C]
  rw [e1,e2,square.1,square.2]
  omega

private theorem exceptional {q : ℕ} (hq : q.Prime) (hne : q≠2) :
    ∃ j<4, q+j<2*q ∧
      (geom 2 1^3).coeff ((q+j)%4)<(geom 2 1^3).coeff j := by
  have hq3 : 3≤q := by have := hq.two_le; omega
  obtain ⟨v,hv⟩ := hq.odd_of_ne_two hne
  have r : q%4=1 ∨ q%4=3 := by omega
  have e : geom 2 1^3=(1+3*X+3*X^2+X^3:ℤ[X]) := by
    norm_num [geom,sum_range_succ]
    ring
  have c1 : (geom 2 1^3).coeff 1=3 := by norm_num [e,coeff_X,coeff_X_pow,coeff_one]
  have c2 : (geom 2 1^3).coeff 2=3 := by norm_num [e,coeff_X,coeff_X_pow,coeff_one]
  have c3 : (geom 2 1^3).coeff 3=1 := by norm_num [e,coeff_X,coeff_X_pow,coeff_one]
  have c0 : (geom 2 1^3).coeff 0=1 := by norm_num [e,coeff_X,coeff_X_pow,coeff_one]
  rcases r with first|last
  · exact ⟨2,by decide,by omega,by rw [show (q+2)%4=3 by omega,c2,c3]; decide⟩
  · exact ⟨1,by decide,by omega,by rw [show (q+1)%4=0 by omega,c0,c1]; decide⟩

theorem upper_zero {p q a b d : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (hab : a+b=2) (hn : NN (product p q a b 0 d)) : d≤b := by
  by_contra! bad
  let P := product p q a b 0 (b+1)
  have nn {k : ℕ} (hk : k<p*q) : 0≤P.coeff k := first_nonneg hp hq hne (by omega) hn hk
  have e := zero_prefix (a:=a) (b:=b) hp hq hne
  have pp := hp.two_le
  have qq := hq.two_le
  have pos := hp.pos
  let N := (a+1)*(p-1)
  have N3 : N≤3*(p-1) := Nat.mul_le_mul_right _ (by omega)
  have span : N<p^2 := by
    obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le pp
    have w : p-1=v+1 := by omega
    rw [w] at N3
    rw [hv,pow_two]
    nlinarith
  have z (k : ℕ) (hk : p^2≤k) : (geom p 1^(a+1)).coeff k=0 :=
    (geom_power_support pos _ k).2 (by change N<k; omega)
  have drop (j : ℕ) (js : j<p^2) (bound : q+j<p*q) :
      (geom p 1^(a+1)).coeff j ≤ (geom p 1^(a+1)).coeff ((q+j)%p^2) := by
    have eq := periodic_coeff (pow_pos pos 2) z e bound
    have val := nn bound
    change 0≤(product p q a b 0 (b+1)).coeff _ at val
    rw [eq,delta,lag,ite_eq_left (Nat.le_add_right q j),Nat.add_sub_cancel_left,Nat.mod_eq_of_lt js] at val
    omega
  by_cases ep : p=2 ∧ a=2
  · obtain ⟨rfl,rfl⟩ := ep
    obtain ⟨j,hj,hb,hc⟩ := exceptional hq hne.symm
    exact hc.not_ge (drop j hj hb)
  by_cases eq : q=2 ∧ a=2
  · obtain ⟨rfl,rfl⟩ := eq
    let k := 2*p-1
    have kh : k<p*2 := by dsimp [k]; omega
    have ks : k<p^2 := by rw [pow_two]; exact (show k<2*p by dsimp [k]; omega).trans_le (Nat.mul_le_mul_right _ pp)
    have low := e k kh
    rw [coeff_shift,ite_eq_right ks.not_ge,sub_zero] at low
    have neg := short_cube pp
    have non := nn kh
    change 0≤(product p 2 2 b 0 (b+1)).coeff k at non
    rw [low] at non
    exact neg.not_ge non
  have span' : N+1<p^2 := by
    by_cases p2 : p=2
    · have : a+1≤2 := by omega
      have h := Nat.mul_le_mul_right (p-1) this
      dsimp [N]
      rw [p2] at h ⊢
      omega
    · have p3 : 3≤p := by omega
      obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le p3
      have w : p-1=v+2 := by omega
      rw [w] at N3
      rw [hv,pow_two]
      nlinarith
  have short : N+1<p*q := by
    by_cases q2 : q=2
    · have bound : a+1≤2 := by omega
      have := Nat.mul_le_mul_right (p-1) bound
      dsimp [N]
      rw [q2]
      omega
    · have three : 3≤q := by omega
      have := Nat.mul_le_mul_left p three
      omega
  have nd : ¬p^2∣q := by
    intro h
    have hpq : p∣q := (dvd_pow_self _ (by decide : 2≠0)).trans h
    exact hne ((Nat.dvd_prime hq).mp hpq |>.resolve_left hp.ne_one)
  obtain ⟨j,js,jn,lower,upper⟩ := span_drop pp nd span' short
  have atj := (geom_power_support pos (a+1) j).1.mpr jn
  have shifted := (geom_power_support pos (a+1) ((q+j)%p^2)).2 lower
  have h := drop j js upper
  omega

end GallianRusinPrimeSquare
