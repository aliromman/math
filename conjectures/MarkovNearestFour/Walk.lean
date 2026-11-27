module

public import conjectures.MarkovNearestFour.Exchange
public import conjectures.MarkovNearestFour.Leading
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation

@[expose] public section
namespace MarkovNearestFour
open MarkovFactorFour
open PowerSeries

noncomputable def specialize (a b : ℕ) : Poly →+* Series :=
  MvPolynomial.eval₂Hom (Int.castRingHom Series) ![z^b,z^a]

def weight (a b : ℕ) (p : Vertex) : ℕ := b*p.a+a*p.b

private theorem weight_center (a b : ℕ) (T : Triangle) :
    weight a b (center T) = weight a b T.left+weight a b T.right := by
  simp only [weight,center,Nat.mul_add]
  omega

private theorem specialized_det (a b : ℕ) (p : Vertex) :
    specialize a b (det p)=z^(weight a b p) := by
  simp [specialize,det,weight,pow_add,pow_mul]

private abbrev Good (a b : ℕ) (p : Vertex) (d : ℕ) : Prop :=
  Profile (specialize a b p.num) (weight a b p) d

private theorem coprime_tie {l r : ℕ} (h : l.Coprime r) (e : l=r) : l=1 := by
  simpa [e,Nat.Coprime] using h

/-- Along the Farey path the two distances are the Euclidean remainders. -/
private theorem along (a b l r : ℕ) (hl : 0<l) (hr : 0<r) (cop : l.Coprime r)
    (T : Triangle) (bal : Balanced T) (hL : Good a b T.left r)
    (hR : Good a b T.right l) (hM : Good a b (center T) (Nat.dist l r)) :
    Good a b (center (follow T (path l r))) 0 := by
  rw [path]
  split
  · rename_i he
    have : l=r := by omega
    simpa [this,follow] using hM
  · rename_i he
    split
    · rename_i hgt
      have hc := (Nat.coprime_sub_self_left hgt.le).2 cop
      have hd := Nat.dist_eq_sub_of_le_right hgt.le
      apply along a b (l-r) r (by omega) hr hc (leftChild T) (balanced_left T bal) hL
      · simpa only [leftChild,hd] using hM
      · have eq := congrArg (specialize a b) (exchange_left T bal)
        simp only [map_mul,map_add,map_pow,specialized_det] at eq
        have mid : Profile (specialize a b T.middle)
            (weight a b T.left+weight a b T.right) (l-r) := by
          rw [←weight_center,←hd]
          exact hM
        have H := exchange_profile (weight a b T.left) (weight a b T.right) r (l-r) hr
          (by omega) (coprime_tie hc.symm) hL
          (show Profile _ _ (r+(l-r)) by simpa only [show r+(l-r)=l by omega] using hR) mid eq
        change Profile (specialize a b (leftChild T).middle) (weight a b (center (leftChild T))) _
        rw [weight_center]
        change Profile _ (weight a b T.left+weight a b (center T)) _
        rw [weight_center,Nat.dist_comm (l-r) r]
        simpa only [two_mul,Nat.add_assoc] using H
    · rename_i hle
      have ht : l≤r := by omega
      have hc := (Nat.coprime_sub_self_right ht).2 cop
      have hd := Nat.dist_eq_sub_of_le ht
      refine along a b l (r-l) hl (by omega) hc (rightChild T) (balanced_right T bal) ?_ hR ?_
      · simpa only [rightChild,hd] using hM
      · have eq := congrArg (specialize a b) (exchange_right T bal)
        simp only [map_mul,map_add,map_pow,specialized_det] at eq
        have mid : Profile (specialize a b T.middle)
            (weight a b T.right+weight a b T.left) (r-l) := by
          rw [Nat.add_comm,←weight_center,←hd]
          exact hM
        have H := exchange_profile (weight a b T.right) (weight a b T.left) l (r-l) hl
          (by omega) (coprime_tie hc) hR
          (show Profile _ _ (l+(r-l)) by simpa only [show l+(r-l)=r by omega] using hL) mid eq
        change Profile (specialize a b (rightChild T).middle) (weight a b (center (rightChild T))) _
        rw [weight_center]
        change Profile _ (weight a b (center T)+weight a b T.right) _
        rw [weight_center]
        simpa only [two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H
termination_by l+r

private theorem initial_leaf {w : ℕ} (hw : 1<w) : Profile 1 w w := by
  exact ⟨0,by omega,1,by simp,by simp [lead,show w≠0 by omega],
    by simp [next,show w≠0 by omega,show w≠1 by omega,coeff_one]⟩

/-- The first coefficient above the minimum weight is four at each reduced target. -/
theorem first_above (a b : ℕ) (ha : 1<a) (hab : a<b) (h : a.Coprime b) :
    PowerSeries.coeff (a*b+1) (specialize a b (numerator a b))=4 := by
  have hb : 1<b := by omega
  have hm : Good a b (center initial) (Nat.dist b a) := by
    rw [Nat.dist_eq_sub_of_le_right hab.le]
    refine ⟨a,by simp [weight,center,initial]; omega,1+z^(b-a),?_,?_,?_⟩
    · change specialize a b (u+v)=_
      simp only [specialize,map_add,MvPolynomial.eval₂Hom_X',Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [mul_add,mul_one,←pow_add,show a+(b-a)=b by omega,add_comm]
    · simp [lead,show b-a≠0 by omega]
    · simp [next,show b-a≠0 by omega,coeff_one,coeff_X_pow,eq_comm (a:=1) (b:=b-a)]
  have H := along a b b a (by omega) (by omega) h.symm initial balanced_initial
    (by simpa [Good,specialize,initial,weight] using initial_leaf ha)
    (by simpa [Good,specialize,initial,weight] using initial_leaf hb) hm
  obtain ⟨k,hk,f,hf,_,f1⟩ := H
  have coord := selected_coordinates a b (by omega) (by omega) h
  simp only [weight,coord.1,coord.2,Nat.mul_comm b a] at hk
  have kval : k=a*b := by omega
  change specialize a b (numerator a b)=z^k*f at hf
  rw [hf,kval,Nat.add_comm,coeff_X_pow_mul]
  exact f1

end MarkovNearestFour
