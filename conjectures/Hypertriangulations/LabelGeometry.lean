module

public import conjectures.Hypertriangulations.Labels
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section
namespace Hypertriangulations
open Finset
variable {α : Type*} [DecidableEq α] (P : α→Plane) {k : ℕ}

private def mapped (r : ℝ) (t x : Plane) : Plane := r • x+t

private theorem orient_mapped (r : ℝ) (t a b c : Plane) :
    orient (mapped r t a) (mapped r t b) (mapped r t c)=r^2*orient a b c := by
  simp only [mapped,orient,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul];ring

private theorem sign_mapped (r : ℝ) (hr : r≠0) (t a b c : Plane) :
    sign (mapped r t a) (mapped r t b) (mapped r t c)=sign a b c := by
  have pos' := sq_pos_of_ne_zero hr
  simp [sign,orient_mapped,pos,pow_ne_zero 2 hr,mul_pos_iff_of_pos_left pos']

private theorem inside_mapped (r : ℝ) (hr : r≠0) (t a b c d : Plane) :
    StrictInside (mapped r t a) (mapped r t b) (mapped r t c) (mapped r t d) ↔ StrictInside a b c d := by
  have pos' := sq_pos_of_ne_zero hr
  have neg (x : ℝ) : r^2*x<0 ↔ x<0 := by simpa using (mul_lt_mul_iff_right₀ (b:=x) (c:=0) pos')
  simp only [StrictInside,orient_mapped,mul_pos_iff_of_pos_left pos',neg]

private theorem white_point (U : Finset α) {a : α} (au : a∉U) :
    average P k (insert a U)=mapped (k:ℝ)⁻¹ ((k:ℝ)⁻¹ • ∑ j∈U,P j) (P a) := by simp [mapped,average,au,smul_add]

private noncomputable def center (P : α→Plane) (k : ℕ) (X : Finset α) (a b c : α) : Plane :=
  (k:ℝ)⁻¹ • ((∑j∈X,P j)+P a+P b+P c)

private theorem black_point (X : Finset α) {a b c : α} (bu : b∉X) (cu : c∉X) (bc : b≠c) :
    average P k (insert b (insert c X))=mapped (-(k:ℝ)⁻¹) (center P k X a b c) (P a) := by
  simp [average,mapped,center,bu,cu,bc,smul_add,neg_smul];abel

omit [DecidableEq α] in
private theorem center_rotate (X : Finset α) (a b c : α) : center P k X b c a=center P k X a b c := by
  unfold center;congr 1;abel

private theorem black_points (X : Finset α) {a b c : α} (au : a∉X) (bu : b∉X) (cu : c∉X)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    let M := mapped (-(k:ℝ)⁻¹) (center P k X a b c)
    average P k (insert b (insert c X))=M (P a) ∧ average P k (insert c (insert a X))=M (P b) ∧
    average P k (insert a (insert b X))=M (P c) := by
  exact ⟨black_point P X bu cu bc,(center_rotate P X a b c) ▸ black_point P X cu au ac.symm,
    ((center_rotate P X b c a).trans (center_rotate P X a b c)) ▸ black_point P X au bu ab⟩

/-- White and black face orientations agree with the order of their three active points. -/
theorem white_sign (hk : 0<k) (U : Finset α) {a b c : α} (au : a∉U) (bu : b∉U) (cu : c∉U) :
    sign (average P k (insert a U)) (average P k (insert b U)) (average P k (insert c U))=sign (P a) (P b) (P c) := by
  rw [white_point P U au,white_point P U bu,white_point P U cu]
  exact sign_mapped _ (inv_ne_zero (by exact_mod_cast hk.ne')) _ _ _ _

theorem black_sign (hk : 0<k) (X : Finset α) {a b c : α} (au : a∉X) (bu : b∉X) (cu : c∉X)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    sign (average P k (insert b (insert c X))) (average P k (insert c (insert a X)))
      (average P k (insert a (insert b X)))=sign (P a) (P b) (P c) := by
  obtain ⟨e₁,e₂,e₃⟩ := black_points P (k:=k) X au bu cu ab ac bc
  rw [e₁,e₂,e₃]
  exact sign_mapped _ (neg_ne_zero.mpr (inv_ne_zero (by exact_mod_cast hk.ne'))) _ _ _ _

omit [DecidableEq α] in
private theorem interior_fresh {a b c d : α} (ins : StrictInside (P a) (P b) (P c) (P d)) :
    d≠a ∧ d≠b ∧ d≠c := by
  have h (x y z : Plane) : ¬StrictInside x y z x := by simp [StrictInside]
  have first : d≠a := by rintro rfl;exact h _ _ _ ins
  have second : d≠b := by rintro rfl;simp [StrictInside] at ins
  have third : d≠c := by rintro rfl;simp [StrictInside] at ins
  exact ⟨first,second,third⟩

/-- An eligible point gives a new white vertex adjacent to all three old vertices. -/
theorem white_star (hk : 0<k) (U : Finset α) {a b c d : α} (au : a∉U) (bu : b∉U) (cu : c∉U) (du : d∉U)
    (card : (insert a U).card=k) (ins : StrictInside (P a) (P b) (P c) (P d)) :
    ∃ D : Finset α,D.card=k ∧ Exchange (insert a U) D ∧ Exchange (insert b U) D ∧ Exchange (insert c U) D ∧
      StrictInside (average P k (insert a U)) (average P k (insert b U)) (average P k (insert c U)) (average P k D) := by
  obtain ⟨da,db,dc⟩ := interior_fresh P ins
  have edge {x : α} (xu : x∉U) (xd : x≠d) : Exchange (insert x U) (insert d U) := ⟨U,x,d,xu,du,xd,rfl,rfl⟩
  refine ⟨insert d U,by simpa [au,du] using card,edge au da.symm,edge bu db.symm,edge cu dc.symm,?_⟩
  rw [white_point P U au,white_point P U bu,white_point P U cu,white_point P U du]
  exact (inside_mapped _ (inv_ne_zero (by exact_mod_cast hk.ne')) _ _ _ _ _).mpr ins

/-- For a black face, remove the interior fixed point and insert all three active points. -/
theorem black_star (hk : 0<k) (X : Finset α) {a b c d : α} (au : a∉X) (bu : b∉X) (cu : c∉X) (du : d∈X)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) (card : (insert b (insert c X)).card=k)
    (ins : StrictInside (P a) (P b) (P c) (P d)) :
    let I := insert b (insert c X);let J := insert c (insert a X);let K := insert a (insert b X)
    ∃ D : Finset α,D.card=k ∧ Exchange I D ∧ Exchange J D ∧ Exchange K D ∧
      StrictInside (average P k I) (average P k J) (average P k K) (average P k D) := by
  let D := insert a (insert b (insert c (X.erase d)))
  have edge (x y z : α) (xu : x∉X) (yu : y∉X) (zu : z∉X) (xy : x≠y) (xz : x≠z)
      (D' : D=insert x (insert y (insert z (X.erase d)))) : Exchange (insert y (insert z X)) D := by
    refine ⟨insert y (insert z (X.erase d)),d,x,by grind,by grind,by grind,?_,D'⟩
    ext;grind
  have abcd := edge a b c au bu cu ab ac rfl
  have bcad := edge b c a bu cu au bc ab.symm (by ext; simp [D];grind)
  have cabd := edge c a b cu au bu ac.symm bc.symm (by ext; simp [D];grind)
  refine ⟨D,abcd.card_eq.symm.trans card,abcd,bcad,cabd,?_⟩
  obtain ⟨e₁,e₂,e₃⟩ := black_points P (k:=k) X au bu cu ab ac bc
  have e₄ : average P k D=mapped (-(k:ℝ)⁻¹) (center P k X a b c) (P d) := by
    have a' : a∉insert b (insert c (X.erase d)) := by grind
    have b' : b∉insert c (X.erase d) := by grind
    have c' : c∉X.erase d := by grind
    simp only [D,average,mapped,center,sum_insert a',sum_insert b',sum_insert c',neg_smul,
      ←X.sum_erase_add P du,smul_add];abel
  rw [e₁,e₂,e₃,e₄]
  exact (inside_mapped _ (neg_ne_zero.mpr (inv_ne_zero (by exact_mod_cast hk.ne'))) _ _ _ _ _).mpr ins

end Hypertriangulations
