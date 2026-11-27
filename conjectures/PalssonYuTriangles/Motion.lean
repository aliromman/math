module

public import conjectures.PalssonYuTriangles.Plane
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section
open Complex Finset Fin.NatCast
open scoped ComplexConjugate
namespace PalssonYu
noncomputable section

/-- A distance-preserving match of finite planar point sets has a common orientation. -/
private theorem match_motion {p q : Fin 7 → ℂ} (p01 : p 0 ≠ p 1) (q01 : q 0 ≠ q 1)
    (iso : ∀ i j, D (q i) (q j)=D (p i) (p j)) :
    (∃ a b : ℂ, ∀ i, q i=b+a*p i) ∨
    (∃ a b : ℂ, normSq a=1 ∧ ∀ i, q i=b+a*conj (p i)) := by
  let U i := coord (p 0) (p 1) (p i)
  let V i := coord (q 0) (q 1) (q i)
  have edge (i j) : D (V i) (V j) = D (U i) (U j) := by
    simp only [V,U,scaled,iso]
  have norm (i) : normSq (V i) = normSq (U i) := by
    simp only [V,U,(coords q01 _).1,(coords p01 _).1,iso]
  have both (i) : (V i).re=(U i).re ∧
      ((V i).im=(U i).im ∨ (V i).im= -(U i).im) := by
    apply same_coords (norm i)
    simp only [V,U,(coords q01 _).2,(coords p01 _).2,iso]
  by_cases direct : ∀ i, V i=U i
  · let a := (q 1-q 0)/(p 1-p 0)
    refine Or.inl ⟨a,q 0-a*p 0,fun i => ?_⟩
    have h := (div_eq_div_iff (sub_ne_zero.mpr q01.symm) (sub_ne_zero.mpr p01.symm)).mp (direct i)
    dsimp [a]
    field_simp
    linear_combination h
  · push Not at direct
    obtain ⟨j,hj⟩ := direct
    obtain ⟨rj,sj|sj⟩ := both j
    · exact (hj (ext rj sj)).elim
    have n : (U j).im≠0 := by intro z; exact hj (ext rj (by rw [sj,z,neg_zero]))
    have reverse (i) : V i=conj (U i) := by
      obtain ⟨ri,si|si⟩ := both i
      · have e := edge i j
        simp only [D,normSq_apply,sub_re,sub_im,ri,rj,si,sj] at e
        have pr : (U i).im*(U j).im=0 := by nlinarith only [e]
        have zi := (mul_eq_zero.mp pr).resolve_right n
        exact ext ri (by simp [si,zi])
      · exact ext ri si
    let a := (q 1-q 0)/conj (p 1-p 0)
    refine Or.inr ⟨a,q 0-a*conj (p 0),?_,fun i => ?_⟩
    · simp only [a,normSq_div,normSq_conj]
      change D (q 1) (q 0)/D (p 1) (p 0)=1
      rw [iso,div_self (D_pos p01.symm).ne']
    · have e := reverse i
      change (q i-q 0)/(q 1-q 0)=conj ((p i-p 0)/(p 1-p 0)) at e
      rw [map_div₀] at e
      have nz : conj (p 1-p 0)≠0 := by
        intro e
        exact sub_ne_zero.mpr p01.symm (by simpa only [conj_conj,map_zero] using congrArg conj e)
      have h := (div_eq_div_iff (sub_ne_zero.mpr q01.symm) nz).mp e
      dsimp [a]
      field_simp
      simp only [map_sub] at h ⊢
      linear_combination h

private theorem zero_translation (p : Fin 7 → ℂ) (s : Fin 7) (b : ℂ)
    (h : ∀ i, p (i+s)=p i+b) : b=0 := by
  have it (j : ℕ) : p ((j:Fin 7)*s)=p 0+j*b := by
    induction j with
    | zero => simp
    | succ j ih => push_cast; rw [add_mul,one_mul,h,ih]; ring
  have e := it 7
  norm_num at e
  rw [show (7:Fin 7)=0 by decide,zero_mul] at e
  linear_combination -e / 7

/-- An order-seven shift preserving all distances must be a rotation about a point. -/
theorem heptagon_of_shift {p : Fin 7 → ℂ} (inj : Function.Injective p)
    (hd : ∀ i j, D (p (i+1)) (p (j+1))=D (p i) (p j)) :
    RegularHeptagon (Finset.univ.image p) := by
  have p01 : p 0 ≠ p 1 := fun e => (by decide : (0:Fin 7)≠1) (inj e)
  have p12 : p (0+1) ≠ p (1+1) := fun e => (by decide : (0+1:Fin 7)≠1+1) (inj e)
  rcases match_motion (q:=fun i => p (i+1)) p01 p12 hd with ⟨r,b,h⟩|⟨r,b,n,h⟩
  · have rn : r≠1 := by
      rintro rfl
      simp only [one_mul] at h
      have z := zero_translation p 1 b (fun i => (h i).trans (add_comm ..))
      exact p01 (by simpa [z] using (h 0).symm)
    let c := b/(1-r)
    have fix : b+r*c=c := by dsimp [c]; field_simp [sub_ne_zero.mpr rn.symm]; ring
    let z := p 0-c
    have it (j : ℕ) : p (j : Fin 7)=c+z*r^j := by
      induction j with
      | zero => simp [z]
      | succ j ih =>
        push_cast
        rw [h,ih,pow_succ]
        linear_combination fix
    have zn : z≠0 := by
      intro hz
      exact p01 (by simpa [hz] using (it 0).trans (by simpa [hz] using (it 1).symm))
    have e := (show p 0=p (7:Fin 7) by rfl).trans (it 7)
    have prod : z*(r^7-1)=0 := by linear_combination (it 0) - e
    have pow := sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left zn)
    refine ⟨c,z,r,zn,isPrimitiveRoot_of_mem_nthRootsFinset (by decide : Nat.Prime 7)
      ((Polynomial.mem_nthRootsFinset (by decide : 0<7) 1).mpr pow) rn,?_⟩
    apply Finset.image_congr
    intro i _
    simpa only [Fin.cast_val_eq_self] using it i.val
  · have rr : r*conj r=1 := by rw [mul_conj,n]; norm_num
    have tr (i) : p (i+2)=p i+(b+r*conj b) := by
      rw [show i+(2:Fin 7)=(i+1)+1 by simp [add_assoc]]
      rw [h,h,map_add,map_mul, conj_conj]
      linear_combination (congrArg (· * p i) rr)
    have bz := zero_translation p 2 _ tr
    have e := tr 0
    rw [bz,add_zero] at e
    exact ((by decide : (0+2:Fin 7)≠0) (inj e)).elim

end
end PalssonYu
