module

public import conjectures.Hypertriangulations.Labels
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

@[expose] public section
namespace Hypertriangulations
open Finset
variable {α : Type*} [DecidableEq α] {I J K : Finset α} {k : ℕ} {w : α→ℝ}

/-- The labels on a supporting line maximize the same sum of projected coordinates. -/
def MaxScore {α : Type*} (w : α→ℝ) (k : ℕ) (I : Finset α) : Prop :=
  I.card=k ∧ ∀ J : Finset α,J.card=k → ∑ i ∈ J,w i≤∑ i ∈ I,w i

private theorem MaxScore.compare (hs : MaxScore w k I) {x y : α} (hx : x∈I) (hy : y∉I) : w y≤w x := by
  have ye : y∉I.erase x := by grind
  have card : (insert y (I.erase x)).card=k := by rw [card_insert_of_notMem ye,card_erase_add_one hx,hs.1]
  have better := hs.2 _ card
  rw [sum_insert ye,←I.add_sum_erase w hx] at better
  linarith only [better]

private theorem MaxScore.tie (hi : MaxScore w k I) (hj : MaxScore w k J) {x y : α}
    (xi : x∈I) (xj : x∉J) (yj : y∈J) (yi : y∉I) : w x=w y :=
  le_antisymm (hj.compare yj xj) (hi.compare xi yi)

omit [DecidableEq α] in
private theorem different (hi : MaxScore w k I) (hj : MaxScore w k J) (ne : I≠J) : ∃ x∈I,x∉J :=
  not_subset.mp fun sub ↦ ne (eq_of_subset_of_card_le sub (hj.1.trans hi.1.symm).le)

def projection (u v : ℝ) (p : Plane) : ℝ := u*p.1+v*p.2

/-- At most two input points have the same value under a nonzero linear functional. -/
theorem projection_fiber {P : α→Plane} (gp : GeneralPosition P) {u v : ℝ} (lin : u≠0 ∨ v≠0)
    {x y z : α} (xy : projection u v (P x)=projection u v (P y)) (xz : projection u v (P x)=projection u v (P z)) :
    x=y ∨ x=z ∨ y=z := by
  by_contra! distinct
  have det := gp x y z distinct.1 distinct.2.1 distinct.2.2
  unfold projection at xy xz
  rcases lin with hu|hv
  · apply det
    apply (mul_eq_zero.mp ?_).resolve_left hu
    unfold orient
    linear_combination -((P z).2-(P x).2)*xy+((P y).2-(P x).2)*xz
  · apply det
    apply (mul_eq_zero.mp ?_).resolve_left hv
    unfold orient
    linear_combination ((P z).1-(P x).1)*xy-((P y).1-(P x).1)*xz

/-- Every other maximizing label is obtained by the same single exchange. -/
private theorem two_options (fiber : ∀ {x y z : α},w x=w y → w x=w z → x=y ∨ x=z ∨ y=z)
    (hi : MaxScore w k I) (hj : MaxScore w k J) (ne : I≠J) :
    ∃ U a b, a∉U ∧ b∉U ∧ a≠b ∧ I=insert a U ∧ J=insert b U ∧
      ∀ K : Finset α,MaxScore w k K → K=I ∨ K=J := by
  obtain ⟨a,ai,aj⟩ := different hi hj ne
  obtain ⟨b,bj,bi⟩ := different hj hi ne.symm
  have tie := hi.tie hj ai aj bj bi
  have ab : a≠b := by grind
  have every (K : Finset α) (hk : MaxScore w k K) (ik : I≠K) : K=insert b (I.erase a) := by
    obtain ⟨x,xi,xk⟩ := different hi hk ik
    obtain ⟨y,yk,yi⟩ := different hk hi ik.symm
    have link := hi.tie hk xi xk yk yi
    have trans : w a=w x := by
      apply le_antisymm
      · rw [tie];exact hi.compare xi bi
      · rw [link];exact hi.compare ai yi
    have xa : x=a := by have := fiber tie trans;grind
    have yb : y=b := by have := fiber tie (trans.trans link);grind
    subst x;subst y
    ext z
    by_cases za : z=a <;> by_cases zb : z=b <;> try grind
    by_cases zi : z∈I <;> by_cases zk : z∈K <;> try grind
    · have := fiber tie (hi.tie hk zi zk yk yi |>.trans tie.symm |>.symm)
      grind
    · have := fiber tie (hi.tie hk xi xk zk zi)
      grind
  refine ⟨I.erase a,a,b,by simp,by grind,ab,(insert_erase ai).symm,every J hj ne,?_⟩
  intro K hk
  rcases eq_or_ne I K with e|e
  · exact Or.inl e.symm
  · exact Or.inr ((every K hk e).trans (every J hj ne).symm)

theorem support_labels {P : α→Plane} (gp : GeneralPosition P) {u v : ℝ} (lin : u≠0 ∨ v≠0)
    (hi : MaxScore (projection u v ∘ P) k I) (hj : MaxScore (projection u v ∘ P) k J)
    (hk : MaxScore (projection u v ∘ P) k K) : I=J ∨ I=K ∨ J=K := by
  rcases eq_or_ne I J with e|e
  · exact Or.inl e
  obtain ⟨_,_,_,_,_,_,_,_,both⟩ := two_options (fun h h' ↦ projection_fiber gp lin h h') hi hj e
  exact Or.inr ((both K hk).imp Eq.symm Eq.symm)

theorem support_exchange {P : α→Plane} (gp : GeneralPosition P) {u v : ℝ} (lin : u≠0 ∨ v≠0)
    (hi : MaxScore (projection u v ∘ P) k I) (hj : MaxScore (projection u v ∘ P) k J) (ij : I≠J) : Exchange I J := by
  obtain ⟨U,a,b,au,bu,ab,i,j,_⟩ := two_options (fun h h' ↦ projection_fiber gp lin h h') hi hj ij
  exact ⟨U,a,b,au,bu,ab,i,j⟩

/-- A location on a supporting line has a unique maximizing label. -/
theorem support_unique_at_point {P : α→Plane} (gp : GeneralPosition P) (inj : Function.Injective P)
    {u v : ℝ} (lin : u≠0 ∨ v≠0) (hk : 0<k) (hi : MaxScore (projection u v ∘ P) k I)
    (hj : MaxScore (projection u v ∘ P) k J) (atPoint : average P k I=average P k J) : I=J := by
  by_contra ij
  obtain ⟨U,a,b,au,bu,ab,rfl,rfl⟩ := support_exchange gp lin hi hj ij
  have scaled := congrArg (fun p : Plane ↦ (k:ℝ) • p) atPoint
  have nz : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  simp only [average,smul_smul,mul_inv_cancel₀ nz,one_smul,sum_insert au,sum_insert bu] at scaled
  exact ab (inj (add_right_cancel scaled))

omit [DecidableEq α] in
/-- Maximizing a supporting functional on averages is equivalent to maximizing its unscaled sum. -/
theorem maxScore_iff_average (P : α→Plane) (hk : 0<k) (u v : ℝ) :
    MaxScore (projection u v ∘ P) k I ↔ I.card=k ∧ ∀ J : Finset α,J.card=k →
      projection u v (average P k J)≤projection u v (average P k I) := by
  have value (J : Finset α) : projection u v (average P k J)=(k:ℝ)⁻¹*∑i∈J,(projection u v ∘ P) i := by
    simp only [projection,average,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Prod.fst_sum,Prod.snd_sum,
      Function.comp_apply,sum_add_distrib,←mul_sum];ring
  have pos : 0<(k:ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hk)
  simp only [MaxScore,value,mul_le_mul_iff_right₀ pos]

end Hypertriangulations
