module

public import conjectures.Hypertriangulations.EdgePotential
public import conjectures.Hypertriangulations.LabelGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section
namespace Hypertriangulations
open Finset
variable {α : Type*} [DecidableEq α]

/-- Sum over the exchanged labels. For adjacent labels there is exactly one summand. -/
def directed (f : EdgeWeight α) (I J : Finset α) : ℤ :=
  ∑ a ∈ I\J,∑ b ∈ J\I,f (I∩J) a b

def faceValue (g : Finset α→Finset α→ℤ) (I J K : Finset α) : ℤ := g I J+g J K+g K I

theorem directed_antisymmetric (f : EdgeWeight α) (h : ∀ U a b, f U b a= -f U a b) (I J : Finset α) :
    directed f J I= -directed f I J := by
  unfold directed
  rw [inter_comm J I,sum_comm]
  simp only [←sum_neg_distrib]
  exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ h _ a b

private theorem directed_insert (f : EdgeWeight α) (U : Finset α) {a b : α} (au : a∉U) (bu : b∉U) (ab : a≠b) :
    directed f (insert a U) (insert b U)=f U a b := by
  have inter : insert a U∩insert b U=U := by ext;grind
  have drop : insert a U\insert b U={a} := by ext;grind
  have gain : insert b U\insert a U={b} := by ext;grind
  simp [directed,inter,drop,gain]

private theorem directed_black (f : EdgeWeight α) (X : Finset α) {a b c : α} (au : a∉X) (bu : b∉X)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    directed f (insert b (insert c X)) (insert c (insert a X))=f (insert c X) b a := by
  rw [insert_comm c a]
  exact directed_insert f _ (by grind) (by grind) ab.symm

variable (P : α→Plane)

omit [DecidableEq α] in
private theorem positive_score (S : Finset α) {a b c : α} (pos : sign (P a) (P b) (P c)=1) :
    1≤score P S a b c ∧ (1<score P S a b c → ∃ d∈S,StrictInside (P a) (P b) (P c) (P d)) := by
  rw [score_count,pos,one_mul]
  constructor
  · omega
  · intro lt
    have n : 0<(S.filter fun x ↦ StrictInside (P a) (P b) (P c) (P x)).card := by exact_mod_cast (by omega :
      0<((S.filter fun x ↦ StrictInside (P a) (P b) (P c) (P x)).card : ℤ))
    obtain ⟨x,hx⟩ := card_pos.mp n
    exact ⟨x,(mem_filter.mp hx).1,(mem_filter.mp hx).2⟩

/-- A single antisymmetric boundary weight applies to every labelled face at every level. -/
theorem mesh_weights [Fintype α] (gp : GeneralPosition P) : ∃ g : Finset α→Finset α→ℤ,
    (∀ I J, g J I= -g I J) ∧ ∀ {k : ℕ} (_hk : 0<k) (I J K : Finset α), I.card=k →
    Exchange I J → Exchange J K → Exchange K I →
    0<orient (average P k I) (average P k J) (average P k K) →
    1≤faceValue g I J K ∧ (1<faceValue g I J K → ∃ D : Finset α, D.card=k ∧ Exchange I D ∧ Exchange J D ∧ Exchange K D ∧
      StrictInside (average P k I) (average P k J) (average P k K) (average P k D)) := by
  obtain ⟨f,anti,whiteEq,blackEq⟩ := edge_potential P gp
  refine ⟨directed f,directed_antisymmetric f anti,?_⟩
  intro k hk I J K size ij jk ki ccw
  have positive : sign (average P k I) (average P k J) (average P k K)=1 := by simp [sign,pos,unit,ccw,ccw.ne']
  rcases classify_triangle ij jk ki with whiteCase|blackCase
  · obtain ⟨U,a,b,c,au,bu,cu,ab,ac,bc,rfl,rfl,rfl⟩ := whiteCase
    rw [white_sign P hk U au bu cu] at positive
    have val : faceValue (directed f) (insert a U) (insert b U) (insert c U)=white P U a b c := by
      simpa only [faceValue,whiteBoundary,directed_insert f U au bu ab,directed_insert f U bu cu bc,
        directed_insert f U cu au ac.symm] using whiteEq U a b c au bu cu
    rw [val]
    obtain ⟨low,step⟩ := positive_score P (univ\U) positive
    refine ⟨low,fun large ↦ ?_⟩
    obtain ⟨d,du,ins⟩ := step large
    exact white_star P hk U au bu cu (mem_sdiff.mp du).2 size ins
  · obtain ⟨X,a,b,c,au,bu,cu,ab,ac,bc,rfl,rfl,rfl⟩ := blackCase
    rw [black_sign P hk X au bu cu ab ac bc] at positive
    have val : faceValue (directed f) (insert b (insert c X)) (insert c (insert a X)) (insert a (insert b X))=
        black P X a b c := by
      simpa only [faceValue,blackBoundary,directed_black f X au bu ab ac bc,
        directed_black f X bu cu bc ab.symm ac.symm,directed_black f X cu au ac.symm bc.symm ab] using blackEq X a b c au bu cu
    rw [val]
    obtain ⟨low,step⟩ := positive_score P X positive
    refine ⟨low,fun large ↦ ?_⟩
    obtain ⟨d,dx,ins⟩ := step large
    exact black_star P hk X au bu cu dx ab ac bc size ins

end Hypertriangulations
