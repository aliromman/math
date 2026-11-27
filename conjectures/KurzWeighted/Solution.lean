module

public import conjectures.KurzWeighted.Averaging
public import conjectures.KurzWeighted.Dichotomy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section
namespace KurzWeighted
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem weighted_mono {w : V→ℝ} (hw : ∀ i,0≤w i) (q : ℝ) : Monotone (weighted w q) := by
  intro S T sub
  have h : (∑ i ∈ S,w i) ≤ ∑ i ∈ T,w i := sum_le_sum_of_subset_of_nonneg sub (fun i _ _ ↦ hw i)
  unfold weighted
  split <;> split <;> norm_num
  linarith

private theorem raw_bound (d i : V) (ne : i≠d) (f : Rule V) (mon : Monotone f)
    (binary : ∀ S, f S=0 ∨ f S=1) (comp : Complete f) (A : ℝ) :
    A ≤ 9*(|swings f d-A| + deviation f d (2*A)) := by
  let g := rounded d f
  let D := deviation f d (2*A)
  have dist : distance f g ≤ 4*D := rounding_bound d f binary comp (2*A)
  have errd := abs_le.mp (swing_lipschitz f g d)
  have erri := abs_le.mp (swing_lipschitz f g i)
  have d' := le_abs_self (A-swings f d)
  rw [abs_sub_comm A] at d'
  have d'' := le_abs_self (swings f d-A)
  have i' := le_abs_self (2*A-swings f i)
  rw [abs_sub_comm (2*A)] at i'
  have cost : |swings f i-2*A|≤D := single_le_sum (fun j _ ↦ abs_nonneg (swings f j-2*A))
    (mem_erase.mpr ⟨ne,mem_univ i⟩)
  have posD : 0≤D := sum_nonneg fun _ _ ↦ abs_nonneg _
  have posd : 0≤|swings f d-A| := abs_nonneg _
  change A≤9*(|swings f d-A|+D)
  rcases symmetric_dichotomy d g (rounded_mono d mon) (rounded_binary d f)
    (rounded_symmetric d f) with h|h
  · linarith
  · have := h i
    linarith

theorem complete_lower_bound {n : ℕ} (hn : 2≤n) (f : Rule (Fin n)) (mon : Monotone f)
    (binary : ∀ S, f S=0 ∨ f S=1) (comp : Complete f) :
    (1/18:ℝ)/n ≤ ∑ i : Fin n,
      |banzhaf f i - (if i.val+1=n then 1 else 2) / (2*(n:ℝ)-1)| := by
  let d : Fin n := ⟨n-1,by omega⟩
  let i : Fin n := ⟨0,by omega⟩
  let T := ∑ j,swings f j
  let m : ℝ := 2*(n:ℝ)-1
  let a : Fin n→ℝ := fun j ↦ if j=d then 1 else 2
  let E := ∑ j, |banzhaf f j-a j/m|
  have den : 0<m := by dsimp [m]; exact_mod_cast (show 0 < (2*(n:ℤ)-1) by omega)
  have npos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have cond (j : Fin n) : j.val+1=n ↔ j=d := by
    change j.val+1=n ↔ j=⟨n-1,_⟩
    rw [Fin.ext_iff]
    have := j.isLt
    dsimp
    omega
  simp_rw [cond]
  change (1/18:ℝ)/n ≤ E
  have amount : 0≤T := sum_nonneg fun j _ ↦ sum_nonneg fun S _ ↦ by
    by_cases h : j∈S
    · simp [h]
    · simp [h]
      exact mon (subset_insert j S)
  have epos : 0≤E := sum_nonneg fun _ _ ↦ abs_nonneg _
  have neq : i≠d := by intro h; have := congrArg Fin.val h; dsimp [i,d] at this; omega
  have nreal : (2:ℝ)≤n := by exact_mod_cast hn
  apply (div_le_iff₀ npos).mpr
  rcases amount.eq_or_lt with zero|tpos
  · have one : 1/m≤E := by
      calc
        _ = |banzhaf f d-a d/m| := by simp [banzhaf,show (∑ j,swings f j)=0 from zero.symm,a,abs_of_pos den]
        _ ≤ _ := single_le_sum (fun j _ ↦ abs_nonneg (banzhaf f j-a j/m)) (mem_univ d)
    have h := (div_le_iff₀ den).mp one
    dsimp [m] at h
    nlinarith
  · let A := T/m
    have hb := raw_bound d i neq f mon binary comp A
    change A ≤ 9*(|swings f d-A|+deviation f d (2*A)) at hb
    have scale (j : Fin n) : T*|banzhaf f j-a j/m|=|swings f j-(if j=d then A else 2*A)| := by
      rw [←abs_of_pos tpos,←abs_mul]
      congr 1
      change T*(swings f j/T-(if j=d then 1 else 2)/m)=_
      by_cases h:j=d <;> simp [h,A] <;> field_simp
    have identity : T*E=|swings f d-A|+deviation f d (2*A) := by
      change T*(∑ j,|banzhaf f j-a j/m|)=_
      rw [mul_sum]
      simp_rw [scale]
      rw [←add_sum_erase univ _ (mem_univ d)]
      simp only [↓reduceIte]
      congr 1
      apply sum_congr rfl
      intro j hj
      simp [(mem_erase.mp hj).1]
    rw [←identity] at hb
    have hm : 1≤9*(E*m) := by
      have a := (div_le_iff₀ den).mp hb
      apply le_of_mul_le_mul_left _ tpos
      nlinarith only [a]
    dsimp [m] at hm
    nlinarith

theorem resolution : Conjecture := by
  refine ⟨1/18,by norm_num,?_⟩
  intro n hn w q hw _ _
  apply complete_lower_bound hn _ (weighted_mono hw q) _ (weighted_complete w q)
  intro S
  unfold weighted
  split <;> simp

/-- info: 'KurzWeighted.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end KurzWeighted
