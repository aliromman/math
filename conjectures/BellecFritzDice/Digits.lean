module

public import conjectures.BellecFritzDice.Statement
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace BellecFritzDice
open MeasureTheory Finset
noncomputable section

def ratio (m : ℕ) : ℝ := 1/(m+2:ℝ)
def digit (b : Bool) : ℝ := if b then 1 else 0
def code (m : ℕ) (x : ℕ → Bool) : ℝ := ∑' j, (ratio m)^j * digit (x j)

private theorem ratio_pos (m : ℕ) : 0<ratio m := by dsimp [ratio]; positivity
private theorem ratio_lt_one (m : ℕ) : ratio m<1 := by
  dsimp [ratio]; rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α:=ℝ) m]
private theorem digit_nonneg (b : Bool) : 0≤digit b := by cases b <;> norm_num [digit]
private theorem digit_le (b : Bool) : digit b≤1 := by cases b <;> norm_num [digit]

private theorem summable_code (m : ℕ) (x : ℕ → Bool) :
    Summable (fun j ↦ (ratio m)^j*digit (x j)) :=
  .of_nonneg_of_le (fun j ↦ mul_nonneg (pow_nonneg (ratio_pos _).le j) (digit_nonneg (x j)))
    (fun j ↦ mul_le_of_le_one_right (pow_nonneg (ratio_pos _).le j) (digit_le (x j)))
    (summable_geometric_of_lt_one (ratio_pos _).le (ratio_lt_one _))

@[fun_prop] theorem measurable_code (m : ℕ) : Measurable (code m) := by
  apply Measurable.tsum
  intro n
  exact measurable_const.mul ((measurable_of_finite digit).comp (measurable_pi_apply n))

theorem code_nonneg (m : ℕ) (x : ℕ → Bool) : 0 ≤ code m x :=
  tsum_nonneg (fun j ↦ mul_nonneg (pow_nonneg (ratio_pos _).le j) (digit_nonneg (x j)))

theorem code_tail (m : ℕ) (x : ℕ → Bool) :
    ratio m * code m x ≤ 1 / (m+1:ℝ) := by
  have bound := (summable_code m x).tsum_le_tsum
    (fun j ↦ (mul_le_of_le_one_right (pow_nonneg (ratio_pos m).le j) (digit_le (x j))))
    (summable_geometric_of_lt_one (ratio_pos m).le (ratio_lt_one m))
  rw [tsum_geometric_of_lt_one (ratio_pos _).le (ratio_lt_one _)] at bound
  apply (mul_le_mul_of_nonneg_left bound (ratio_pos m).le).trans_eq
  have h₂ : (m:ℝ)+2≠0 := by positivity
  have h₁ : (m:ℝ)+1≠0 := by positivity
  dsimp [ratio]
  rw [show 1-1/((m:ℝ)+2)=((m:ℝ)+1)/((m:ℝ)+2) by field_simp; ring, inv_div]
  field_simp

theorem code_step (m : ℕ) (x : ℕ → Bool) :
    code m x = digit (x 0) + ratio m * code m (fun j => x (j+1)) := by
  rw [code,(summable_code m x).tsum_eq_zero_add]
  simp only [pow_zero,one_mul,code,←tsum_mul_left,pow_succ]
  congr 1
  apply tsum_congr
  intro n
  ring

theorem code_le_two (m : ℕ) (x : ℕ → Bool) : code m x ≤ 2 := by
  rw [code_step]
  have r : 1/(m+1:ℝ)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  linarith [code_tail m (fun j => x (j+1)),digit_le (x 0)]

theorem code_injective (m : ℕ) (hm : 0<m) : Function.Injective (code m) := by
  have hd {x y : ℕ → Bool} (h : code m x=code m y) : x 0=y 0 ∧
      code m (fun j => x (j+1)) = code m (fun j => y (j+1)) := by
    rw [code_step m x,code_step m y] at h
    have t := code_tail m (fun j => x (j+1))
    have u := code_tail m (fun j => y (j+1))
    have l := mul_nonneg (ratio_pos m).le (code_nonneg m (fun j => x (j+1)))
    have r := mul_nonneg (ratio_pos m).le (code_nonneg m (fun j => y (j+1)))
    have b : 1/(m+1:ℝ)<1 := (div_lt_one (by positivity)).mpr (by exact_mod_cast (show 1<m+1 by omega))
    have e : x 0=y 0 := by
      cases hx : x 0 <;> cases hy : y 0 <;> simp [digit,hx,hy] at h ⊢ <;> linarith
    rw [e] at h
    exact ⟨e,(mul_right_inj' (ratio_pos m).ne').mp (add_left_cancel h)⟩
  intro x y h
  ext n
  induction n generalizing x y with
  | zero => exact (hd h).1
  | succ n ih => exact ih (hd h).2

abbrev Column (n : ℕ) := Fin (n+3) → Bool
def uniform {n : ℕ} (b : Column n) : Prop := ∀ i, b i=b 0
def wins {n : ℕ} (s : ℕ → Column n) : Prop :=
  (fun i => code (n+3) (fun k => s k i)) ∈ below (n+3) 0

theorem skip_uniform {n : ℕ} (s : ℕ → Column n) (h : uniform (s 0)) :
    wins s ↔ wins (fun j => s (j+1)) := by
  change (n+3:ℕ)*code _ _ < ∑ i,code _ _ ↔ (n+3:ℕ)*code _ _ < ∑ i,code _ _
  have step (i : Fin (n+3)) := code_step (n+3) (fun j => s j i)
  rw [step 0,Finset.sum_congr rfl (fun i (_ : i∈Finset.univ) => step i),sum_add_distrib,←Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i (_ : i∈Finset.univ) => congrArg digit (h i))]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_add,←mul_assoc]
  rw [add_lt_add_iff_left]
  rw [mul_comm (↑(n+3):ℝ) (ratio (n+3)),mul_assoc]
  exact mul_lt_mul_iff_right₀ (ratio_pos _)

end
end BellecFritzDice

namespace BellecFritzDice
open Finset
noncomputable section

def winColumn {n : ℕ} : Set (Column n) := {b | b 0=false ∧ ¬uniform b}

theorem first_mixed {n : ℕ} (s : ℕ → Column n) (different : ¬uniform (s 0)) :
    wins s ↔ s 0 0=false := by
  let m := n+3
  let x (i : Fin m) := code m (fun j => s j i)
  let b := s 0
  let r := 1/(m+1:ℝ)
  have loss : (m:ℝ)*r<1 := by
    dsimp [r]
    rw [mul_one_div,div_lt_one (by positivity)]
    linarith
  have lo (i : Fin m) : digit (b i) ≤ x i := by
    dsimp only [x,b]
    rw [code_step]
    exact le_add_of_nonneg_right (mul_nonneg (ratio_pos _).le (code_nonneg _ _))
  have hi (i : Fin m) : x i ≤ digit (b i)+r := by
    dsimp only [x,b]; rw [code_step]; exact add_le_add_right (code_tail _ _) _
  have num : ∑ i, digit (b i) = ((univ.filter (fun i => b i=true)).card:ℝ) := by simp [digit]
  have sumLo := sum_le_sum (s:=univ) (fun i (_:i∈univ) => lo i)
  have sumHi := sum_le_sum (s:=univ) (fun i (_:i∈univ) => hi i)
  rw [num] at sumLo
  rw [sum_add_distrib,num,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at sumHi
  change (m:ℝ)*x 0 < ∑ i,x i ↔ b 0=false
  by_cases b₀ : b 0=false
  · have someTrue : ∃i,b i=true := by
      by_contra! h
      exact different (fun i => by change b i=b 0; rw [b₀]; simpa using h i)
    obtain ⟨j,hj⟩ := someTrue
    have c : 0<(univ.filter (fun i => b i=true)).card := card_pos.mpr ⟨j,by simp [hj]⟩
    have c' : (1:ℝ) ≤ (univ.filter (fun i => b i=true)).card := by exact_mod_cast c
    have u : x 0 ≤ r := by simpa only [b₀,digit,Bool.false_eq_true,ite_false,zero_add] using hi 0
    exact iff_of_true (by linarith [mul_le_mul_of_nonneg_left u (Nat.cast_nonneg (α:=ℝ) m)]) b₀
  · have true₀ : b 0=true := by simpa using b₀
    have someFalse : ∃i,b i=false := by
      by_contra! h
      exact different (fun i => by change b i=b 0; rw [true₀]; simpa using h i)
    obtain ⟨j,hj⟩ := someFalse
    have sub : univ.filter (fun i => b i=true) ⊆ univ.erase j := by
      intro i hi
      exact mem_erase.mpr ⟨fun e => by subst i;simpa [hj] using (mem_filter.mp hi).2,mem_univ _⟩
    have c : (univ.filter (fun i => b i=true)).card ≤ m-1 := by simpa [m] using card_le_card sub
    have c' : ((univ.filter (fun i => b i=true)).card:ℝ)+1 ≤ m := by
      exact_mod_cast (show (univ.filter (fun i => b i=true)).card+1≤m by dsimp [m] at *;omega)
    have l : 1≤x 0 := by simpa only [true₀,digit,ite_true] using lo 0
    exact iff_of_false (by linarith [mul_le_mul_of_nonneg_left l (Nat.cast_nonneg (α:=ℝ) m)]) b₀

def firstWin {n : ℕ} (d : ℕ) : Set (ℕ → Column n) :=
  {s | (∀ j<d, uniform (s j)) ∧ s d ∈ winColumn}

theorem wins_set (n : ℕ) : {s : ℕ → Column n | wins s}=⋃ d,firstWin d := by
  classical
  have skip (d : ℕ) (s : ℕ → Column n) (pre : ∀j<d,uniform (s j)) :
      wins s ↔ wins (fun j => s (j+d)) := by
    induction d generalizing s with
    | zero => simp
    | succ d ih =>
      rw [skip_uniform s (pre 0 (by omega))]
      exact ih (fun j => s (j+1)) (fun j hj => pre (j+1) (by omega))
  ext s
  simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  constructor
  · intro win
    have exists' : ∃ i, ¬uniform (s i) := by
      by_contra! h
      have same (i : Fin (n+3)) : (fun j => s j i)=(fun j => s j 0) := funext (fun j => h j i)
      change (n+3:ℕ)*code _ _ < ∑i,code _ _ at win
      rw [Finset.sum_congr rfl (fun i (_ : i∈univ) => congrArg (code (n+3)) (same i))] at win
      simp at win
    let d := Nat.find exists'
    have pre : ∀j<d,uniform (s j) := fun j hj => by simpa using Nat.find_min exists' hj
    have dif : ¬uniform (s d) := Nat.find_spec exists'
    have h := (first_mixed (fun j => s (j+d)) (by simpa using dif)).mp ((skip d s pre).mp win)
    exact ⟨d,pre,by simpa using h,dif⟩
  · rintro ⟨d,pre,winning,dif⟩
    exact (skip d s pre).mpr ((first_mixed _ (by simpa using dif)).mpr (by simpa using winning))

theorem firstWin_disjoint (n : ℕ) : Pairwise (fun a b => Disjoint (firstWin (n:=n) a) (firstWin b)) := by
  intro a b h
  apply Set.disjoint_left.mpr
  intro s h₁ h₂
  rcases lt_or_gt_of_ne h with h|h
  · exact h₁.2.2 (h₂.1 a h)
  · exact h₂.2.2 (h₁.1 b h)

end
end BellecFritzDice
