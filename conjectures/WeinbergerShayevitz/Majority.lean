module

public import conjectures.WeinbergerShayevitz.Cube
public import conjectures.WeinbergerShayevitz.Gini
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace WeinbergerShayevitz
open Finset
open scoped BigOperators

def vote (b : Bool) : ℤ := if b then 1 else -1
def bit (b : Bool) : ℤ := if b then 1 else 0

/-- Count observed ones minus observed zeros. A tie sends true. -/
def majority : (n : ℕ) → ℤ → Observation n → Bool
  | 0,o,_ => decide (0 ≤ o)
  | n+1,o,y => match y 0 with
    | none => majority n o (Fin.tail y)
    | some b => majority n (o + vote b) (Fin.tail y)

def weight : (n : ℕ) → Word n → ℤ
  | 0,_ => 0
  | n+1,x => bit (x 0) + weight n (Fin.tail x)

private def dir (d : ℤ) : ℤ := if 0 < d then 1 else if d < 0 then -1 else 0

private theorem cmp_int (a b : ℤ) :
    cmp (a:ℝ) (b:ℝ) = (dir (a-b):ℝ) := by
  unfold cmp dir
  push_cast
  split_ifs <;> norm_num at * <;> omega

private noncomputable def joint (n : ℕ) (d o : ℤ) (x y : Word n) : ℝ :=
  channel (3/4) n (signBit ∘ majority n o) x *
    ((dir (d+weight n x-weight n y) : ℤ):ℝ)

private noncomputable def score (n : ℕ) (d o : ℤ) : ℝ :=
  𝔼 x, 𝔼 y, joint n d o x y

private theorem score_zero (d o : ℤ) : score 0 d o =
    ((if 0 ≤ o then (1:ℤ) else -1) * dir d:ℤ) := by
  simp [score,joint,channel,majority,weight,signBit]

private theorem joint_step (n : ℕ) (d o : ℤ) (b c : Bool) (x y : Word n) :
    joint (n+1) d o (Fin.cons b x) (Fin.cons c y) =
      (1/4)*joint n (d+bit b-bit c) (o+vote b) x y +
      (3/4)*joint n (d+bit b-bit c) o x y := by
  have h : d+(bit b+weight n x)-(bit c+weight n y) =
      d+bit b-bit c+weight n x-weight n y := by ring
  simp only [joint,channel,Function.comp_def,majority,weight,Fin.cons_zero,Fin.tail_cons,h]
  ring

private theorem score_step (n : ℕ) (d o : ℤ) :
    16*score (n+1) d o =
      score n d (o-1) + 6*score n d o + score n (d-1) (o-1) +
      3*score n (d-1) o + score n (d+1) (o+1) +
      3*score n (d+1) o + score n d (o+1) := by
  unfold score
  rw [expect_succ]
  simp only [expect_succ,joint_step,div_eq_mul_inv,expect_add_distrib,←expect_mul,←mul_expect,
    bit,vote,Bool.false_eq_true,↓reduceIte,add_zero,neg_zero,add_neg_cancel_right,sub_eq_add_neg]
  ring

/-- Store the 25 possible offsets on either axis during the finite calculation. -/
private def cached {α : Type} (f : ℤ → α) (i : ℤ) : α :=
  let v := Array.ofFn (fun j : Fin 25 ↦ f ((j:ℕ)-12 : ℤ))
  if h : (i+12).toNat < 25 ∧ (-12 : ℤ) ≤ i then
    v[(i+12).toNat]'(by simpa [v] using h.1)
  else f i

private theorem cached_apply {α : Type} (f : ℤ → α) (i : ℤ) : cached f i = f i := by
  dsimp only [cached]
  split
  · simp only [Array.getElem_ofFn]
    congr 1; omega
  · rfl

private def count : ℕ → ℤ → ℤ → ℤ
  | 0,d,o => (if 0 ≤ o then 1 else -1) * dir d
  | n+1,d,o => cached (fun i ↦ cached (fun j ↦
      count n i (j-1) + 6*count n i j + count n (i-1) (j-1) +
      3*count n (i-1) j + count n (i+1) (j+1) + 3*count n (i+1) j + count n i (j+1))) d o

private theorem count_score (n : ℕ) (d o : ℤ) : (count n d o : ℝ)=16^n * score n d o := by
  induction n generalizing d o with
  | zero => simpa [count] using (score_zero d o).symm
  | succ n ih =>
    simp only [count,cached_apply,Int.cast_add,Int.cast_mul,Int.cast_ofNat,ih,pow_succ]
    rw [mul_assoc,score_step]
    ring

set_option maxHeartbeats 1200000 in
theorem majority_alignment :
    alignment (channel (3/4) 12 (signBit ∘ majority 12 0)) (fun x ↦ (weight 12 x:ℝ)) =
    3845275777343/17592186044416 := by
  have h : count 12 0 0 = 61524412437488 := by decide +kernel
  have hs := count_score 12 0 0
  rw [h] at hs
  calc
    _ = score 12 0 0 := by simp [alignment,score,joint,mul_expect,cmp_int]
    _ = _ := by norm_num at hs ⊢; linarith

end WeinbergerShayevitz
