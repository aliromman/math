module

public import conjectures.BrownMolFixed.Probability
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace BrownMolFixed
open Finset

/-- At scale s, each vertex operates with probability B to the power -s. -/
def scaleProb (B s : ℕ) : ℝ := 1/(B:ℝ)^s

theorem scale_pos {B : ℕ} (hB : 0<B) (s : ℕ) : 0<scaleProb B s := by unfold scaleProb; positivity

theorem scale_le_one {B : ℕ} (hB : 1≤B) (s : ℕ) : scaleProb B s≤1 := by
  unfold scaleProb
  have b : (1:ℝ)≤B := by exact_mod_cast hB
  exact (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (one_le_pow₀ b)).trans_eq (by norm_num)

theorem scale_anti {B : ℕ} (hB : 1≤B) : Antitone (scaleProb B) := by
  intro i j hij
  exact one_div_le_one_div_of_le (pow_pos (by exact_mod_cast (show 0<B by omega)) _) (pow_le_pow_right₀ (by exact_mod_cast hB) hij)

theorem scale_strict {B : ℕ} (hB : 1<B) : StrictAnti (scaleProb B) := by
  intro i j hij
  exact one_div_lt_one_div_of_lt (pow_pos (by exact_mod_cast (show 0<B by omega)) _)
    (pow_lt_pow_right₀ (by exact_mod_cast hB) hij)

private theorem scale_add (B i j : ℕ) : scaleProb B (i+j)=scaleProb B i*scaleProb B j := by
  simp [scaleProb,pow_add,mul_comm]

private theorem tiny_empty {p : ℝ} (_hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    (1-p)^m*(1+(m:ℝ)*p)≤1 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ,mul_assoc]
    have a : (1-p)*(1+((n:ℝ)+1)*p)≤1+(n:ℝ)*p := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ)≤(n:ℝ)+1) (sq_nonneg p)]
    exact (mul_le_mul_of_nonneg_left a (pow_nonneg (by linarith) _)).trans ih

private theorem tiny_active {p : ℝ} (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    1-(1-p)^m≤(m:ℝ)*p := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    have ho : (1-p)^n≤1 := pow_le_one₀ (by linarith) (by linarith)
    nlinarith only [ih,mul_nonneg hp (sub_nonneg.mpr ho)]

theorem empty_large {B s e r : ℕ} (hB : 1≤B) (h : s+r≤e) :
    (1-scaleProb B s)^(B^e) ≤ scaleProb B r := by
  have bpos : (0:ℝ)<B := by exact_mod_cast (by omega : 0<B)
  have ppos := scale_pos (by omega : 0<B) s
  have pone := scale_le_one hB s
  have lo : (B:ℝ)^r ≤ ((B^e:ℕ):ℝ)*scaleProb B s := by
    simp only [scaleProb,Nat.cast_pow,mul_one_div,le_div_iff₀ (pow_pos bpos s),←pow_add]
    exact pow_le_pow_right₀ (by exact_mod_cast hB) (by omega)
  have fpos : 0≤(1-scaleProb B s)^(B^e) := pow_nonneg (sub_nonneg.mpr pone) _
  have b := tiny_empty ppos.le pone (B^e)
  apply (le_div_iff₀ (pow_pos bpos r)).mpr
  exact (mul_le_mul_of_nonneg_left (lo.trans (by linarith)) fpos).trans b

theorem active_small {B s e r : ℕ} (hB : 1≤B) (h : e+r≤s) :
    1-(1-scaleProb B s)^(B^e) ≤ scaleProb B r := by
  have bpos : (0:ℝ)<B := by exact_mod_cast (by omega : 0<B)
  apply (tiny_active (scale_pos (by omega : 0<B) s).le (scale_le_one hB s) (B^e)).trans
  simp only [Nat.cast_pow,scaleProb,mul_one_div,div_le_div_iff₀ (pow_pos bpos s) (pow_pos bpos r),one_mul,←pow_add]
  exact pow_le_pow_right₀ (by exact_mod_cast hB) h

private def value (B s : ℕ) {n : ℕ} (e : Fin n→ℕ) (b : Fin n→Bool) (i : Fin n) : ℝ :=
  if b i then 1-(1-scaleProb B s)^(B^(e i)) else (1-scaleProb B s)^(B^(e i))

private theorem value_range {n B : ℕ} (hB : 1≤B) (s : ℕ) (e : Fin n→ℕ) (b : Fin n→Bool) (i : Fin n) :
    0≤value B s e b i ∧ value B s e b i≤1 := by
  have hb := scale_le_one hB s
  have hp := (scale_pos (by omega : 0<B) s).le
  have q0 : 0≤(1-scaleProb B s)^(B^(e i)) := pow_nonneg (by linarith) _
  have q1 : (1-scaleProb B s)^(B^(e i))≤1 := pow_le_one₀ (by linarith) (by linarith)
  unfold value
  split <;> constructor <;> linarith

/-- A likely occupied prefix gives a point above the diagonal. -/
theorem scale_above {n B s : ℕ} (hB : 2≤B) (size : 2^n<B) (hs : 1≤s)
    (e : Fin n→ℕ) (z : Fin n) (large : ∀ i, i≤z → s+1≤e i)
    (small : ∀ i, z< i → e i+1≤s) :
    scaleProb B s < layerValue (fun i => B^(e i)) (scaleProb B s) := by
  let b := fun i : Fin n => decide (i≤z)
  have iv : IntervalSupport b := by
    refine ⟨⟨z,by simp [b]⟩,?_⟩
    intro i j k _ hj _ hkj
    exact decide_eq_true (hkj.trans (of_decide_eq_true hj))
  have half : scaleProb B 1≤1/2 := by
    simpa [scaleProb] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤B by exact_mod_cast hB)
  have v (i : Fin n) : (1/2:ℝ)≤value B s e b i := by
    by_cases h : i≤z
    · have lo := empty_large (by omega : 1≤B) (large i h)
      simp [value,b,h]
      linarith
    · have hi := active_small (by omega : 1≤B) (small i (lt_of_not_ge h))
      simp [value,b,h]
      linarith
  have lower := prod_le_prod₀ (s:=univ) (fun (_i : Fin n) _ => show (0:ℝ)≤1/2 by norm_num) (fun i _ => v i)
  have incr : scaleProb B s<(1/2:ℝ)^n := by
    apply (scale_anti (by omega : 1≤B) hs).trans_lt
    simpa [scaleProb,one_div_pow] using one_div_lt_one_div_of_lt
      (show (0:ℝ)<(2:ℝ)^n by positivity) (show (2:ℝ)^n<B by exact_mod_cast size)
  have term := single_le_sum (s:=univ) (f:=fun b : Fin n→Bool => (if IntervalSupport b then (1:ℝ) else 0)*∏i,value B s e b i)
    (fun b _ => mul_nonneg (by split <;> norm_num) (prod_nonneg fun i _ => (value_range (by omega : 1≤B) s e b i).1)) (mem_univ b)
  apply incr.trans_le
  calc
    _ ≤ ∏ i,value B s e b i := by simpa using lower
    _ ≤ _ := by simpa [iv,layerValue,value] using term

/-- Two rare intermediate layers between two likely anchors force a point below the diagonal. -/
theorem scale_below {n B s c : ℕ} (hB : 2≤B) (size : 2^n<B) (hs : s+1≤c+c)
    (e : Fin n→ℕ) (a i j b : Fin n) (ij : i≠j) (ai : a≤ i) (ib : i≤b) (aj : a≤j) (jb : j≤b)
    (ha : s+(s+1)≤e a) (hb : s+(s+1)≤e b) (hi : e i+c≤s) (hj : e j+c≤s) :
    layerValue (fun i => B^(e i)) (scaleProb B s) < scaleProb B s := by
  have bound (x : Fin n→Bool) : (if IntervalSupport x then (1:ℝ) else 0) * ∏ q,value B s e x q ≤ scaleProb B (s+1) := by
    have sub (v : Finset (Fin n)) : (∏ q,value B s e x q)≤∏ q∈v,value B s e x q :=
      prod_le_prod_of_subset_of_le_one₀ (subset_univ _) (fun u _ => (value_range (by omega : 1≤B) s e x u).1)
        (fun u _ _ => (value_range (by omega : 1≤B) s e x u).2)
    by_cases support : IntervalSupport x
    · simp only [support,ite_true,one_mul]
      by_cases xa : x a=true
      · by_cases xb : x b=true
        · have xi := support.2 a b i xa xb ai ib
          have xj := support.2 a b j xa xb aj jb
          have mul := mul_le_mul (active_small (by omega : 1≤B) hi) (active_small (by omega : 1≤B) hj)
            (by simpa [value,xj] using (value_range (by omega : 1≤B) s e x j).1) (scale_pos (by omega : 0<B) c).le
          have two := sub {i,j}
          simp only [prod_insert (show i∉({j} : Finset _) by simpa using ij),prod_singleton] at two
          exact two.trans ((by simpa [value,xi,xj] using mul : value B s e x i*value B s e x j≤scaleProb B c*scaleProb B c).trans
            ((scale_add B c c).symm.trans_le (scale_anti (by omega : 1≤B) hs)))
        · have lo := sub {b}
          rw [prod_singleton] at lo
          exact lo.trans (by simpa [value,xb] using empty_large (by omega : 1≤B) hb)
      · have lo := sub {a}
        rw [prod_singleton] at lo
        exact lo.trans (by simpa [value,xa] using empty_large (by omega : 1≤B) ha)
    · simp [support,(scale_pos (by omega : 0<B) (s+1)).le]
  have total := sum_le_sum (s:=univ) (fun x _ => bound x)
  have cap : (2:ℝ)^n*scaleProb B (s+1)<scaleProb B s := by
    rw [scale_add,show scaleProb B 1=1/(B:ℝ) by simp [scaleProb]]
    have less : ((2:ℝ)^n)/(B:ℝ)<1 := (div_lt_one (by exact_mod_cast (show 0<B by omega))).mpr (by exact_mod_cast size)
    calc
      _ = scaleProb B s * ((2:ℝ)^n/(B:ℝ)) := by ring
      _ < _ := (mul_lt_mul_of_pos_left less (scale_pos (by omega : 0<B) s)).trans_eq (mul_one _)
  apply lt_of_le_of_lt _ cap
  simpa [layerValue,value] using total

end BrownMolFixed
