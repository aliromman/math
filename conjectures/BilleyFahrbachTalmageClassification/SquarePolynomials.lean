module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Polynomial bounds on the unit square from rectangular coefficient sums -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification.Square

abbrev Row := List ℚ
abbrev Rows := List Row

/-- Add coefficient lists, with zero coefficients after the end of each list. -/
def addWith {α : Type*} (f : α → α → α) : List α → List α → List α
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => f x y :: addWith f xs ys

def add := addWith ((· + ·) : ℚ → ℚ → ℚ)
def addRows := addWith add
def scale (a : ℚ) (p : Row) := p.map (a * ·)

noncomputable def horner {α : Type*} (v : α → ℝ) (x : ℝ) : List α → ℝ
  | [] => 0
  | c :: cs => v c + x * horner v x cs

noncomputable def eval (p : Row) (z : ℝ) : ℝ := horner (fun a : ℚ => (a : ℝ)) z p
noncomputable def evalRows (p : Rows) (x z : ℝ) : ℝ := horner (fun q => eval q z) x p

private theorem horner_add {α : Type*} (f : α → α → α) (v : α → ℝ)
    (hv : ∀ a b, v (f a b) = v a + v b) (x : ℝ) (p q : List α) :
    horner v x (addWith f p q) = horner v x p + horner v x q := by
  induction p generalizing q with
  | nil => simp [addWith, horner]
  | cons a p ih =>
    cases q with
    | nil => simp [addWith, horner]
    | cons b q => simp only [addWith, horner, hv, ih]; ring

@[simp] theorem eval_add (p q : Row) (z : ℝ) :
    eval (add p q) z = eval p z + eval q z :=
  horner_add _ _ (fun _ _ => Rat.cast_add ..) _ _ _

@[simp] theorem evalRows_add (p q : Rows) (x z : ℝ) :
    evalRows (addRows p q) x z = evalRows p x z + evalRows q x z :=
  horner_add _ _ (fun _ _ => eval_add _ _ _) _ _ _

@[simp] theorem eval_nil (z : ℝ) : eval [] z = 0 := rfl
@[simp] theorem eval_cons (c : ℚ) (p : Row) (z : ℝ) :
    eval (c :: p) z = (c : ℝ) + z * eval p z := rfl
@[simp] theorem evalRows_nil (x z : ℝ) : evalRows [] x z = 0 := rfl
@[simp] theorem evalRows_cons (p : Row) (ps : Rows) (x z : ℝ) :
    evalRows (p :: ps) x z = eval p z + x * evalRows ps x z := rfl

@[simp] theorem eval_scale (a : ℚ) (p : Row) (z : ℝ) :
    eval (scale a p) z = (a : ℝ) * eval p z := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
    change ((a*b : ℚ):ℝ) + z*eval (scale a p) z = _
    rw [Rat.cast_mul, ih, eval_cons]
    ring

/-- Multiply a univariate polynomial by a linear factor. -/
def linear (a b : ℚ) (p : Row) : Row := add (scale a p) (0 :: scale b p)

@[simp] theorem eval_linear (a b : ℚ) (p : Row) (z : ℝ) :
    eval (linear a b p) z = (a+b*z) * eval p z := by
  simp [linear]
  ring

/-- The coefficient matrix of a product in separate variables. -/
def tensor (p q : Row) : Rows := p.map (scale · q)

@[simp] theorem eval_tensor (p q : Row) (x z : ℝ) :
    evalRows (tensor p q) x z = eval p x * eval q z := by
  induction p with
  | nil => simp [tensor]
  | cons a p ih =>
    change eval (scale a q) z + x*evalRows (tensor p q) x z = _
    rw [eval_scale, ih, eval_cons]
    ring

/-- Coefficients of the binomial polynomial at an integer translate of the argument. -/
def chooseRow (j : ℕ) : ℕ → Row
  | 0 => [1]
  | k+1 => scale ((k+1 : ℚ)⁻¹) (linear ((j:ℚ)-k) 1 (chooseRow j k))

theorem eval_chooseRow (j k : ℕ) (x : ℝ) :
    eval (chooseRow j k) x = Ring.choose ((j:ℝ)+x) k := by
  induction k with
  | zero => simp [chooseRow]
  | succ k ih =>
    rw [chooseRow, eval_scale, eval_linear, ih]
    push_cast
    have h : ((k:ℝ)+1)*Ring.choose ((j:ℝ)+x) (k+1) =
        Ring.choose ((j:ℝ)+x) k * (((j:ℝ)+x)-k) := by
      simpa [Nat.choose_succ_self_right, nsmul_eq_mul] using
        (Ring.choose_smul_choose ((j:ℝ)+x) (Nat.le_succ k))
    field_simp
    linear_combination -h

/-- Test all successive partial sums of a row. -/
def positivePrefixes (a : ℚ) : Row → Bool
  | [] => decide (0 < a)
  | b :: bs => decide (0 < a+b) && positivePrefixes (a+b) bs

/-- Test all rectangular partial sums, including the final row and column. -/
def positiveRectangles (a : Row) : Rows → Bool
  | [] => positivePrefixes 0 a
  | p :: ps => let next := add a p
               positivePrefixes 0 next && positiveRectangles next ps

private theorem blend_pos {x a b : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    0 < (1-x)*a + x*b := by
  rcases eq_or_lt_of_le hx' with rfl|h
  · simpa using hb
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr h) ha) (mul_nonneg hx hb.le)

private theorem prefixes_sound (a : ℚ) (p : Row) (hp : positivePrefixes a p = true)
    (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) : 0 < (a:ℝ) + eval p z := by
  induction p generalizing a with
  | nil =>
    simp only [positivePrefixes, decide_eq_true_eq] at hp
    simpa using (show (0:ℝ) < a by exact_mod_cast hp)
  | cons b p ih =>
    simp only [positivePrefixes, Bool.and_eq_true, decide_eq_true_eq] at hp
    have h := blend_pos hz hz' (show (0:ℝ) < (a+b:ℚ) by exact_mod_cast hp.1) (ih _ hp.2)
    push_cast at h
    rw [eval_cons]
    linarith

theorem rectangles_sound (p : Rows) (hp : positiveRectangles [] p = true)
    (x z : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    0 < evalRows p x z := by
  suffices hall : ∀ (a : Row) (ps : Rows), positiveRectangles a ps = true →
      0 < eval a z + evalRows ps x z by simpa using hall [] p hp
  intro a ps
  induction ps generalizing a with
  | nil =>
    intro h
    simpa using prefixes_sound 0 a h z hz hz'
  | cons p ps ih =>
    intro h
    simp only [positiveRectangles, Bool.and_eq_true] at h
    have h₁ : 0 < eval (add a p) z := by simpa using prefixes_sound 0 _ h.1 z hz hz'
    have hh := blend_pos hx hx' h₁ (ih _ h.2)
    rw [eval_add] at hh
    rw [evalRows_cons]
    linarith

end BilleyFahrbachTalmageClassification.Square
